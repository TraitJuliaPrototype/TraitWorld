# ---------------------------------------------------------------------------
# Interface packages: a trait module reaches code that is not a trait module
# only through one (rule 1). An interface package has an ordinary half, the
# package's root module, which imports the wrapped package, and a trait half,
# a trait module nested in it, whose functions reach the outside only through
# declared calls, with handles for values that come back.
#
#     module MakieInterface                  # the ordinary half
#     using TraitWorld, Makie
#     @interface_package Makie               # records what is wrapped; tolerations; sealing (M6)
#     @trait_module module Plots             # the trait half
#         @handle Figure                     # a value from Makie, opaque inside
#         figure() = @call Makie.Figure()::Figure
#         scatter!(f::Figure, t::PointSeries) = @call Makie.scatter!(f, xs(t), ys(t))::Nothing
#     end
#     using .Plots; export figure, scatter!
#     end
#
# A declared call is a dynamic call upward with no inference edge
# (`invokelatest`), its result asserted to the declared type or wrapped as a
# handle; handles are unwrapped before the call. Trait objects never go up.
# ---------------------------------------------------------------------------

"Supertype of handles: a value from outside the trait world that must come back to it. No operations, never inspected."
abstract type Handle end

"""
    @handle Figure

Define a handle type: `struct Figure <: TraitWorld.Handle; ref::Any; end`.
Inside the trait world a handle may be stored, returned and passed to declared
calls and to the module's own functions; `h.ref` and `typeof(h)` are refused.
"""
macro handle(name)
    name isa Symbol || error("@handle: expected a name, got `$name`")
    return esc(quote
        Core.@__doc__ struct $name <: $TraitWorld.Handle
            ref::Any
        end
        $name
    end)
end

"""
    DeclaredCall{S}

A declared call into the package an interface wraps: the outside function,
called through `invokelatest` (no inference edge, so the worker's cache cannot
depend on anything behind it), handles unwrapped before and the result
asserted to `S`, or wrapped when `S` is a handle type.
"""
struct DeclaredCall{S}
    f::Any
    name::String
    iface::Module
end

@inline _unwrap_handle(x) = x
@inline _unwrap_handle(h::Handle) = getfield(h, :ref)
@noinline _unwrap_handle(::TObj) = throw(TraitUseError(["a trait object was passed to a declared call: trait objects never go up"]))
@inline _wrap_result(::Type{S}, r) where {S} = r::S
@inline _wrap_result(::Type{S}, r) where {S<:Handle} = S(r)

# not inlined: verify_main recognizes the call as a declared target and does not walk it
@noinline function (dc::DeclaredCall{S})(args...; kws...) where {S}
    r = if isempty(kws)
        Base.invokelatest(dc.f, map(_unwrap_handle, args)...)
    else
        nt = Base.values(kws)
        Base.invokelatest(dc.f, map(_unwrap_handle, args)...; map(_unwrap_handle, nt)...)
    end
    return _wrap_result(S, r)
end
Base.show(io::IO, dc::DeclaredCall{S}) where {S} = print(io, "@call ", dc.name, "::", S)

"""
Interface packages loaded: the ordinary half's module => the module it wraps.
Filled when `@interface_package` runs, and again when an interface package is
loaded from its image (the package callback), because what its macros recorded
while it was precompiled is not in the image.
"""
const INTERFACES = IdDict{Module,Module}()
"Packages whose pirates are tolerated: the union of the loaded interface packages' lists and the project's."
const TOLERATED = Set{String}()
"The declared calls of an interface package, what `verify_main` lists as targets; kept in the package's own module, so they are saved with its image."
declared_calls(iface::Module) = getglobal(iface, :__tw_declared__)::Vector{DeclaredCall}

"The root of an interface package, or of a trait module nested in one; `nothing` otherwise."
function _interface_root(m::Module)
    x = m
    while true
        isdefined(x, :__tw_interface__) && return x
        p = parentmodule(x)
        p === x && return nothing
        x = p
    end
end
"Whether `m` is the ordinary half of an interface package (its root module; a package root is its own parent)."
is_interface_root(m::Module) = _interface_root(m) === m

"The `[traits] tolerate` list of a package's Project.toml."
function _read_tolerations(mod::Module)
    dir = pkgdir(mod)
    dir === nothing && return String[]
    return _tolerations_of(joinpath(dir, "Project.toml"))
end

"""
    @interface_package Makie

At the top of an interface package's module, after `using Makie`: records the
package it wraps, reads the tolerations from the package's `Project.toml`
(`[traits] tolerate = ["…"]`), and seals the wrapped package's dependency
closure (M6).
"""
macro interface_package(wrapped)
    return esc(quote
        const __tw_interface__ = $wrapped
        const __tw_declared__ = $TraitWorld.DeclaredCall[]
        $TraitWorld._register_interface!(@__MODULE__, __tw_interface__)
    end)
end

function _register_interface!(mod::Module, wrapped::Module)
    get(INTERFACES, mod, nothing) === wrapped && return nothing
    INTERFACES[mod] = wrapped
    for p in _read_tolerations(mod)
        push!(TOLERATED, p)
    end
    _seal_interface!(mod, wrapped)
    return nothing
end
_register_interface!(mod::Module, @nospecialize(wrapped)) =
    throw(ArgumentError("@interface_package: expected a module, got $wrapped"))
"""
After a package load: the generation moves (a load can bring projections and
implementations without running `@implement` here), and an interface package
loaded from its image is registered.
"""
function _on_package_load(id::Base.PkgId)
    _bump!()
    m = get(Base.loaded_modules, id, nothing)
    m isa Module || return nothing
    is_interface_root(m) && _register_interface!(m, getglobal(m, :__tw_interface__))
    (isdefined(m, :__trait_module__) || _has_trait_module(m)) && seal!(m)   # a trait package seals itself (no rescan needed)
    Base.toplevel_load[] && _check_loads!()                                  # once per `using`, nested loads included
    return nothing
end

"""
    @call Makie.scatter!(f, xs(t), ys(t); color = c)::Nothing

A declared call from an interface package's trait module into the package it
wraps. The function is resolved in the ordinary half (the interface package's
root module), the result type must be a trait-world type or a handle; the
call is dynamic, with no inference edge, and its result is checked.
"""
macro call(ex)
    ex isa Expr && ex.head === :(::) && length(ex.args) == 2 ||
        error("@call: declare the result type, as in `@call Pkg.f(args…)::T`")
    callex, Sex = ex.args
    callex isa Expr && callex.head === :call || error("@call: expected a call, got `$callex`")
    iface = _interface_root(__module__)
    iface === nothing && error("@call: only inside the trait module of an interface package (`@interface_package`)")
    fpath = callex.args[1]
    f = try
        Core.eval(iface, fpath)
    catch e
        error("@call: cannot resolve `$fpath` in $iface: $(sprint(showerror, e))")
    end
    S = Core.eval(__module__, Sex)
    S isa Type || error("@call: the result type `$Sex` is not a type")
    (S <: Handle || S === Nothing || deep_concrete(S)) ||
        error("@call: the result type $S is neither a handle nor deeply concrete: a declared call brings in trait-world values only")
    dc = DeclaredCall{S}(f, string(fpath), iface)
    push!(declared_calls(iface), dc)
    return esc(Expr(:call, dc, callex.args[2:end]...))
end
