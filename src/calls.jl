# ---------------------------------------------------------------------------
# Calls upward (the note's rule 1, "Calls upward"): code that stays outside
# the trait world runs for it only as a call upward. A trait module declares a
# call into an ordinary package with `@call Pkg.f(args…)::T`; the call's body
# is ordinary code, resolved in the ordinary module around the trait module
# (which imports the package), and the call is dynamic, with no inference
# edge, its result checked. Values that come back without operations are
# handles. Any trait package may declare calls; declaring them adds no methods
# and decides nothing about what trait-world code compiles against, so it
# needs no kind of package of its own.
#
#     module MakiePlots                      # the ordinary module: imports Makie
#     using TraitWorld, Makie
#     @trait_module module Plots             # the trait module
#         @handle Figure                     # a value from Makie, opaque inside
#         figure() = @call Makie.Figure()::Figure
#         scatter!(f::Figure, t::PointSeries) = @call Makie.scatter!(f, xs(t), ys(t))::Nothing
#     end
#     using .Plots; export figure, scatter!
#     end
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

A declared call into a package that stays outside: the outside function,
called through `invokelatest` (no inference edge, so the worker's cache cannot
depend on anything behind it), handles unwrapped before and the result
asserted to `S`, or wrapped when `S` is a handle type.
"""
struct DeclaredCall{S}
    f::Any
    name::String
    holder::Module
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
The ordinary module that holds a trait module's declared calls: the nearest
enclosing module that is not a trait module, which imports the outside
package. `nothing` when the trait module sits at the top (in `Main`), where
nothing imports the outside package for it.
"""
function _call_holder(m::Module)
    x = m
    while isdefined(x, :__trait_module__) || _in_trait_module(x)
        p = parentmodule(x)
        p === x && return nothing
        x = p
    end
    (x === Main || x === Core || x === Base) && return nothing
    return x
end
_in_trait_module(x::Module) = (p = parentmodule(x); p !== x && isdefined(p, :__trait_module__))

"The declared calls held by an ordinary module, what `verify_main` lists as targets; kept in the module itself, so they are saved with its image."
declared_calls(m::Module) = isdefined(m, :__tw_declared__) ?
    Base.invokelatest(getglobal, m, :__tw_declared__)::Vector{DeclaredCall} : DeclaredCall[]   # defined during `@call`'s own expansion: read in the latest world
"Whether `m` holds declared calls: the ordinary module around a trait module that calls out."
is_declarer(m::Module) = isdefined(m, :__tw_declared__)
"Modules holding declared calls, among the loaded packages (and those defined in this session)."
function declarers()
    out = Module[]
    for (_, m) in Base.loaded_modules
        is_declarer(m) && push!(out, m)
    end
    for m in _SESSION_DECLARERS
        m in out || push!(out, m)
    end
    return out
end
const _SESSION_DECLARERS = Module[]

"""
After a package load: the generation moves (a load can bring projections and
implementations without running `@implement` here), a trait wrapper loaded
from its image is registered, a trait package seals itself, and the sealing
scan runs once per top-level `using`.
"""
function _on_package_load(id::Base.PkgId)
    _bump!()
    m = get(Base.loaded_modules, id, nothing)
    m isa Module || return nothing
    is_wrapper_root(m) && _register_wrapper!(m, getglobal(m, :__tw_wrapper__)...)
    Base.inferencebarrier(_filter_scan!)(m)
    (isdefined(m, :__trait_module__) || _has_trait_module(m)) && seal!(m)   # a trait package seals itself (no rescan needed)
    Base.toplevel_load[] && _check_loads!()                                  # once per `using`, nested loads included
    Base.toplevel_load[] && Base.inferencebarrier(_vc_load!)()               # the view caches of what is loaded now
    return nothing
end

"""
    @call Makie.scatter!(f, xs(t), ys(t); color = c)::Nothing

A declared call from a trait module into a package that stays outside. The
function is resolved in the ordinary module around the trait module, which
imports the package; the result type must be a trait-world type or a handle;
the call is dynamic, with no inference edge, and its result is checked.
"""
macro call(ex)
    ex isa Expr && ex.head === :(::) && length(ex.args) == 2 ||
        error("@call: declare the result type, as in `@call Pkg.f(args…)::T`")
    callex, Sex = ex.args
    callex isa Expr && callex.head === :call || error("@call: expected a call, got `$callex`")
    holder = _call_holder(__module__)
    holder === nothing && error("@call: a declared call needs an ordinary module around the trait module, one that imports the package it calls")
    fpath = callex.args[1]
    f = try
        Core.eval(holder, fpath)
    catch e
        error("@call: cannot resolve `$fpath` in $holder: $(sprint(showerror, e))")
    end
    if !is_declarer(holder)
        Core.eval(holder, :(const __tw_declared__ = $TraitWorld.DeclaredCall[]))
        holder in _SESSION_DECLARERS || push!(_SESSION_DECLARERS, holder)
    end
    S = Core.eval(__module__, Sex)
    S isa Type || error("@call: the result type `$Sex` is not a type")
    (S <: Handle || S === Nothing || deep_concrete(S)) ||
        error("@call: the result type $S is neither a handle nor deeply concrete: a declared call brings in trait-world values only")
    dc = DeclaredCall{S}(f, string(fpath), holder)
    push!(declared_calls(holder), dc)
    return esc(Expr(:call, dc, callex.args[2:end]...))
end
