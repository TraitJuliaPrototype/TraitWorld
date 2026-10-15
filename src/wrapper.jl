# ---------------------------------------------------------------------------
# Trait wrappers (the note's "Trait wrappers: code written without traits"):
# a trait wrapper brings a package written without traits into the trait world
# and stands in for its owner there (rule 3). It names the implementation
# packages of a split core among its own dependencies, so they are loaded
# whenever the core's types can enter the trait world, and as delegates their
# methods are the core's; it reads its tolerations from its Project.toml; and
# its load seals the package, the implementations and their dependencies
# (Sealing). At most one wrapper per package: a second is refused at its load.
#
#     module StaticArraysCoreWrapper
#     using TraitWorld
#     import StaticArraysCore, StaticArrays
#     @trait_wrapper StaticArraysCore StaticArrays
#     end
#
# A library written with traits needs no wrapper. The Base wrapper is implicit:
# Julia is one owner, sealed from the start.
# ---------------------------------------------------------------------------

"Packages whose pirates are tolerated: the union of the loaded wrappers' lists and the project's."
const TOLERATED = Set{String}()
"Wrapped packages: the package's root module => its wrapper's module."
const WRAPPERS = IdDict{Module,Module}()
"Wrapped packages: the package's root module => the implementation packages its wrapper delegates to."
const DELEGATES = IdDict{Module,Vector{Module}}()

"""
    @trait_wrapper Pkg Impl…

At the top of a trait wrapper's module, after importing `Pkg` and its
implementation packages: registers the wrapper for `Pkg`, names `Impl…` as
the implementations it delegates to, reads the tolerations from the wrapper's
`Project.toml` (`[traits] tolerate = ["…"]`) and seals what it brings in.
"""
macro trait_wrapper(pkg, impls...)
    return esc(quote
        const __tw_wrapper__ = ($pkg, ($(impls...),))
        $TraitWorld._register_wrapper!(@__MODULE__, __tw_wrapper__...)
    end)
end

"Whether `m` is a trait wrapper's module."
is_wrapper_root(m::Module) = isdefined(m, :__tw_wrapper__)

"The wrapper of the package `m` belongs to, or `nothing`."
wrapper_of(m::Module) = get(WRAPPERS, _wrap_key(m), nothing)
_wrap_key(m::Module) = (o = owner(m); o isa Module ? o : Base.moduleroot(m))

"Whether `m` belongs to a wrapped package or to an implementation a wrapper names."
function is_wrapped(m::Module)
    k = _wrap_key(m)
    haskey(WRAPPERS, k) && return true
    for v in values(DELEGATES)
        for d in v
            d === k && return true
        end
    end
    return false
end

"The implementations a wrapper names for the package owned by `o`: its delegates; empty when unwrapped."
function delegates_of(@nospecialize(o))
    o isa Module || return Module[]
    return get(DELEGATES, o, Module[])::Vector{Module}
end

function _register_wrapper!(w::Module, pkg::Module, impls::Tuple)
    k = _wrap_key(pkg)
    prev = get(WRAPPERS, k, nothing)
    prev === w && return nothing
    if prev !== nothing
        # at most one wrapper per package: the second decides nothing (Base swallows exceptions from package callbacks)
        Base.inferencebarrier(_second_wrapper)(w, k, prev)
        return nothing
    end
    WRAPPERS[k] = w
    DELEGATES[k] = Module[_wrap_key(i) for i in impls if i isa Module]
    empty!(_PIRATICAL)                          # ownership changed: the audit's cache must be rebuilt
    for p in _read_tolerations(w)
        push!(TOLERATED, p)
    end
    _seal_wrapper!(w, k, DELEGATES[k])
    return nothing
end
_register_wrapper!(w::Module, @nospecialize(pkg), @nospecialize(impls)) =
    throw(ArgumentError("@trait_wrapper: expected a package and implementation packages, got $pkg and $impls"))

function _second_wrapper(w::Module, k::Module, prev::Module)
    @error "TraitBoundError: $w is a second trait wrapper for $k, which $prev wraps already: refused, it decides nothing (a package has at most one wrapper in an environment)"
    return nothing
end

"The `[traits] tolerate` list of a package's Project.toml."
function _read_tolerations(mod::Module)
    dir = pkgdir(mod)
    dir === nothing && return String[]
    return _tolerations_of(joinpath(dir, "Project.toml"))
end
