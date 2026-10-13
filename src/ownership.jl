# ---------------------------------------------------------------------------
# Ownership (rule 5), ported from TraitRegions. Julia itself (Base, Core and
# every standard library) is ONE owner. Package extensions inherit their
# parent's ownership: an extension is how an owner delegates. A method is
# owned by its package if, in every signature it applies to, the package owns
# the function or one of the types (`owned_method`); Aqua's weaker "mentions"
# rule (`is_piratical`) is kept for the piracy audit of ordinary packages.
#
# PoC limit: methods are attributed to `parentmodule(m)`; stock Julia records
# no loader context, so a definition laundered through `Core.eval(Owner, …)`
# counts as the owner's.
# ---------------------------------------------------------------------------

const _STDLIBS = Ref{Union{Nothing,Set{Symbol}}}(nothing)

function _stdlib_names()
    s = _STDLIBS[]
    s === nothing || return s
    s = Set{Symbol}(Symbol.(readdir(Sys.STDLIB)))
    _STDLIBS[] = s
    return s
end

"Parent package of a loaded package extension, or `nothing`."
function _extension_parent(r::Module)
    v = get(Base.EXT_PRIMED, Base.PkgId(r), nothing)   # extension => [parent, triggers...]
    v === nothing && return nothing
    return get(Base.loaded_modules, first(v), nothing)
end

"""
    owner(m::Module)

`:Julia` for Base, Core and the standard libraries; otherwise the package's
root module, with package extensions mapped to their parent. A module
defined in a script or at the REPL (directly under `Main`) is its own owner;
`Main` itself is the session's.
"""
function owner(m::Module)
    r = Base.moduleroot(m)
    if r === Main && m !== Main
        # a module defined in a script or at the REPL counts as its own package
        while parentmodule(m) !== Main
            m = parentmodule(m)
        end
        return m
    end
    (r === Base || r === Core) && return :Julia
    nameof(r) in _stdlib_names() && return :Julia
    p = _extension_parent(r)
    return p === nothing ? r : owner(p)
end

# Implementer declarations: interfaces a package may extend as if it owned
# them. Defaults cover the interface/implementation splits measured on the
# CairoMakie stack; packages override or add via Project.toml.
const DEFAULT_IMPLEMENTS = Dict{Symbol,Vector{Symbol}}(
    :StaticArrays     => [:StaticArraysCore],
    :ChainRules       => [:ChainRulesCore],
    :Colors           => [:ColorTypes],
    :ColorVectorSpace => [:ColorTypes],
    :ImageCore        => [:ColorTypes],
    :StatsBase        => [:StatsAPI],
    :Distributions    => [:StatsAPI, :StatsBase],
)

const _IMPLEMENTS = IdDict{Module,Vector{Symbol}}()

"Interfaces package `m` declares it implements (Project.toml `[traitbound] implements`)."
function implements(m::Module)
    get!(_IMPLEMENTS, m) do
        out = copy(get(DEFAULT_IMPLEMENTS, nameof(m), Symbol[]))
        dir = pkgdir(m)
        if dir !== nothing
            proj = joinpath(dir, "Project.toml")
            if isfile(proj)
                toml = Base.parsed_toml(proj)
                # plain haskey/getindex: these are compiled in the sysimage,
                # `get` with a typed default costs ~10 ms of first-use compile
                if haskey(toml, "traitbound")
                    tb = toml["traitbound"]
                    if tb isa Dict && haskey(tb, "implements")
                        for name in tb["implements"]
                            push!(out, Symbol(name::String))
                        end
                    end
                end
            end
        end
        out
    end
end

function _owners!(acc::Base.IdSet{Any}, @nospecialize(T))
    if T isa Union
        _owners!(acc, T.a); _owners!(acc, T.b)
    elseif T isa UnionAll
        _owners!(acc, T.var.lb); _owners!(acc, T.var.ub); _owners!(acc, T.body)
    elseif T isa Core.TypeofVararg
        isdefined(T, :T) && _owners!(acc, T.T)
    elseif T isa DataType
        push!(acc, owner(T.name.module))
        for p in T.parameters
            _owners!(acc, p)
        end
    elseif T isa TypeVar
        _owners!(acc, T.lb); _owners!(acc, T.ub)
    end
    return acc
end

"""
Owners of every function and type mentioned in a method signature. An
identity set on purpose: hashing values of type `Any` is a call other
packages extend, and the audit must not be invalidated by their loads.
"""
sig_owners(@nospecialize(sig)) = _owners!(Base.IdSet{Any}(), sig)

"""
    is_piratical(m::Method)

A method is piratical if its defining package owns neither the function nor
any type mentioned in its signature, and declares no implementer relation to
one of those owners.
"""
function is_piratical(m::Method)
    definer = owner(m.module)
    owners = sig_owners(m.sig)
    definer in owners && return false
    definer isa Module || return true
    # rare and full of TOML handling: kept behind a dynamic call so that its
    # abstract edges cannot invalidate the audit's hot path
    impl = Base.inferencebarrier(implements)(definer)::Vector{Symbol}
    for o in owners
        o isa Module && nameof(o) in impl && return false
    end
    return true
end

# one signature per Union member at the top level of each argument (and of a
# type variable's upper bound), at most `limit` combinations
function _sig_alternatives(@nospecialize(sig), limit::Int = 256)
    body = Base.unwrap_unionall(sig)
    body isa DataType || return Any[sig]
    alts = Any[]
    for p in body.parameters
        if p isa Union
            push!(alts, Base.uniontypes(p))
        elseif p isa TypeVar && p.ub isa Union
            push!(alts, Base.uniontypes(p.ub))
        else
            push!(alts, Any[p])
        end
    end
    prod(length, alts; init = 1) <= limit || return Any[sig]
    return Any[Tuple{c...} for c in Iterators.product(alts...)]
end

"""
    owned_method(m::Method)

Rule 5: the package that defined `m` owns, in every signature `m` applies to,
the function or one of the types. Unlike Aqua's rule, `f(::Union{Mine, Int})`
is not owned: it applies to `Int` alone too.
"""
function owned_method(m::Method)
    definer = owner(m.module)
    for s in _sig_alternatives(m.sig)
        definer in sig_owners(s) || return false
    end
    return true
end
