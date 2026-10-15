# ---------------------------------------------------------------------------
# Ownership (rule 5), ported from TraitRegions. Julia itself (Base, Core and
# every standard library) is ONE owner. Package extensions inherit their
# parent's ownership: an extension is how an owner delegates. A method is
# owned by its package if, in every signature it applies to, the package owns
# the function or one of the types (`owned_method`); Aqua's weaker "mentions"
# rule is not used: a `Union` with a foreign type would pass it.
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

# Extensions noted from their source files: while an extension is precompiled,
# Base has not recorded its parent yet (EXT_PRIMED), but its file lies in the
# parent's `ext/` directory, whose Project.toml names it and its triggers.
const _EXT_PARENTS = IdDict{Module,Module}()
const _EXT_TRIGGERS = IdDict{Module,Vector{String}}()

"Record `mod` as a package extension if `file` is in a package's `ext/` directory that declares it."
function _note_extension!(mod::Module, file)
    r = Base.moduleroot(mod)
    haskey(_EXT_PARENTS, r) && return nothing
    file isa Symbol || file isa AbstractString || return nothing
    f = string(file)
    basename(dirname(f)) == "ext" || return nothing
    proj = joinpath(dirname(dirname(f)), "Project.toml")
    isfile(proj) || return nothing
    toml = Base.parsed_toml(proj)
    exts = get(toml, "extensions", nothing)
    exts isa Dict || return nothing
    trig = get(exts, String(nameof(r)), nothing)
    trig === nothing && return nothing
    parent = _loaded_root(String(toml["name"]))
    parent === nothing && return nothing
    _EXT_PARENTS[r] = parent
    _EXT_TRIGGERS[r] = trig isa String ? [trig] : String[t for t in trig]
    return nothing
end
function _loaded_root(name::String)
    for (k, v) in Base.loaded_modules
        k.name == name && return v
    end
    return nothing
end

"""
Parent package of a package extension, or `nothing`. `Base.EXT_PRIMED` knows
the extensions primed in this session; one loaded from an image (Adapt's,
Compat's, when their triggers were already loaded) is recognized by its source
file, which lies in the parent's `ext/` directory (session 19: the sealing scan
reported such extensions as pirates of their own parents).
"""
function _extension_parent(r::Module)
    p = get(_EXT_PARENTS, r, nothing)
    p === nothing || return p
    v = get(Base.EXT_PRIMED, Base.PkgId(r), nothing)   # extension => [parent, triggers...]
    v === nothing || return get(Base.loaded_modules, first(v), nothing)
    o = get(Base.pkgorigins, Base.PkgId(r), nothing)
    if o !== nothing && o.path !== nothing
        _note_extension!(r, o.path)
        p = get(_EXT_PARENTS, r, nothing)
        p === nothing || return p
    end
    r in _NOT_EXTENSIONS && return nothing
    # an extension of a standard library (Pkg's REPLExt): the parent that names it
    for (_, m) in Base.loaded_modules
        if Base.get_extension(m, nameof(r)) === r
            _EXT_PARENTS[r] = m
            return m
        end
    end
    # a loaded package that is no extension stays one: remembered, since the
    # sealing scan asks once per method (without this, 15 s instead of 2 s
    # for a full scan with Makie loaded)
    haskey(Base.loaded_modules, Base.PkgId(r)) && push!(_NOT_EXTENSIONS, r)
    return nothing
end
"Loaded package roots known not to be extensions (reset in `__init__`)."
const _NOT_EXTENSIONS = Base.IdSet{Module}()
"Trigger packages of a package extension (names), or `nothing`."
function _extension_triggers(r::Module)
    t = get(_EXT_TRIGGERS, r, nothing)
    t === nothing || return t
    v = get(Base.EXT_PRIMED, Base.PkgId(r), nothing)
    v === nothing && return nothing
    return String[p.name for p in v[2:end]]
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
    (r === Base || r === Core || r === Base.Compiler) && return :Julia      # the compiler is a module of its own in 1.12
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
        if T.name === Base.typename(TObj) && T.parameters[1] isa TypeVar
            # a trait object `TObj{T} where T >: Union{traits}` belongs to its traits' owners:
            # the lower bound says which traits it carries
            _owners!(acc, T.parameters[1].lb)
            for p in T.parameters[2:end]
                _owners!(acc, p)
            end
        else
            for p in T.parameters
                # a value as a type parameter (Makie's `Plot{scatter}`, a function) belongs to its type's owner
                _owners!(acc, p isa Type || p isa TypeVar || p isa Core.TypeofVararg ? p : typeof(p))
            end
        end
    elseif T isa TypeVar
        # an ordinary lower bound restricts nothing: `x::T where T >: Mine` applies to Any
        _owners!(acc, T.ub)
    end
    return acc
end

"""
Owners of every function and type mentioned in a method signature. An
identity set on purpose: hashing values of type `Any` is a call other
packages extend, and the audit must not be invalidated by their loads.
"""
sig_owners(@nospecialize(sig)) = _owners!(Base.IdSet{Any}(), sig)

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
    n = 1
    for a in alts
        n *= length(a)
    end
    n <= limit || return Any[sig]
    # the product by hand: Iterators.product would compile per arity, at the first call of a session
    combos = Vector{Any}[Any[]]
    for a in alts
        next = Vector{Any}[]
        for c in combos, x in a
            push!(next, Any[c..., x])
        end
        combos = next
    end
    out = Any[]
    for c in combos
        push!(out, Tuple{c...})
    end
    return out
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
