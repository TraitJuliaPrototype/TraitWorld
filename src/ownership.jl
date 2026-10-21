# ---------------------------------------------------------------------------
# Ownership (rule 3), ported from TraitRegions. Julia itself (Base, Core and
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
file, which lies in the parent's `ext/` directory (session 19: a scan for pirates
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
    # a loaded package that is no extension stays one: remembered, since a scan
    # over all methods asks once per method (without this, 15 s instead of 2 s
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
    memo = _OWNER_MEMO[]
    memo === nothing && return _owner(m)
    o = get(memo, m, nothing)
    o === nothing || return o
    return memo[m] = _owner(m)
end
"Owners by module, memoized while a caller scans many methods at once (a package image's), where they cannot change; `nothing` otherwise."
const _OWNER_MEMO = Ref{Union{Nothing,IdDict{Module,Any}}}(nothing)
function _owner(m::Module)
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

"""
    @joint_owners P1 P2 …

At the top level of a package's module: the packages named (by name) own its functions and types
with it (traits §10.1, joint owners). Only the owner declares its joint owners.
"""
macro joint_owners(names...)
    all(n -> n isa Symbol, names) && !isempty(names) ||
        error("@joint_owners: name the packages, as in `@joint_owners DiffEqBase OrdinaryDiffEqCore`")
    owner(__module__) === __module__ ||
        error("@joint_owners: only a package's own module declares its joint owners, not $(__module__)")
    return esc(:(const __tw_joint_owners__ = $(Tuple(names))))
end
"The joint owners the owner `o` declares, by name."
_joint_names(@nospecialize(o)) = o isa Module && isdefined(o, :__tw_joint_owners__) ? getfield(o, :__tw_joint_owners__)::Tuple : ()
"Whether `definer` owns what the owner `o` owns: it is `o`, or a joint owner `o` declares."
owns(@nospecialize(definer), @nospecialize(o)) = definer === o || (definer isa Module && nameof(definer) in _joint_names(o))

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
packages extend, and the ownership check must not be invalidated by their loads.
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

Rule 3: the package that defined `m` owns, in each alternative of `m`'s own signature
(each `Union` member taken separately), the function or one of the types. Unlike Aqua's
rule, `f(::Union{Mine, Int})` is not owned: its alternative `f(::Int)` names nothing of
the definer's. A method on an abstract type is owned by the type's owner also where it
applies to another package's subtype (note "Ownership": stakeholders include supertypes' owners).
"""
function owned_method(m::Method)
    definer = owner(m.module)
    for s in _sig_alternatives(m.sig)
        any(o -> owns(definer, o), sig_owners(s)) || return false
    end
    return true
end

# --- package roots of modules and types ----------------------------------------------------
# Which package a value of a given type belongs to. Written for the patched runtime's
# invalidation policy (now removed); kept for a strict mode, which needs the same lookups.

"A package's root module: a module under `Main` counts as its own package."
function _pkg_root(m::Module)
    while true
        p = parentmodule(m)
        (p === m || p === Main) && return m
        m = p
    end
end

"""
The packages (outside Base, Core and the trait world) that every value matching `t` mentions in its
type: `t` itself (or a `Vararg`'s element, a type variable's bound) is a package's type, or a type
parameter requires one (`Ref{T} where T<:InlineString`, `Diagonal{T, Ones{T}}`); for a `Union`, the
packages both sides require. `Type{T}` counts as `T`.
"""
function _required_roots(@nospecialize(t), depth::Int = 0)
    out = Module[]
    depth > 4 && return out
    t isa UnionAll && return _required_roots(Base.unwrap_unionall(t), depth)
    t isa TypeVar && return _required_roots(t.ub, depth + 1)
    t isa Core.TypeofVararg && return isdefined(t, :T) ? _required_roots(t.T, depth + 1) : out
    t isa Union && return intersect(_required_roots(t.a, depth + 1), _required_roots(t.b, depth + 1))
    t isa DataType || return out
    r = _type_root(t.name.module)
    r === nothing || push!(out, r)
    for p in t.parameters
        union!(out, _required_roots(p, depth + 1))
    end
    return out
end

const _TYPE_ROOTS = IdDict{Module,Any}()           # module => its package root, or `nothing`
"The package whose types a module's are: `nothing` for Base's and Core's types (everyone's) and the trait world's; a standard library's types are its own (`LibGit2`, `SparseArrays`)."
function _type_root(mod::Module)
    r = get(_TYPE_ROOTS, mod, missing)
    r === missing || return r
    r = _julia_core(mod) || _trait_world_package(mod) ? nothing : _pkg_root(mod)
    _TYPE_ROOTS[mod] = r
    return r
end

"Whether a module belongs to Base, Core or the compiler."
_julia_core(mod::Module) = (p = _pkg_root(mod); p === Base || p === Core || p === Base.Compiler)
"In the trait world and not one of Julia's standard libraries (whose types and methods are their own here)."
_trait_world_package(mod::Module) = owner(_pkg_root(mod)) !== :Julia && is_trait_world(mod)
