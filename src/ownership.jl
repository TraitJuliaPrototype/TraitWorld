# Ownership and pirates (traits §12.1, §12.2; lowering §11).
#
# A package owns the functions and types it defines, traits included. Julia (Core, Base, the standard
# libraries) is one owner. A package extension counts as its parent. At the prompt, `Main` is one
# owner and each module defined directly under `Main` is an owner of its own. A membership is declared
# by the trait's owner or the type's owner; a pirate is a method of a function the definer does not
# own, for types it does not own.

"A membership or a method by a package that owns none of what it names (traits §11.3)."
struct OwnershipError <: Exception
    msg::String
end
Base.showerror(io::IO, e::OwnershipError) = print(io, "OwnershipError: ", e.msg)

const _STDLIBS = Ref{Union{Nothing,Set{Symbol}}}(nothing)
function _stdlib_names()
    s = _STDLIBS[]
    s === nothing || return s
    s = Set{Symbol}(Symbol.(readdir(Sys.STDLIB)))
    _STDLIBS[] = s
    return s
end

const _EXT_PARENTS = IdDict{Module,Module}()
const _EXT_TRIGGERS = IdDict{Module,Vector{String}}()
const _NOT_EXTENSIONS = Base.IdSet{Module}()

# an extension's parent and triggers: from Base's record of primed extensions, or from its source file,
# which lies in the parent's `ext/` directory, whose Project.toml names it and its triggers
function _extension_parent(r::Module)
    p = get(_EXT_PARENTS, r, nothing)
    p === nothing || return p
    r in _NOT_EXTENSIONS && return nothing
    v = get(Base.EXT_PRIMED, Base.PkgId(r), nothing)       # extension => [parent, triggers...]
    if v !== nothing
        parent = get(Base.loaded_modules, first(v), nothing)
        if parent !== nothing
            _EXT_PARENTS[r] = parent
            _EXT_TRIGGERS[r] = String[q.name for q in v[2:end]]
            return parent
        end
    end
    o = get(Base.pkgorigins, Base.PkgId(r), nothing)
    if o !== nothing && o.path !== nothing && _note_extension!(r, o.path)
        return _EXT_PARENTS[r]
    end
    haskey(Base.loaded_modules, Base.PkgId(r)) && push!(_NOT_EXTENSIONS, r)
    return nothing
end

function _note_extension!(r::Module, f::AbstractString)
    d = dirname(f)
    basename(d) == "ext" || (d = dirname(d); basename(d) == "ext") || return false
    proj = joinpath(dirname(d), "Project.toml")
    isfile(proj) || return false
    toml = Base.parsed_toml(proj)
    exts = get(toml, "extensions", nothing)
    exts isa AbstractDict || return false
    trig = get(exts, String(nameof(r)), nothing)
    trig === nothing && return false
    parent = nothing
    for (k, m) in Base.loaded_modules
        k.name == toml["name"] && (parent = m)
    end
    parent === nothing && return false
    _EXT_PARENTS[r] = parent
    # the triggers as strings, checked one by one: a TOML value is untyped, and a store built from it
    # needed `convert(Vector{String}, ::Any)`, which any package's new `print` method for its strings
    # invalidated, and with it the load hooks that reach this function (E-295)
    names = String[]
    if trig isa String
        push!(names, trig)
    elseif trig isa AbstractVector
        for t in trig
            t isa String && push!(names, t)
        end
    end
    _EXT_TRIGGERS[r] = names
    return true
end

"""
    owner(m::Module)

`:Julia` for Core, Base, the compiler and the standard libraries; otherwise the package's root module,
a package extension's parent's owner; a module defined directly under `Main` is its own owner, and
`Main` is the session's (traits §12.1).
"""
function owner(m::Module)
    r = Base.moduleroot(m)
    if r === Main && m !== Main
        while parentmodule(m) !== Main
            m = parentmodule(m)
        end
        return m
    end
    (r === Base || r === Core || r === Base.Compiler) && return :Julia
    nameof(r) in _stdlib_names() && return :Julia
    p = _extension_parent(r)
    return p === nothing ? r : owner(p)
end

"""
    @joint_owners P1 P2 …

At the top level of a package's own module: the packages named own its functions and types with it
(traits §12.1). Not symmetric, not transitive.
"""
macro joint_owners(names...)
    (!isempty(names) && all(n -> n isa Symbol, names)) ||
        error("@joint_owners: name the packages, as in `@joint_owners DiffEqBase OrdinaryDiffEqCore`")
    owner(__module__) === __module__ ||
        error("@joint_owners: only a package's own module declares its joint owners, not $(__module__)")
    return esc(:(const __tw_joint_owners__ = $(Tuple(names))))
end

_joint_names(@nospecialize(o)) =
    o isa Module && isdefined(o, :__tw_joint_owners__) ? getfield(o, :__tw_joint_owners__)::Tuple : ()

"Whether `definer` owns what the owner `o` owns: it is `o`, or a joint owner `o` names."
owns(@nospecialize(definer), @nospecialize(o)) =
    definer === o || (definer isa Module && nameof(definer) in _joint_names(o))

_type_owner(@nospecialize(T)) = (S = Base.unwrap_unionall(T); S isa DataType ? owner(S.name.module) : nothing)

function _owners!(acc::Base.IdSet{Any}, @nospecialize(T))
    if T isa Union
        _owners!(acc, T.a); _owners!(acc, T.b)
    elseif T isa UnionAll
        _owners!(acc, T.var.ub); _owners!(acc, T.body)
    elseif T isa Core.TypeofVararg
        isdefined(T, :T) && _owners!(acc, T.T)
    elseif T isa DataType
        push!(acc, owner(T.name.module))
        for p in T.parameters
            # a value as a type parameter belongs to its type's owner
            _owners!(acc, p isa Type || p isa TypeVar || p isa Core.TypeofVararg ? p : typeof(p))
        end
    elseif T isa TypeVar
        _owners!(acc, T.ub)          # a lower bound restricts nothing: `x::T where T >: Mine` applies to Any
    end
    return acc
end

"The owners of every function and type a signature names."
sig_owners(@nospecialize(sig)) = _owners!(Base.IdSet{Any}(), sig)

# one signature per Union member at the top level of each argument, at most `limit` combinations; a
# `Vararg` tail that may be empty gives the alternative without it too
const _NO_ARG = Ref(:no_arg)
_may_be_empty(@nospecialize(v)) = !isdefined(v, :N) || v.N isa TypeVar || v.N == 0
function _sig_alternatives(@nospecialize(sig), limit::Int = 256)
    body = Base.unwrap_unionall(sig)
    body isa DataType || return Any[sig]
    alts = Any[]
    for p in body.parameters
        if p isa Union
            push!(alts, Base.uniontypes(p))
        elseif p isa TypeVar && p.ub isa Union
            push!(alts, Base.uniontypes(p.ub))
        elseif p isa Core.TypeofVararg && _may_be_empty(p)
            push!(alts, Any[p, _NO_ARG])
        else
            push!(alts, Any[p])
        end
    end
    # plain loops, so that the hooks' precompiled code holds all of it (no `collect` of a closure's
    # generator compiled at a session's loads)
    n = 1
    for a in alts
        n *= length(a::Vector{Any})
    end
    n <= limit || return Any[sig]
    combos = Vector{Any}[Any[]]
    for a in alts
        next = Vector{Any}[]
        for c in combos, x in a::Vector{Any}
            c2 = copy(c)
            push!(c2, x)
            push!(next, c2)
        end
        combos = next
    end
    out = Any[]
    for c in combos
        ps = Any[]
        for x in c
            x === _NO_ARG || push!(ps, x)
        end
        push!(out, Tuple{ps...})
    end
    return out
end

"""
    owned_method(m::Method) -> Bool

Whether `m` is no pirate (traits §12.2): in each alternative of its signature (each `Union` member
taken separately, each arity a `Vararg` tail admits), its package owns the function or one of the
types. A `Union` with an own type, or a lower-bounded type variable, is no way around it.
"""
function owned_method(m::Method)
    definer = owner(m.module)
    for s in _sig_alternatives(m.sig)
        any(o -> owns(definer, o), sig_owners(s)) || return false
    end
    return true
end

_owner_name(@nospecialize(o)) = o === :Julia ? "Julia" : string(o)

# A membership is declared by the trait's owner or the type's owner (traits §12.1); one in a package
# extension names each of its triggers
function _check_membership_owner(mod::Module, @nospecialize(X), @nospecialize(member))
    definer = owner(mod)
    to = _type_owner(bare(X))
    mo = _type_owner(member)
    if !(owns(definer, to) || owns(definer, mo))
        throw(OwnershipError("@implement $(bare(X)) $member in $mod: $(_owner_name(definer)) owns neither " *
            "the trait (owned by $(_owner_name(to))) nor the type (owned by $(_owner_name(mo))); " *
            "the trait's owner or the type's owner declares it, a foreign pair in the trait owner's package extension"))
    end
    r = Base.moduleroot(mod)
    trig = _extension_parent(r) === nothing ? nothing : get(_EXT_TRIGGERS, r, nothing)
    if trig !== nothing
        named = Set{String}(string(nameof(Base.moduleroot(o))) for o in sig_owners(Tuple{bare(X), member}) if o isa Module)
        missing_ = [t for t in trig if !(t in named)]
        isempty(missing_) || throw(ImplementError(X, member,
            "a membership in the package extension $r names each of its triggers; it does not name $(join(missing_, ", "))"))
    end
    return nothing
end

# An operation that is an existing function may be served by methods in a block only for types the
# declaring package owns (traits §12.1)
function _check_block_owner(mod::Module, @nospecialize(f), @nospecialize(member))
    definer = owner(mod)
    owns(definer, owner(parentmodule(f))) && return nothing
    owns(definer, _type_owner(member)) && return nothing
    throw(OwnershipError("@implement in $mod: a method of $(parentmodule(f)).$(nameof(f)) for $member, " *
        "neither of which $(_owner_name(definer)) owns; declare the type's existing methods instead: " *
        "@implement X $member without a block"))
end

# a scope that declares `no_pirates` (bit 2 of the module's trait options) refuses a pirate
_no_pirates(m::Module) = (ccall(:jl_get_module_trait_options, Cint, (Any,), m) & 2) != 0

function _check_pirate(m::Method)
    _no_pirates(m.module) || return nothing
    owned_method(m) && return nothing
    throw(OwnershipError("$(m.name) at $(m.sig) in $(m.module) is a pirate: $(_owner_name(owner(m.module))) " *
        "owns neither the function nor a type in each of its signatures, and the scope declares `no_pirates`"))
end
