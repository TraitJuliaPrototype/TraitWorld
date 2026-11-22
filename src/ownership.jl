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

"""
The owners of every function and type a signature names; of a call of an owner-only function (traits
§12.2; compiler §1.2), the function's owner alone, whatever types it names.
"""
function sig_owners(@nospecialize(sig))
    o = _owner_only_owner(sig)
    o === nothing || return (s = Base.IdSet{Any}(); push!(s, o); s)
    return _owners!(Base.IdSet{Any}(), sig)
end

# The owner of the function of a signature where the function is owner-only (its owner's alone: by its
# module's `owner_only` option, a trait module's default, unless exported or public; or by `@owner_only`),
# else `nothing`. The compiler's test, which inference reads (compiler §1.2).
function _owner_only_owner(@nospecialize(sig))
    F = _owner_only_ftype(sig)
    return F === nothing ? nothing : owner(F.name.module)
end
# the type of the function of a signature where the function is owner-only, else `nothing`
function _owner_only_ftype(@nospecialize(sig))
    b = Base.unwrap_unionall(sig)
    b isa DataType && b <: Tuple && !isempty(b.parameters) || return nothing
    F = b.parameters[1]
    F isa TypeVar && (F = F.ub)
    if F === typeof(Core.kwcall) && length(b.parameters) >= 3
        F = b.parameters[3]
        F isa TypeVar && (F = F.ub)
    end
    F isa Type || return nothing
    F = Base.unwrap_unionall(F)
    (F isa DataType && CC.is_owner_only(F)) || return nothing
    return F
end

# What a message says of a method of another owner's owner-only function (traits §11.3, §12.2): the function, why it
# is owner-only, its owner, and that only the owner adds its methods, whatever types they are for
function _owner_only_what(@nospecialize(sig))
    F = _owner_only_ftype(sig)::DataType
    mod = F.name.module
    name = isdefined(F, :instance) ? nameof(F.instance) : F.name.name
    o = _owner_name(owner(mod))
    # an operation is owner-only only where its module closes it (traits §12.2)
    X = _declared_owner_only(mod, F.name.singletonname) ? _operation_of(F) : nothing
    X === nothing || return "`$name` is an operation of $X that $mod declares `@owner_only`: only $o adds methods to it, whatever types they are for"
    why = _declared_owner_only(mod, F.name.singletonname) ? "declared `@owner_only`" : "neither exported nor declared `public`"
    return "`$name` is an owner-only function of $mod ($why): only $o adds methods to it, whatever types they are for"
end
# and who may declare the method: what the owner writes to let others extend the function, or what the definer
# writes instead
function _owner_only_fix(@nospecialize(sig), @nospecialize(definer))
    F = _owner_only_ftype(sig)::DataType
    mod = F.name.module
    name = isdefined(F, :instance) ? nameof(F.instance) : F.name.name
    o = _owner_name(owner(mod))
    let_ = _declared_owner_only(mod, F.name.singletonname) ? "$mod does not declare it `@owner_only`" : "$mod declares it `public` or exports it"
    who = string(mod) == o ? "" : "$o "
    return "To let other modules add methods, $let_, or $(who)names $(_owner_name(definer)) a joint owner " *
        "(`@joint_owners`). Otherwise define a function of your own"
end
function _owner_list(s::Base.IdSet{Any})
    names = String[]
    for o in s
        push!(names, _owner_name(o))
    end
    return join(sort!(names), ", ")
end
# What a message says of a classic pirate (traits §11.3, §12.2): the owners of the function and of the types it
# names, and who may declare the method
function _classic_pirate_text(@nospecialize(sig), @nospecialize(definer))
    u = Base.unwrap_unionall(sig)
    fo, to = Base.IdSet{Any}(), Base.IdSet{Any}()
    if u isa DataType && u <: Tuple && !isempty(u.parameters)
        _owners!(fo, u.parameters[1])
        for p in u.parameters[2:end]
            _owners!(to, p)
        end
    end
    return "$(_owner_name(definer)) owns neither the function (owned by $(_owner_list(fo))) nor a type in each of its " *
        "signatures (owned by $(_owner_list(to))). The function's owner or the owner of a type it is for defines it, or " *
        "names $(_owner_name(definer)) a joint owner (`@joint_owners`)"
end

"""
    @owner_only f g …

At the top level of a function's own module: the functions named take methods from their owner only,
exported or not (traits §12.2). A method of one by another package is a pirate's, whatever types it
names; so a call of one is a fact at any signature (facts §3). A trait module's functions that it
neither exports nor declares `public` are owner-only by default, but for its traits' operations: a member's
package adds an operation's method for its own type. `@owner_only op` closes an operation.
"""
macro owner_only(names...)
    (!isempty(names) && all(n -> n isa Symbol, names)) ||
        error("@owner_only: name the module's functions, as in `@owner_only area perimeter`")
    return esc(Expr(:block, [:(ccall(:jl_set_owner_only, Cvoid, (Any, Any), @__MODULE__, $(QuoteNode(n)))) for n in names]...,
                    nothing))
end

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
types. A `Union` with an own type, or a lower-bounded type variable, is no way around it. A method of
an owner-only function is no pirate only where its package owns the function.
"""
function owned_method(m::Method)
    definer = owner(m.module)
    # a method of an owner-only function is its owner's only, whatever types it names (traits §12.2)
    fo = _owner_only_owner(m.sig)
    fo === nothing || return owns(definer, fo)
    for s in _sig_alternatives(m.sig)
        _owns_any(definer, sig_owners(s)::Base.IdSet{Any}) || return false
    end
    return true
end

# loops rather than `any` with a closure: a closure over an untyped value is compiled per the value's
# type where a run-time site reaches it, in every session (E-322)
function _owns_any(@nospecialize(definer), owners::Base.IdSet{Any})
    for o in owners
        owns(definer, o) && return true
    end
    return false
end

_owner_name(@nospecialize(o)) = o === :Julia ? "Julia" : string(o)

# A membership is declared by the trait's owner or the type's owner (traits §12.1); one in a package
# extension names each of its triggers. Returns whether the membership is a pirate's (traits §12.2):
# one by neither owner. It behaves as a pirate's method: refused in a scope that declares `no_pirates`,
# followed elsewhere with a warning, and under strict mode refused where it would change code compiled
# by facts (`_declare_pirate!`).
function _check_membership_owner(mod::Module, @nospecialize(X), @nospecialize(member))
    definer = owner(mod)
    to = _type_owner(bare(X))
    mo = _type_owner(member)
    if !(owns(definer, to) || owns(definer, mo))
        what = _pirate_membership_text(mod, X, member)
        _no_pirates(mod) && throw(OwnershipError(what * ": a pirate's membership, and the scope declares `no_pirates`. " *
            "The trait's owner or the type's owner declares it, a foreign pair in the trait owner's package extension"))
        STRICT[] || _warn_pirate_membership(what)
        return true
    end
    r = Base.moduleroot(mod)
    trig = _extension_parent(r) === nothing ? nothing : get(_EXT_TRIGGERS, r, nothing)
    if trig !== nothing
        named = Set{String}(string(nameof(Base.moduleroot(o))) for o in sig_owners(Tuple{bare(X), member}) if o isa Module)
        missing_ = [t for t in trig if !(t in named)]
        isempty(missing_) || throw(ImplementError(X, member,
            "a membership in the package extension $r names each of its triggers; it does not name $(join(missing_, ", "))"))
    end
    return false
end

function _pirate_membership_text(mod::Module, @nospecialize(X), @nospecialize(member))
    return "@implement $(bare(X)) $member in $mod: $(_owner_name(owner(mod))) owns neither the trait " *
        "(owned by $(_owner_name(_type_owner(bare(X))))) nor the type (owned by $(_owner_name(_type_owner(member))))"
end
function _warn_pirate_membership(what::String)
    @warn what * ": a pirate's membership. It is followed; code that relied on its absence is compiled again. " *
        "The trait's owner or the type's owner declares it, a foreign pair in the trait owner's package extension" maxlog = 1 _id = Symbol(what)
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
    definer = owner(m.module)
    head = "$(_callform(m.sig)) in $(m.module) is a pirate, and the scope declares `no_pirates`: "
    _owner_only_owner(m.sig) === nothing &&
        throw(OwnershipError(head * _classic_pirate_text(m.sig, definer)))
    throw(OwnershipError(head * _owner_only_what(m.sig) * ". " * _owner_only_fix(m.sig, definer)))
end

# A trait's operation is not owner-only by the default (traits §12.2): a member's package adds its method for its own
# type, exported or not; a module closes an operation with `@owner_only`. Where the trait is declared, each operation
# whose function is its owner's gets the binding's flag that Julia's compiler and the library's ownership read as open
# (`jl_set_open_operation`, compiler §1.2: `Compiler.is_owner_only`): from the declaration on, in the module's body,
# at the prompt, and in a module whose end has passed. The flag is no `public` declaration: `Base.ispublic` stays as
# the module writes it, and the module may still export the operation.
function _open_operations!(m::Module, @nospecialize(X))
    c = contract(X)
    (c === nothing || c.mod !== m) && return nothing
    for op in c.operations
        F = typeof(op.f)
        (F isa DataType && F <: Function && isdefined(F.name, :singletonname)) || continue
        fm = F.name.module
        owns(owner(m), owner(fm)) || continue
        ccall(:jl_set_open_operation, Cvoid, (Any, Any), fm, F.name.singletonname)
    end
    return nothing
end
# whether the function `M.name` is declared `@owner_only` (the binding's flag, compiler §1.2)
_declared_owner_only(M::Module, name::Symbol) = ccall(:jl_binding_owner_only_p, Cint, (Any, Any), M, name) != 0
# the trait of its module that declares the function of type `F` an operation, or nothing
function _operation_of(F::DataType)
    M = F.name.module
    for n in names(M; all = true)
        isdefined(M, n) || continue
        X = try getglobal(M, n) catch; continue end
        (X isa Type && istrait(Base.unwrap_unionall(X))) || continue
        c = contract(X)
        c === nothing && continue
        for op in c.operations
            typeof(op.f) === F && return bare(c.trait)
        end
    end
    return nothing
end
