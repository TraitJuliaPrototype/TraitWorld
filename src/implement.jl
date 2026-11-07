# @implement (traits §5; lowering §3).

"""
    @implement X S                          # S serves X by its own methods and the defaults
    @implement X S begin … end              # with the operations' methods written here
    @implement X S by f                     # forwarding: the field f serves X
    @implement (X, Y) S …                   # several traits at once
    @implement X{p…} S                      # stating parameters
    @implement X{T} S{T} where {T}          # a family: every instance of S
    @implement X A                          # A a closed abstract type or a trait

Declare `S` a member of the trait `X` (traits §5): define the block's methods, check the
contract (§5.10), and declare the membership. A refusal raises `ImplementError` and declares
nothing. The declaring code continues in the new world.
"""
macro implement(args...)
    return _implement_expr(__module__, args)
end

function _implement_expr(mod::Module, args)
    length(args) >= 2 || error("@implement X S [begin … end | by f]")
    traitsex, memberex = args[1], args[2]
    rest = args[3:end]
    by = nothing
    block = nothing
    wherevars = Any[]
    if Meta.isexpr(memberex, :where)
        append!(wherevars, memberex.args[2:end])
        memberex = memberex.args[1]
    end
    if length(rest) == 1 && Meta.isexpr(rest[1], :block)
        block = rest[1]
    elseif length(rest) == 2 && rest[1] === :by
        f = rest[2]
        if Meta.isexpr(f, :where)
            append!(wherevars, f.args[2:end])
            f = f.args[1]
        end
        f isa Symbol || error("@implement … by f: f is a field's name, got $f")
        by = f
    elseif !isempty(rest)
        error("@implement X S, then nothing, a begin … end block, or by f; got $(rest)")
    end
    traits = Meta.isexpr(traitsex, :tuple) ? Any[traitsex.args...] : Any[traitsex]
    names = Symbol[]
    tvdefs = Any[]
    for v in wherevars
        if v isa Symbol
            push!(names, v); push!(tvdefs, :($v = Core.TypeVar($(QuoteNode(v)))))
        elseif Meta.isexpr(v, :<:) && v.args[1] isa Symbol
            push!(names, v.args[1]); push!(tvdefs, :($(v.args[1]) = Core.TypeVar($(QuoteNode(v.args[1])), $(v.args[2]))))
        else
            error("@implement: a where variable is T or T <: B; got $v")
        end
    end
    call = :($(GlobalRef(@__MODULE__, :_implement_vars!))($mod, Any[$(traits...)], $memberex,
             Any[$(names...)], $(QuoteNode(by)), $(QuoteNode(block))))
    out = Expr(:block, Expr(:let, Expr(:block, tvdefs...), call), Expr(:latestworld), nothing)
    return esc(out)
end

"the field each type forwards a trait to, by type name (for `like`, traits §6.5)"
const _FORWARD_FIELD = IdDict{Core.TypeName,Symbol}()

# The member's pattern from its body and its `where` variables. A variable bounded by a `Union`
# declares one membership per type of the union (lowering §3):
# `@implement BoundedText I where {I <: Base.BitInteger}`.
function _implement_vars!(mod::Module, traits::Vector{Any}, @nospecialize(body), tvs::Vector{Any},
                          by::Union{Nothing,Symbol}, block)
    k = findfirst(tv -> (tv::TypeVar).ub isa Union, tvs)
    if k !== nothing
        tv = tvs[k]::TypeVar
        rest = Any[tvs[i] for i in eachindex(tvs) if i != k]
        for t in Base.uniontypes(tv.ub)
            b = body === tv ? t : _subst_tv(body, tv, t)
            _implement_vars!(mod, Any[_subst_tv(X, tv, t) for X in traits], b, rest, by, block)
        end
        return nothing
    end
    body isa TypeVar && throw(ArgumentError("@implement: the member is a type or a family of types; got $body"))
    member = foldr((tv, acc) -> UnionAll(tv, acc), tvs; init = body)
    return _implement!(mod, traits, member, by, block)
end

function _implement!(mod::Module, traits::Vector{Any}, @nospecialize(member), by::Union{Nothing,Symbol}, block)
    how = How(by)
    for X in traits
        istrait(X) || throw(ArgumentError("@implement: $X is not a trait"))
    end
    foreach(X -> _forget_defaults!(X, member), traits)   # a redeclaration fixes them anew (traits §5.11)
    defined = block === nothing ? Method[] : _define_block!(mod, traits, member, block)
    added = Method[]
    try
        for X in traits
            push!(added, Base.invokelatest(_implement_one!, mod, X, member, how)...)
        end
    catch
        foreach(Base.delete_method, defined)
        foreach(Base.delete_method, added)
        rethrow()
    end
    return nothing
end

# A pattern member: a family (S{P} where P), a closed abstract type, a trait.
_is_pattern(@nospecialize(T)) = !(T isa DataType) || isabstracttype(T) || Base.has_free_typevars(T)

function _implement_one!(mod::Module, @nospecialize(X), @nospecialize(member), how::How)
    added = Method[]
    defaults = Any[]
    if _is_pattern(member)
        inst = _pattern_instance(X, member)
    else
        inst, receiver, problems = check_member(bare(X), member; stated = X, how, defaults)
        isempty(problems) || throw(ImplementError(X, member, problems))
    end
    receiver = how.by === nothing ? :self : :field
    if how.by !== nothing
        m = _define_fwd!(mod, member, bare(X), how.by)
        push!(added, m)
    end
    # `struct S <: X` needs no entry: X is S's declared supertype (traits §5.2)
    if !(member isa DataType && _declared_subtype(member, inst))
        try
            _declare!(member, inst, mod, how.by, receiver)
        catch err
            err isa ErrorException || rethrow()
            throw(ImplementError(X, member, err.msg))
        end
    end
    if !_is_pattern(member) || how.by !== nothing
        how.by === nothing || (_FORWARD_FIELD[(Base.unwrap_unionall(member)::DataType).name] = how.by)
    end
    _is_pattern(member) && _pending!(member, inst, how)
    _record_defaults!(member, defaults)
    push!(_IMPLEMENTED, (Base.unwrap_unionall(member).name, Base.unwrap_unionall(bare(X)).name))
    return added
end

## What the hooks read (traits §5.2, §5.11; lowering §11)

# every `@implement X S` of this session, as (S's TypeName, X's TypeName): the module-end hook
const _IMPLEMENTED = Set{Any}()

# the operations a default serves at a member, fixed at its membership: function => [(trait, member,
# call types), …]. A later method that would take such a call is refused (the definition hook).
const _DEFAULT_SERVED = IdDict{Any,Vector{Any}}()

function _record_defaults!(@nospecialize(member), defaults::Vector{Any})
    for (X, f, tt) in defaults
        push!(get!(Vector{Any}, _DEFAULT_SERVED, f), (X, member, tt))
    end
end

function _forget_defaults!(@nospecialize(X), @nospecialize(member))
    for recs in values(_DEFAULT_SERVED)
        filter!(r -> !(r[2] === member && bare(r[1]) === bare(X)), recs)
    end
end

# The definition hook (compiler §10.1): before a method is visible, one that would take a call
# that a default serves at a member since its membership is refused (traits §5.11).
function _definition_hook(m::Method, after::Bool)
    after && return _check_bounded(m)
    sig = Base.unwrap_unionall(m.sig)
    (sig isa DataType && !isempty(sig.parameters)) || return nothing
    fT = sig.parameters[1]
    (fT isa DataType && isdefined(fT, :instance)) || return nothing
    recs = get(_DEFAULT_SERVED, fT.instance, nothing)
    recs === nothing && return nothing
    for (X, S, tt) in recs
        Tuple{fT, tt.parameters...} <: m.sig || continue
        throw(ImplementError(X, S, "a default of $(bare(X)) serves $(nameof(fT.instance)) at $S since its membership: " *
                                   "define the method before `@implement`, or in its block"))
    end
    return nothing
end

# The image hook (compiler §10.1): an image's method that would take a call a default serves at a
# member since its membership stays inactive, with a warning (traits §5.11).
function _image_methods_hook(ms::Vector{Any}, pkg::String)
    drop = Any[]
    for m in ms
        m isa Method || continue
        try
            _definition_hook(m, false)
        catch e
            e isa ImplementError || rethrow()
            @warn "$pkg: a method left inactive" method = m exception = e
            push!(drop, m)
        end
    end
    return drop
end

# The module-end hook (compiler §10.1): a type the module defines with a trait as its declared
# supertype, and no `@implement` for it, is refused at the module's end (traits §5.2).
function _module_end_hook(m::Module)
    for name in names(m; all = true)
        isdefined(m, name) || continue
        T = try getglobal(m, name) catch; continue end
        T isa Type || continue
        S = Base.unwrap_unionall(T)
        (S isa DataType && S.name.module === m && S.name.name === name) || continue
        istrait(S) && continue
        X = supertype(S)
        while X !== Any && !istrait(X)
            X = supertype(X)
        end
        X === Any && continue
        (S.name, X.name) in _IMPLEMENTED && continue
        kind = isabstracttype(S) ? "abstract type" : "struct"
        throw(ImplementError(X.name.wrapper, S.name.wrapper,
            "$kind $(S.name.name) <: $(X.name.name) needs `@implement $(X.name.name) $(S.name.name)` before the end of module $m"))
    end
    return nothing
end

# whether S is a subtype of the trait instance by its declared supertypes alone
function _declared_subtype(S::DataType, @nospecialize(inst))
    tn = (Base.unwrap_unionall(inst)::DataType).name
    t = S
    while t !== Any
        t.name === tn && return t <: inst
        t = supertype(t)
    end
    return false
end

# A family states its trait's instance with its own variables (traits §5.8; lowering §4).
function _pattern_instance(@nospecialize(X), @nospecialize(member))
    c = contract(X)
    if X isa UnionAll && c !== nothing && !isempty(c.params)
        throw(ImplementError(X, member, "a family or abstract member states the trait's instance with its variables, as @implement $(bare(X)){…} S{T} where {T}"))
    end
    return X
end

# the forwarding method of a member (lowering §2): _fwd(t::S, ::Type{X}) = t.f
function _define_fwd!(mod::Module, @nospecialize(member), @nospecialize(Xb), by::Symbol)
    f = GlobalRef(@__MODULE__, :_fwd)
    Core.eval(mod, :($f(t::$member, ::Type{$Xb}) = getfield(t, $(QuoteNode(by)))))
    m = which(_fwd, Tuple{member isa UnionAll ? Base.unwrap_unionall(member) : member, Type{Xb}})
    _FWD_FIELDS[m] = by
    return m
end

# The block's methods (traits §5.4): each a method of an operation of the traits, the
# receiver typed by the member, unannotated further arguments typed as declared.
function _define_block!(mod::Module, traits::Vector{Any}, @nospecialize(member), block::Expr)
    defined = Method[]
    try
        for item in block.args
            item isa LineNumberNode && continue
            (Meta.isexpr(item, :(=)) || Meta.isexpr(item, :function)) && Meta.isexpr(item.args[1], :call) ||
                error("@implement: a block holds the operations' methods, f(x, …) = …; got $item")
            call, body = item.args[1], item.args[2]
            fname = call.args[1]
            cargs = call.args[2:end]
            op, c, X = _find_op(traits, fname, length(cargs))
            env = _stated_env(c, X)
            newargs = Any[]
            for (i, a) in enumerate(cargs)
                if i == op.receiver
                    nm = a isa Symbol ? a : Meta.isexpr(a, :(::)) ? a.args[1] : error("@implement: the receiver is a name: $a")
                    push!(newargs, Expr(:(::), nm, member))
                elseif a isa Symbol
                    ty = op.args[i][2]
                    t = ty === nothing ? nothing : try _eval_in(c, ty, env, member) catch; nothing end
                    push!(newargs, t isa Type && !Base.has_free_typevars(t) ? Expr(:(::), a, t) : a)
                else
                    push!(newargs, a)
                end
            end
            fref = GlobalRef(parentmodule(op.f), nameof(op.f))
            before = Set{Method}(methods(op.f))
            Core.eval(mod, Expr(:function, Expr(:call, fref, newargs...), body))
            for m in methods(op.f)
                m in before || push!(defined, m)
            end
        end
    catch
        foreach(Base.delete_method, defined)
        rethrow()
    end
    return defined
end

function _find_op(traits::Vector{Any}, fname, n::Int)
    name = fname isa Symbol ? fname : Meta.isexpr(fname, :.) ? fname.args[end].value : fname
    for X in traits, (c, _) in _contracts_of(X isa DataType ? X : bare(X))
        for op in c.operations
            op.name === name && length(op.args) == n && return op, c, X
        end
    end
    error("@implement: $name with $n arguments is not an operation of $(join(traits, ", "))")
end

function _stated_env(c::Contract, @nospecialize(X))
    env = Dict{Symbol,Any}()
    X isa DataType || return env
    dt = Base.unwrap_unionall(X)::DataType
    dt.name === (Base.unwrap_unionall(c.trait)::DataType).name || return env
    for (i, p) in enumerate(c.params)
        v = dt.parameters[i]
        v isa TypeVar || (env[p] = v)
    end
    return env
end

## Members of a pattern, checked at their first use (lowering §4)

"the patterns whose members are checked at their first use: (pattern, trait instance, how)"
const _PATTERNS = Any[]
_pending!(@nospecialize(member), @nospecialize(inst), how::How) = push!(_PATTERNS, (member, inst, how))

"the kept answers per (member type, trait): `nothing` for a member that passed, else the error"
const _CHECKED = IdDict{Any,Any}()

"""
    check_first_use(T, X)

Check the member `T` of a pattern's membership in `X` (lowering §4), once: the answer is kept,
a failure too, and raised at every later use.
"""
function check_first_use(@nospecialize(T), @nospecialize(X))
    key = (T, bare(X))
    r = get(_CHECKED, key, missing)
    if r === missing
        _CHECKED[key] = _IN_PROGRESS
        r = try
            _check_pattern_member(T, X)
        catch err
            delete!(_CHECKED, key)
            rethrow()
        end
        _CHECKED[key] = r
        # a checked member of a pattern joins its trait's candidates for the split (compiler §7.2)
        r === nothing && isconcretetype(T) && ccall(:jl_register_candidate, Cvoid, (Any, Any), X, T)
    elseif r === _IN_PROGRESS
        throw(ImplementError(X, T, "the check of $T as a member of $(bare(X)) reaches $T again"))
    end
    r === nothing || throw(r)
    return nothing
end

struct InProgress end
const _IN_PROGRESS = InProgress()

# the runtime's member hook (compiler §10.4): called at a member's first use at dispatch
_member_hook(@nospecialize(T), @nospecialize(X)) = (check_first_use(T, X); nothing)

function _check_pattern_member(@nospecialize(T), @nospecialize(X))
    for (pat, inst, how) in _PATTERNS
        bare(inst) === bare(X) || continue
        T <: pat || continue
        # the trait's instance at T: the pattern's variables matched against T
        Tinst = inst
        if Base.has_free_typevars(inst)
            ti, vals = ccall(:jl_type_intersection_with_env, Any, (Any, Any), T, pat)::Core.SimpleVector
            tvs = Any[]
            p = pat
            while p isa UnionAll
                push!(tvs, p.var)
                p = p.body
            end
            Tinst = inst
            for (k, tv) in enumerate(tvs)
                Tinst = _subst_tv(Tinst, tv, vals[k])
            end
        end
        _, _, problems = check_member(bare(X), T; stated = Tinst, how)
        isempty(problems) || return ImplementError(Tinst, T, problems)
        return nothing
    end
    return nothing
end

_subst_tv(@nospecialize(t), tv::TypeVar, @nospecialize(v)) =
    Base.has_free_typevars(t) ? ccall(:jl_instantiate_type_in_env, Any, (Any, Any, Ptr{Any}), t, UnionAll(tv, t), Ref{Any}(v)) : t
