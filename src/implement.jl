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
        _check_membership_owner(mod, X, member)
    end
    foreach(X -> _forget_records!(X, member), traits)   # a redeclaration fixes them anew (traits §5.10, §5.11)
    defined = block === nothing ? Method[] : _define_block!(mod, traits, member, block)
    added = Method[]
    try
        for X in traits
            append!(added, Base.invokelatest(_implement_one!, mod, X, member, how))
        end
        # the forwarding's methods fix their calls once every trait's are defined: two traits forwarded
        # by one field may share an operation's method
        how.by === nothing || foreach(X -> _record_forwarders!(X, member, how.by), traits)
    catch
        # a refused membership takes its block's methods away; while an image is built a method cannot
        # be deleted, and the error fails the build
        if ccall(:jl_generating_output, Cint, ()) == 0
            foreach(Base.delete_method, defined)
            foreach(Base.delete_method, added)
        end
        rethrow()
    end
    return nothing
end

# A pattern member: a family (S{P} where P), a closed abstract type, a trait.
_is_pattern(@nospecialize(T)) = !(T isa DataType) || isabstracttype(T) || Base.has_free_typevars(T)

function _implement_one!(mod::Module, @nospecialize(X), @nospecialize(member), how::How)
    added = Method[]
    if _is_pattern(member)
        inst = _pattern_instance(X, member)
    else
        inst, receiver, problems = check_member(bare(X), member; stated = X, how)
        isempty(problems) || throw(ImplementError(X, member, problems))
    end
    receiver = how.by === nothing ? :self : :field
    if how.by !== nothing
        append!(added, _define_fwd!(mod, member, bare(X), how.by))
    end
    # every membership is an entry, `struct S <: X` too (traits §5.2): the image keeps it, its records come
    # back from it, the member hook runs for an abstract member's subtypes, the ambiguity report sees it
    try
        _declare!(member, inst, mod, how.by, receiver)
    catch err
        err isa ErrorException || rethrow()
        # a declared subtype stays a subtype of X: the module-end hook names the refusal, not a missing @implement
        member isa DataType && _declared_subtype(member, inst) &&
            (_REFUSED[(member.name, Base.unwrap_unionall(bare(X)).name)] = err.msg)
        throw(ImplementError(X, member, err.msg))
    end
    if !_is_pattern(member) || how.by !== nothing
        how.by === nothing || (_FORWARD_FIELD[(Base.unwrap_unionall(member)::DataType).name] = how.by)
    end
    _is_pattern(member) && _pending!(member, inst, how)
    _is_pattern(member) || _record_checks!(X, member, _records_at(X, member, X, how)...)
    push!(_IMPLEMENTED, (Base.unwrap_unionall(member).name, Base.unwrap_unionall(bare(X)).name))
    _is_pattern(member) || Base.invokelatest(_compile_ahead!, inst, member)   # compiling ahead (traits §16)
    return added
end

## What the hooks read (traits §5.2, §5.10, §5.11; lowering §11)

# every `@implement X S` of this session, as (S's TypeName, X's TypeName): the module-end hook
const _IMPLEMENTED = Set{Any}()
# a declared subtype's `@implement` the runtime refused (strict mode's ambiguity, another instance), with
# the reason: the module-end hook names it
const _REFUSED = Dict{Any,String}()

# The calls a membership fixed (traits §5.11): those a default serves at a member, and those its
# forwarding's methods serve. A later method that would take one is refused (the definition hook).
struct _FixedCall
    trait::Any       # the membership's trait
    source::Any      # the trait whose default serves the call, or the forwarding field (a Symbol)
    member::Any
    sig::Any         # Tuple{typeof(f), argument types…}
end

# The results a membership's check inferred within the declared result (traits §5.10). A later method
# that would serve the call is inferred at it, and refused where its result leaves the declared one.
struct _CheckedResult
    trait::Any       # the membership's trait
    contract::Any    # the contract the check read: a redeclared trait's operation is looked up anew
    op::Any          # the operation (an OperationDecl)
    member::Any
    sig::Any         # Tuple{typeof(f), argument types…}, the call the check inferred
    env::Any         # the trait's parameters at the member
    receiver::Any    # the receiver type
end

# function => the records under it: made where a check passes in the session, and rebuilt for each
# membership an image activates (`_sync_image_records!`).
const _FIXED_CALLS = IdDict{Any,Vector{Any}}()
const _CHECKED_RESULTS = IdDict{Any,Vector{Any}}()

function _record_checks!(@nospecialize(X), @nospecialize(member), defaults::Vector{Any}, results::Vector{Any})
    Xb = bare(X)
    for (src, f, sig) in defaults
        push!(get!(Vector{Any}, _FIXED_CALLS, f), _FixedCall(Xb, src, member, sig))
    end
    for (c, op, sig, env, R) in results
        push!(get!(Vector{Any}, _CHECKED_RESULTS, op.f), _CheckedResult(Xb, c, op, member, sig, env, R))
    end
    return nothing
end

# the forwarding's methods, each a call the membership fixes
function _record_forwarders!(@nospecialize(X), @nospecialize(member), by::Symbol)
    Xb = bare(X)
    for (f, sig) in _fwd_sigs(member, Xb)
        push!(get!(Vector{Any}, _FIXED_CALLS, f), _FixedCall(Xb, by, member, sig))
    end
    return nothing
end

# The signatures of the forwarding's methods `_define_fwd!` defines at `member` for `Xb`: for each
# required operation and arity, the receiver typed by the member, the further arguments untyped.
function _fwd_sigs(@nospecialize(member), @nospecialize(Xb))
    out = Tuple{Any,Any}[]
    c = contract(Xb)
    c === nothing && return out
    core = Base.unwrap_unionall(member)
    done = Set{Tuple{Any,Int,Bool}}()
    for op in c.operations
        op.hasdefault && continue
        key = (op.f, length(op.args), op.vararg)
        key in done && continue
        push!(done, key)
        ps = Any[i == op.receiver ? core : Any for i in 1:length(op.args)]
        op.vararg && (ps[end] = Vararg{ps[end]})
        push!(out, (op.f, Base.rewrap_unionall(Tuple{Core.Typeof(op.f), ps...}, member)))
    end
    return out
end

# a membership redeclared, or made again from an image's entry, fixes its calls and results anew
function _forget_records!(@nospecialize(X), @nospecialize(member))
    Xb = bare(X)
    for recs in values(_FIXED_CALLS)
        _forget_in!(recs, member, Xb)
    end
    for recs in values(_CHECKED_RESULTS)
        _forget_in!(recs, member, Xb)
    end
    return nothing
end

# a loop, not `filter!` with a closure: a closure over the trait would be compiled per trait (E-322)
function _forget_in!(recs::Vector{Any}, @nospecialize(member), @nospecialize(Xb))
    j = 0
    for i in eachindex(recs)
        r = recs[i]
        (getfield(r, :member) === member && getfield(r, :trait) === Xb) && continue
        j += 1
        recs[j] = r
    end
    resize!(recs, j)
    return nothing
end

# The memberships images activated (compiler §9), read from the runtime's list up to the library's
# cursor: for each in force, at a concrete member and a set with a contract, its records are made again,
# without inference (`_records_at`), the member's old ones forgotten first, so that a membership's
# records come back however often it is met. The membership and the contract are the record; the
# dictionaries are a cache of them (traits §5.10). Run before a definition or an image's methods are
# checked. A failure here warns and refuses nothing.
const _ENTRY_CURSOR = Ref(0)

function _sync_image_records!()
    n = Int(ccall(:jl_activated_memberships_count, Csize_t, ()))
    n <= _ENTRY_CURSOR[] && return nothing
    list = ccall(:jl_activated_memberships, Any, ())::Core.SimpleVector
    from = _ENTRY_CURSOR[] + 1
    _ENTRY_CURSOR[] = length(list)
    for i in from:length(list)
        en = list[i]
        try
            _records_from_entry!(en)
        catch err
            @warn "TraitWorld: the records of an image's membership were not made" entry = en exception = err
        end
    end
    return nothing
end

function _records_from_entry!(@nospecialize(en))
    getfield(en, :max_world, :acquire) == typemax(UInt64) || return nothing
    S = getfield(en, :member)
    isconcretetype(S) || return nothing    # a pattern's members get their records at their first use
    inst = getfield(en, :instance)
    X = bare(inst)
    (istrait(X) && contract(X) !== nothing) || return nothing
    # two images may leave two entries in force for one member and set (compiler C-84): the latest holds
    _latest_entry(S, getfield(en, :set)::Core.TypeName) === en || return nothing
    by = getfield(en, :by)
    how = How(by isa Symbol ? by : nothing)
    _forget_records!(X, S)
    _record_checks!(X, S, _records_at(X, S, inst, how)...)
    how.by === nothing || _record_forwarders!(X, S, how.by)
    return nothing
end

# the entry in force for the concrete member S in the set named `setname` that began last
function _latest_entry(@nospecialize(S), setname::Core.TypeName)
    best = nothing
    for e in getfield((Base.unwrap_unionall(S)::DataType).name, :memberships, :acquire)
        getfield(e, :set) === setname || continue
        getfield(e, :max_world, :acquire) == typemax(UInt64) || continue
        getfield(e, :member) == S || continue
        (best === nothing || getfield(e, :min_world) > getfield(best, :min_world)) && (best = e)
    end
    return best
end

# The definition hook (compiler §10.1). Before a method is visible: the scope's pirates, strict
# mode's walk, then the membership's own checks. After: strict mode's log, the bounded check.
function _definition_hook(m::Method, after::Bool)
    if after
        _strict_on_definition(m, true)   # strict mode's check after the definition (traits §12.3)
        return _check_bounded(m)
    end
    _check_pirate(m)                     # a scope that declares `no_pirates` (traits §12.2)
    _strict_on_definition(m, false)      # strict mode: a pirate that would win at a fact (traits §12.3)
    try
        _check_membership_calls(m)
    catch
        STRICT[] && _strict_log_stop!()  # the after branch, which stops strict mode's log, will not run
        rethrow()
    end
    return nothing
end

# A method about to be defined, or an image's method about to be activated, that would take a call a
# membership fixed (traits §5.11), make it ambiguous at the member, or serve a checked call with a result
# outside the declared one (traits §5.10), is refused: an ImplementError.
function _check_membership_calls(m::Method)
    _sync_image_records!()
    sig = Base.unwrap_unionall(m.sig)
    (sig isa DataType && !isempty(sig.parameters)) || return nothing
    fT = sig.parameters[1]
    (fT isa DataType && isdefined(fT, :instance)) || return nothing
    fixed = get(_FIXED_CALLS, fT.instance, nothing)
    checked = get(_CHECKED_RESULTS, fT.instance, nothing)
    fixed === nothing && checked === nothing && return nothing
    world = Base.get_world_counter()
    if fixed !== nothing
        for r in fixed
            r = r::_FixedCall
            s = typeintersect(r.sig, m.sig)      # the record's calls the method applies to
            (s === Union{} || !_would_win(m, s, world)) && continue
            how = r.source isa Symbol ? "the forwarding of $(r.trait) by the field $(r.source)" : "a default of $(bare(r.source))"
            throw(ImplementError(r.trait, r.member, "$how serves $(nameof(fT.instance)) at $(r.member) since its membership: " *
                                                   "define the method before `@implement`, or in its block"))
        end
    end
    checked === nothing && return nothing
    for r in checked
        r = r::_CheckedResult
        s = typeintersect(r.sig, m.sig)
        (s === Union{} || !_would_win(m, s, world)) && continue
        declared = _declared_result(r)
        declared === nothing && continue           # the trait no longer declares the operation
        f = nameof(fT.instance)
        cur = _current_method(s, world)
        if cur !== nothing && cur !== m && !(cur.sig == m.sig) &&
           ccall(:jl_type_morespecific, Cint, (Any, Any), m.sig, cur.sig) == 0
            throw(ImplementError(r.trait, r.member,
                "the method $m would make $f ambiguous with $cur at $s, the member $(r.member)'s call of " *
                "$(bare(r.trait))'s $(_declared(r.op, r.contract)): define it more specific than $cur, or not at this member"))
        end
        rt = _infer_new_method(m, s, world)
        rt <: declared && continue
        throw(ImplementError(r.trait, r.member,
            "the method $m would serve $s, the member $(r.member)'s call of $(bare(r.trait))'s " *
            "$(_declared(r.op, r.contract)), and infers its result as $rt, outside the declared $declared: " *
            "return within $declared, or do not define the method at this member"))
    end
    return nothing
end

# the declared result at the record's call, from the trait's contract now: a redeclared contract's
# operation of the same name and arguments, or nothing where it has none. A trait whose name now
# holds another type (a redeclaration that made a new type) has no members of its own any more.
function _declared_result(r::_CheckedResult)
    tn = (Base.unwrap_unionall(r.trait)::DataType).name
    Base.invokelatest(isdefinedglobal, tn.module, tn.name) &&
        Base.invokelatest(getglobal, tn.module, tn.name) === tn.wrapper || return nothing
    c = contract(r.trait)
    c === nothing && return nothing
    op = r.op
    if c !== r.contract
        k = findfirst(o -> o.name === op.name && length(o.args) == length(op.args) && o.receiver == op.receiver &&
                           o.vararg == op.vararg && !o.hasdefault, c.operations)
        k === nothing && return nothing
        op = c.operations[k]
    end
    d = try _eval_in(c, op.result, r.env, r.receiver) catch; nothing end
    return d isa Type ? d : nothing
end

# the one method dispatch selects at `s` now, or nothing (no method, or ambiguous)
function _current_method(@nospecialize(s), world::UInt)
    ms = Base._methods_by_ftype(s, nothing, 1, world, false, Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
    (ms isa Vector && length(ms) == 1) || return nothing
    return (ms[1]::Core.MethodMatch).method
end

# The result of the method `m`, not yet in the table, at the call `s`: `m` itself inferred, without
# caching (the method may be refused). A call `m` makes to its own function sees the methods in force,
# so a self-recursive method's recursion is inferred at the method it replaces. Any on a failure.
function _infer_new_method(m::Method, @nospecialize(s), world::UInt)
    try
        _, sparams = ccall(:jl_type_intersection_with_env, Any, (Any, Any), s, m.sig)::Core.SimpleVector
        mi = Base.specialize_method(m, s, sparams)
        frame = CC.typeinf_frame(CC.NativeInterpreter(world), mi, false)
        frame === nothing && return Any
        return CC.widenconst(CC.ignorelimited(frame.result.result))
    catch
        return Any
    end
end

# The image hook (compiler §10.1): an image's method that the membership checks refuse stays inactive,
# with a warning (traits §5.10, §5.11); strict mode's winning pirates too (lowering §13).
function _image_methods_hook(ms::Vector{Any}, pkg::String)
    drop = Any[]
    for m in ms
        m isa Method || continue
        try
            _check_membership_calls(m)
        catch e
            e isa ImplementError || rethrow()
            @warn "$pkg: a method left inactive" method = m exception = e
            push!(drop, m)
        end
    end
    for m in _strict_image_refusals(ms)
        m in drop || push!(drop, m)
    end
    return drop
end

# The module-end hook (compiler §10.1): the methods that waited for later definitions are classified
# (compiler §6.7), and a type the module defines with a trait as its declared supertype, and no
# `@implement` for it, is refused at the module's end (traits §5.2).
function _module_end_hook(m::Module)
    _end_pending_bounded(m)
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
        # a set whose contract no `@trait` declared (Base's `IO`, traits §9b): a declared subtype is a
        # member, as in Julia
        contract(X) === nothing && continue
        (S.name, X.name) in _IMPLEMENTED && continue
        kind = isabstracttype(S) ? "abstract type" : "struct"
        why = get(_REFUSED, (S.name, X.name), nothing)
        why === nothing || throw(ImplementError(X.name.wrapper, S.name.wrapper,
            "$kind $(S.name.name) <: $(X.name.name): its `@implement` was refused: $why"))
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

# A member's forwarding (traits §5.5; lowering §2): _fwd(t::S, ::Type{X}) = t.f, and for each of X's
# required operations a method at the member that calls the operation on the field, so that the
# trait's method for a required operation serves no type that joins later (compiler §5.6). The
# methods are the membership's, as its declaration is: no block's owner rule. Returns the methods.
function _define_fwd!(mod::Module, @nospecialize(member), @nospecialize(Xb), by::Symbol)
    f = GlobalRef(@__MODULE__, :_fwd)
    Core.eval(mod, :($f(t::$member, ::Type{$Xb}) = getfield(t, $(QuoteNode(by)))))
    m = which(_fwd, Tuple{member isa UnionAll ? Base.unwrap_unionall(member) : member, Type{Xb}})
    _FWD_FIELDS[m] = by
    defined = Method[m]
    c = contract(Xb)
    c === nothing && return defined
    done = Set{Tuple{Any,Int,Bool}}()
    for op in c.operations
        op.hasdefault && continue
        key = (op.f, length(op.args), op.vararg)
        key in done && continue
        push!(done, key)
        fref = GlobalRef(parentmodule(op.f), nameof(op.f))
        names = Symbol[nm for (nm, _) in op.args]
        rname = names[op.receiver]
        sigargs = Any[i == op.receiver ? Expr(:(::), nm, member) : nm for (i, nm) in enumerate(names)]
        callargs = Any[i == op.receiver ? :(getfield($rname, $(QuoteNode(by)))) : nm for (i, nm) in enumerate(names)]
        if op.vararg
            sigargs[end] = Expr(:..., sigargs[end])
            callargs[end] = Expr(:..., callargs[end])
        end
        before = Set{Method}(methods(op.f))
        Core.eval(mod, Expr(:function, Expr(:call, fref, sigargs...), Expr(:call, fref, callargs...)))
        for m2 in methods(op.f)
            m2 in before || push!(defined, m2)
        end
    end
    return defined
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
            _check_block_owner(mod, op.f, member)
            fref = GlobalRef(parentmodule(op.f), nameof(op.f))
            before = Set{Method}(methods(op.f))
            sig = Expr(:call, fref, newargs...)
            # a family's variables are the method's static parameters: in scope in its body (`T` in
            # `@implement CoreIntegrator{Vector{T}, Float64} Tsit5Integrator{T, M} where {T, M}`)
            if member isa UnionAll && (wh = _where_exprs(member)) !== nothing
                k = findfirst(a -> Meta.isexpr(a, :(::)) && a.args[2] === member, newargs)
                if k !== nothing
                    newargs[k] = Expr(:(::), newargs[k].args[1], _type_expr(Base.unwrap_unionall(member)))
                    sig = Expr(:where, Expr(:call, fref, newargs...), wh...)
                end
            end
            Core.eval(mod, Expr(:function, sig, body))
            for m in methods(op.f)
                m in before || push!(defined, m)
            end
        end
    catch
        ccall(:jl_generating_output, Cint, ()) == 0 && foreach(Base.delete_method, defined)
        rethrow()
    end
    return defined
end

# A pattern's variables as a `where` clause's expressions, `T` or `T <: ub` (nothing where a variable has a
# lower bound, which a method's `where` would have to state too)
function _where_exprs(@nospecialize(member))
    out = Any[]
    u = member
    while u isa UnionAll
        v = u.var
        v.lb === Union{} || return nothing
        push!(out, v.ub === Any ? v.name : Expr(:<:, v.name, _type_expr(v.ub)))
        u = u.body
    end
    return out
end
# A type as an expression, its free variables by their names (for a method's signature)
function _type_expr(@nospecialize(t))
    t isa TypeVar && return t.name
    t isa Symbol && return QuoteNode(t)
    t isa Union && return Expr(:curly, GlobalRef(Core, :Union), Any[_type_expr(x) for x in Base.uniontypes(t)]...)
    if t isa UnionAll
        return Expr(:where, _type_expr(Base.unwrap_unionall(t)), (_where_exprs(t)::Vector{Any})...)
    end
    t isa Core.TypeofVararg && return isdefined(t, :N) ? Expr(:curly, GlobalRef(Core, :Vararg), _type_expr(t.T), _type_expr(t.N)) :
                                       isdefined(t, :T) ? Expr(:curly, GlobalRef(Core, :Vararg), _type_expr(t.T)) : GlobalRef(Core, :Vararg)
    t isa DataType || return t
    Base.has_free_typevars(t) || return t
    ref = GlobalRef(t.name.module, t.name.name)
    return Expr(:curly, ref, Any[_type_expr(p) for p in t.parameters]...)
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

"the patterns declared in this session whose members are checked at their first use: (pattern, trait instance, how)"
const _PATTERNS = Any[]
_pending!(@nospecialize(member), @nospecialize(inst), how::How) = push!(_PATTERNS, (member, inst, how))

# a loop: a closure over the pattern would be compiled per pattern type (E-322)
function _has_pattern(out::Vector{Any}, @nospecialize(pat), @nospecialize(inst))
    for p in out
        p[1] == pat && p[2] == inst && return true
    end
    return false
end

# The patterns of `X` that may hold `T`: those declared in this session, and those on the runtime's
# entries of `T`'s TypeName and its supertypes', which a package image keeps (the library's table is
# this session's only: another package's additions to it are not in that package's image).
function _patterns_for(@nospecialize(T), @nospecialize(X))
    out = Any[]
    for p in _PATTERNS
        bare(p[2]) === bare(X) && push!(out, p)
    end
    Xname = (Base.unwrap_unionall(bare(X))::DataType).name
    d = Base.unwrap_unionall(T)
    while d isa DataType && d !== Any
        for en in getfield(d.name, :memberships, :acquire)
            getfield(en, :set) === Xname || continue
            getfield(en, :max_world, :acquire) == typemax(UInt64) || continue
            pat, inst = getfield(en, :member), getfield(en, :instance)
            _is_pattern(pat) || continue
            # not a pattern `@implement` declared: `Dynamic{X}`'s membership, a trait's supertraits
            core = Base.unwrap_unionall(pat)
            (core isa DataType && (core.name === Base.unwrap_unionall(Dynamic).name || istrait(core))) && continue
            _has_pattern(out, pat, inst) && continue
            by = getfield(en, :by)
            push!(out, (pat, inst, How(by isa Symbol ? by : nothing)))
        end
        d = d.super
    end
    return out
end

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
    for (pat, inst, how) in _patterns_for(T, X)
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
        # a member checked at its first use keeps its check while it is a member (traits §5.10, §5.11)
        _record_checks!(X, T, _records_at(X, T, Tinst, how)...)
        return nothing
    end
    return nothing
end

_subst_tv(@nospecialize(t), tv::TypeVar, @nospecialize(v)) =
    Base.has_free_typevars(t) ? ccall(:jl_instantiate_type_in_env, Any, (Any, Any, Ptr{Any}), t, UnionAll(tv, t), Ref{Any}(v)) : t
