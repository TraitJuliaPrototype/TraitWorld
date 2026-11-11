# The checks of a membership (traits §5.10; lowering §3, step 3): completeness, results,
# fields, parameters and supertraits, by plain inference at the member.

"How a member serves a trait: by a forwarding field, or by its own methods and the defaults."
struct How
    by::Union{Nothing,Symbol}
end

"""
    check_member(X, S; stated = nothing, how = How(nothing)) -> (instance, receiver, problems)

Check the type `S` against the contract of the trait `X` (and its supertraits'). `stated` is
the trait instance the declaration wrote, `X{p…}`, or the bare `X`. Returns the trait's
instance at `S`, the receiver kind (`:self`, `:field`, `:none`) and the problems found.
"""
function check_member(@nospecialize(X), @nospecialize(S); @nospecialize(stated = X), how::How = How(nothing))
    problems = String[]
    c = contract(X)
    c === nothing && return (stated, :self, String["$X has no contract: it is not a trait"])
    env = _params_at(c, S, stated, how, problems)
    inst = _instance(c, env, stated)
    served_own = _check_contract!(problems, c, env, S, inst, how)
    _check_concrete!(problems, c, env, S, how)
    # the supertraits' contracts, at the parameters the subtrait gives them (traits §4.5)
    if inst isa DataType
        for (sc, senv) in _contracts_of(inst)
            sc === c && continue
            sinst = _instance(sc, senv, bare(sc.trait))
            served_own |= _check_contract!(problems, sc, senv, S, sinst, how)
            _agree!(problems, sc, sinst, S, how)
            _check_concrete!(problems, sc, senv, S, how)
        end
    end
    receiver = how.by !== nothing ? :field : served_own ? :self : :none
    return (inst, receiver, problems)
end

# A trait's concrete parts (traits §14): each named parameter, and Self, concrete at a member; a
# pattern's members are checked at their first use. Self is the receiver type: the forwarding
# field's where the member forwards (traits §4.4)
function _check_concrete!(problems, c::Contract, env, @nospecialize(S), how::How = How(nothing))
    isempty(c.concrete) && return
    (S isa DataType && !Base.has_free_typevars(S)) || return
    for (n, level) in c.concrete
        v = n === :Self ? _receiver_type(S, how) : get(env, n, nothing)
        v === nothing && continue
        is_concrete_part(v) && continue
        tag = level === :enforce ? "@enforce_concrete_only" : "@warn_on_abstract"
        msg = "$(n === :Self ? "Self" : "the parameter $n") is $v, which is not concrete ($tag $n in $(bare(c.trait)))"
        if level === :enforce
            push!(problems, msg)
        else
            key = (c.trait, n, S)
            key in _CONCRETE_WARNED || (push!(_CONCRETE_WARNED, key); @warn "$S as a member of $(bare(c.trait)): $msg")
        end
    end
end

# the instance of the trait named `tn` among S's declared supertypes, or nothing
function _declared_instance(S::DataType, tn::Core.TypeName)
    t = S
    while t !== Any
        t.name === tn && return t
        t = supertype(t)
    end
    return nothing
end

# the receiver type: the member, or its forwarding field's type (traits §4.4)
_receiver_type(@nospecialize(S), how::How) =
    how.by === nothing ? S : (S isa DataType && hasfield(S, how.by) ? fieldtype(S, how.by) : Any)

# The parameters' values at S: stated, from the declared fields' stored types, from the
# equations at Self; then their bounds (traits §3.2).
function _params_at(c::Contract, @nospecialize(S), @nospecialize(stated), how::How, problems)
    env = Dict{Symbol,Any}()
    source = Dict{Symbol,String}()
    # the declared supertype (`struct S <: X{Int}`): the parameters come from the definition (traits §5.2)
    decl = S isa DataType ? _declared_instance(S, Base.unwrap_unionall(c.trait).name) : nothing
    if decl !== nothing
        for (i, p) in enumerate(c.params)
            v = decl.parameters[i]
            v isa TypeVar && continue
            env[p] = v
            source[p] = "declared, $(S.name.name) <: $decl"
        end
    end
    sdt = Base.unwrap_unionall(stated)
    if stated isa DataType && sdt.name === Base.unwrap_unionall(c.trait).name
        for (i, p) in enumerate(c.params)
            v = sdt.parameters[i]
            v isa TypeVar && continue
            if haskey(env, p) && !(env[p] == v)
                push!(problems, "the parameter $p is $(env[p]) ($(source[p])) and $v (stated)")
            else
                env[p] = v
                haskey(source, p) || (source[p] = "stated")
            end
        end
    end
    if S isa DataType
        for f in c.fields
            any(p -> _mentions(f.type, p) && !haskey(env, p), c.params) || continue
            f.name in c.inputs && continue           # a property named by an input: stated
            hasfield(S, f.name) || continue          # reported by the field check
            stored = fieldtype(S, f.name)
            tvs = Dict{Symbol,TypeVar}(p => TypeVar(p) for p in c.params if _mentions(f.type, p))
            pat = try
                _eval_in(c, f.type, merge(Dict{Symbol,Any}(env), Dict{Symbol,Any}(tvs)), _receiver_type(S, how))
            catch
                continue
            end
            order = collect(values(tvs))
            if pat isa TypeVar
                # the field's type is the parameter itself: `u::U` gives U = the stored type
                vals = Any[stored]
                order = TypeVar[pat]
            else
                wrapped = foldr((tv, acc) -> UnionAll(tv, acc), order; init = pat)
                stored <: wrapped || continue           # reported by the field check
                env_ = ccall(:jl_type_intersection_with_env, Any, (Any, Any), stored, wrapped)::Core.SimpleVector
                vals = env_[2]
                length(vals) == length(order) || continue
            end
            for (k, tv) in enumerate(order)
                v = vals[k]
                v isa TypeVar && continue
                p = tv.name
                if haskey(env, p) && !(env[p] == v)
                    push!(problems, "the parameter $p is $(env[p]) ($(source[p])) and $v (the field $(f.name)::$(stored))")
                else
                    env[p] = v
                    source[p] = "the field $(f.name)"
                end
            end
        end
    end
    self = _receiver_type(S, how)
    for (p, ex) in c.equations
        v = try
            _eval_in(c, ex, env, self)
        catch err
            push!(problems, "the equation $p = $ex fails at $self: $(sprint(showerror, err))")
            continue
        end
        if haskey(env, p) && !(env[p] == v)
            push!(problems, "the parameter $p is $(env[p]) ($(source[p])) but its equation $p = $ex gives $v")
        else
            env[p] = v
            source[p] = "the equation"
        end
    end
    for (i, p) in enumerate(c.params)
        if !haskey(env, p)
            push!(problems, "the parameter $p is not determined: no field or equation defines it; state it, @implement $(bare(c.trait)){…} $S")
            continue
        end
        b = c.bounds[i]
        b === nothing && continue
        bt = try _eval_in(c, b, env, self) catch; continue end
        env[p] isa Type && bt isa Type && !(env[p] <: bt) &&
            push!(problems, "the parameter $p = $(env[p]) is not within its bound $b")
    end
    return env
end

function _instance(c::Contract, env, @nospecialize(stated))
    length(env) == length(c.params) || return stated
    isempty(c.params) && return c.trait
    return bare(c.trait){Any[env[p] for p in c.params]...}
end

# Completeness, results and fields of one contract at S. Returns whether S serves an
# operation by its own method.
function _check_contract!(problems, c::Contract, env, @nospecialize(S), @nospecialize(inst), how::How)
    own = false
    R = _receiver_type(S, how)
    complete_env = length(env) == length(c.params)
    if how.by !== nothing
        # forwarding: the field's type is a member by its own methods or the defaults; no chain
        if !(S isa DataType && hasfield(S, how.by))
            push!(problems, "$S has no field $(how.by) to forward $(bare(c.trait)) to")
        elseif !(R <: inst)
            push!(problems, "the field $(how.by)::$R is not a member of $inst: forwarding needs a member, by its own methods or the defaults")
        elseif !(_fwd_method(R, bare(c.trait)) === nothing)
            push!(problems, "the field $(how.by)::$R forwards $(bare(c.trait)) itself: forwarding does not chain")
        end
        for f in c.fields
            f.name === how.by && !f.isconst &&
                push!(problems, "the forwarding field $(how.by) is also a writable declared field")
        end
    elseif complete_env
        for op in c.operations
            tt = _call_types(c, op, env, R)
            tt === nothing && (push!(problems, "the declared signature of $(op.name) cannot be evaluated at $S"); continue)
            m = _serving_method(op, tt)
            if m === nothing
                op.hasdefault && continue        # a default serves the operation at S

                h = _hidden_method(op, tt)
                if h !== nothing
                    push!(problems, "$(op.name)'s method $(h.sig) takes any receiver, so the trait's method, more specific, " *
                                    "would hide it: define $(op.name) at $S")
                else
                    push!(problems, "no method serves $(_declared(op, c)) at $S$(_near(op, R))")
                end
                continue
            end
            if _untyped_receiver(m, op)
                # a method that takes any receiver loses to the trait's method, or is ambiguous with it,
                # once S is a member (traits §6.2; open issue 150)
                push!(problems, "$(op.name)'s method $(_callform(m.sig)) takes any receiver, so the trait's method, more specific, " *
                                "would hide it: define $(op.name) at $S")
                continue
            end
            own = true
            declared = try _eval_in(c, op.result, env, R) catch; nothing end
            declared isa Type || continue
            # at a further argument declared abstract (an iteration state, say), inference says little:
            # the method's existence is checked, and each call through the trait asserts the result (§7.9)
            _open_further(op, tt) && continue
            rt = Base.infer_return_type(op.f, tt)
            # the declared result as written, and what it is at S where that differs (`T` = `Float64`)
            dstr = string(op.result) == string(declared) ? "$declared" : "$(op.result) = $declared"
            rt <: declared ||
                push!(problems, "$(op.name)'s method at $S infers its result as $rt, " *
                                (declared <: rt ? "wider than" : "outside") * " the declared $dstr")
        end
    end
    complete_env && S isa DataType && _check_fields!(problems, c, env, S)
    return own
end

# The records a passed check leaves (traits §5.10, §5.11; lowering §3, step 7): for each operation of
# the contract and its supertraits', a checked result where a method serves it and its result is
# inferred (not at an abstract further argument), a fixed call where a default serves it. No inference:
# the same at `@implement`, at a first use, and for a membership an image activated, whose check passed
# when the image was built. A forwarding member's calls are its forwarders' (`_fwd_sigs`).
function _records_at(@nospecialize(X), @nospecialize(S), @nospecialize(stated), how::How)
    defaults, results = Any[], Any[]
    c = contract(bare(X))
    (c === nothing || how.by !== nothing) && return defaults, results
    env = _params_at(c, S, stated, how, String[])
    inst = _instance(c, env, stated)
    _records_walk!(defaults, results, c, env, S, how)
    if inst isa DataType
        for (sc, senv) in _contracts_of(inst)
            sc === c && continue
            _records_walk!(defaults, results, sc, senv, S, how)
        end
    end
    return defaults, results
end

function _records_walk!(defaults, results, c::Contract, env, @nospecialize(S), how::How)
    length(env) == length(c.params) || return nothing
    R = _receiver_type(S, how)
    for op in c.operations
        tt = _call_types(c, op, env, R)
        tt === nothing && continue
        sig = Tuple{Core.Typeof(op.f), tt.parameters...}
        if _serving_method(op, tt) === nothing
            op.hasdefault && push!(defaults, (c.trait, op.f, sig))
            continue
        end
        declared = try _eval_in(c, op.result, env, R) catch; nothing end
        declared isa Type || continue
        _open_further(op, tt) && continue
        push!(results, (c, op, sig, env, R))
    end
    return nothing
end

function _where_env(c::Contract, op::OperationDecl, env, @nospecialize(R))
    env2 = Dict{Symbol,Any}(env)
    for w in op.wherevars
        if w isa Symbol
            env2[w] = Any
        elseif Meta.isexpr(w, :<:) && w.args[1] isa Symbol
            env2[w.args[1]] = _eval_in(c, w.args[2], env2, R)
        end
    end
    return env2
end

# The call's argument types: the receiver at R, the others as declared.
function _call_types(c::Contract, op::OperationDecl, env, @nospecialize(R))
    ts = Any[]
    for (i, (_, ty)) in enumerate(op.args)
        if i == op.receiver
            push!(ts, R)
        else
            t = ty === nothing ? Any : try
                # the operation's own `where` variables at their bounds: a variable the trait's parameters
                # do not fix is checked at its widest (`get(d, k, default::D) where {D}`)
                env2 = isempty(op.wherevars) ? env : _where_env(c, op, env, R)
                _eval_in(c, ty, env2, R)
            catch
                return nothing
            end
            t isa TypeVar && (t = t.ub)
            t isa Type || return nothing
            push!(ts, (op.vararg && i == length(op.args)) ? Vararg{t} : t)
        end
    end
    return Tuple{ts...}
end

# The method that serves the operation at the call types, other than the trait's own method. At a further
# argument declared abstract (an iteration state), a method that meets the declared signature serves:
# the member's own state is narrower (traits §5.10)
function _serving_method(op::OperationDecl, @nospecialize(tt))
    open = _open_further(op, tt)
    return _first_serving(Tuple{Core.Typeof(op.f), tt.parameters...}, Base.get_world_counter(), !open)
end
# whether an argument other than the receiver is declared abstract (a loop: a closure over `tt` would be
# compiled per call type, E-322)
function _open_further(op::OperationDecl, @nospecialize(tt))
    ps = tt.parameters::Core.SimpleVector
    for i in 1:length(ps)
        i != op.receiver && !isconcretetype(ps[i]) && return true
    end
    return false
end
# whether a serving method's argument at the receiver's position is untyped (`Any`)
function _untyped_receiver(m::Method, op::OperationDecl)
    sig = Base.unwrap_unionall(m.sig)
    (sig isa DataType && op.receiver + 1 <= length(sig.parameters)) || return false
    p = sig.parameters[op.receiver + 1]
    Base.isvarargtype(p) && (p = Base.unwrapva(p))
    p isa TypeVar && (p = p.ub)
    return p === Any
end
# A method untyped at the receiver (a function's fallback, `mul!(C, A, B)`) that would serve the
# operation but that the trait's method, more specific there, hides (open issue 150)
function _hidden_method(op::OperationDecl, @nospecialize(tt))
    ps = Any[tt.parameters...]
    op.receiver <= length(ps) || return nothing
    ps[op.receiver] = Any
    return _first_serving(Tuple{Core.Typeof(op.f), ps...}, Base.get_world_counter())
end
function _first_serving(@nospecialize(T), world::UInt, covers::Bool = true)
    ms = Base._methods_by_ftype(T, -1, world)
    ms isa Vector || return nothing
    for match in ms
        m = (match::Core.MethodMatch).method
        _is_trait_method(m) && continue
        (match.fully_covers || !covers) || continue
        return m
    end
    return nothing
end

# a trait's method calls _fwd on its receiver (lowering §2); no other method does
const _IS_TRAIT_METHOD = IdDict{Method,Bool}()
_is_trait_method(m::Method) = get!(_IS_TRAIT_METHOD, m) do
    any(s -> s isa GlobalRef && s.mod === TraitWorld && s.name === :_fwd, _code_refs(m))
end
function _code_refs(m::Method)
    isdefined(m, :generator) && return Any[]      # a generated method has no lowered code of its own
    src = Base.uncompressed_ast(m)
    out = Any[]
    for st in src.code
        st isa GlobalRef && push!(out, st)
        st isa Expr && _collect_refs!(out, st)
    end
    return out
end
_collect_refs!(out, ex::Expr) = (for a in ex.args; a isa GlobalRef ? push!(out, a) : a isa Expr && _collect_refs!(out, a); end; out)

_declared(op::OperationDecl, c::Contract) =
    string(op.name, "(", join([ty === nothing ? string(n) : string(n, "::", ty) for (n, ty) in op.args], ", "), ")::", op.result)

function _near(op::OperationDecl, @nospecialize(R))
    ms = Method[]
    for m in methods(op.f)
        _is_trait_method(m) && continue
        ps = (Base.unwrap_unionall(m.sig)::DataType).parameters
        op.receiver + 1 <= length(ps) || continue
        p = ps[op.receiver + 1]
        p isa Type && !Base.has_free_typevars(p) && typeintersect(R, p) !== Union{} && push!(ms, m)
    end
    isempty(ms) && return ""
    return "; its methods there: " * join(string.(ms), "; ")
end

# Declared fields (traits §4.3): present, typed, writable where declared so.
function _check_fields!(problems, c::Contract, env, S::DataType)
    for f in c.fields
        declared = try _eval_in(c, f.type, env, S) catch; nothing end
        declared isa Type || continue
        # a field named by an input is the property at the input's value (`HasProperty{:ps, R}`: `x.ps`)
        name = f.name in c.inputs ? get(env, f.name, nothing) : f.name
        name isa Symbol || continue
        if _has_own_getproperty(S)
            rt = Base.infer_return_type(_getprop_at(name), (S,))
            rt <: declared || push!(problems, "getproperty(::$S, :$(name)) infers $rt, not the declared $(f.type) = $declared")
            continue
        end
        if !hasfield(S, name)
            push!(problems, "the field $(name)::$(f.type) is missing: $S stores $(join(fieldnames(S), ", "))")
            continue
        end
        stored = fieldtype(S, name)
        if f.isconst
            stored <: declared || push!(problems, "the field $(name) is stored as $stored, not as the declared $declared")
        else
            ismutabletype(S) || (push!(problems, "the field $(name) is writable through the trait, but $S is immutable: declare it @const"); continue)
            isconst(S, name) && (push!(problems, "the field $(name) is const in $S, but writable through the trait: declare it @const"); continue)
            stored == declared || push!(problems, "the writable field $(name) is stored as $stored; the trait declares $declared")
        end
    end
end

"`getproperty` at the constant name `n`, as a call `x.n` infers it"
struct _GetPropAt{n} end
(::_GetPropAt{n})(x) where {n} = getproperty(x, n)
_getprop_at(name::Symbol) = _GetPropAt{name}()
_has_own_getproperty(@nospecialize(S)) = which(getproperty, Tuple{S, Symbol}).module !== Base

# A member that joins a supertrait by a membership of its own serves it the same way (traits §4.5).
function _agree!(problems, sc::Contract, @nospecialize(sinst), @nospecialize(S), how::How)
    S isa DataType || return
    S <: sinst || return
    theirs = _fwd_method(S, bare(sc.trait))
    mine = how.by
    theirfield = theirs === nothing ? nothing : _fwd_field(theirs)
    theirfield === mine ||
        push!(problems, "$S is a member of $(bare(sc.trait)) already, served $(theirfield === nothing ? "by its own methods" : "by the field $theirfield"), not $(mine === nothing ? "by its own methods" : "by the field $mine")")
end

# the method of _fwd for (S, X) other than the fallback and Dynamic's, or nothing
function _fwd_method(@nospecialize(S), @nospecialize(Xb))
    m = which(_fwd, Tuple{S, Type{Xb}})
    return m.sig === Tuple{typeof(_fwd), Any, Type} ? nothing : m
end
_fwd_field(m::Method) = get(_FWD_FIELDS, m, nothing)
const _FWD_FIELDS = IdDict{Method,Symbol}()
