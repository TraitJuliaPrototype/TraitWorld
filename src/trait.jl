# @trait (traits §4; lowering §2).

"what `_fwd` answers for a member that serves a trait by its own methods or the defaults"
struct NoForward end
const NOFWD = NoForward()

# The forwarding of a member: its field for a member that forwards the trait `X` by it (traits
# §5.5), else NOFWD. `@implement X S by f` adds a method for S; Dynamic forwards to its object.
# Inference resolves it at a member's type, so the trait's method takes one branch.
_fwd(@nospecialize(t), @nospecialize(X::Type)) = NOFWD

"""
    @trait X
    @trait X{P, Q <: B} <: (A, C{P}) begin
        op(x::X, i::Int)::R                 # an operation
        op2(x::X)::R2 = body                # an operation with a default
        u::U                                # a declared field
        @const p::P                         # a read-only declared field
        T = eltype(Self)                    # a parameter defined by an equation of Self
        @input N                            # input parameters
    end

Declare the trait `X`: an open abstract type with the contract the body states (traits §4).
It defines, in this order, the type, its supertraits' memberships, the operations' functions,
the trait's method for each operation, the contract on the type's `TypeName`, and
`Dynamic{X}`'s membership (lowering §2). A trait's declaration changes no compiled code.
"""
macro trait(head, body = nothing)
    return _trait(__module__, head, body)
end

function _trait(mod::Module, head, body)
    name, params, bounds, supers = _parse_head(head)
    items = _parse_body(name, params, body)
    T = isempty(params) ? name : Expr(:curly, name, params...)
    tvdefs = Any[bounds[i] === nothing ? :($(params[i]) = Core.TypeVar($(QuoteNode(params[i])))) :
                 :($(params[i]) = Core.TypeVar($(QuoteNode(params[i])), $(bounds[i]))) for i in eachindex(params)]
    t = gensym(:trait)
    # the pattern X{P…} where {P…}, with the parameters' variables shared by what follows
    wrapped = isempty(params) ? name :
        foldr((p, acc) -> :(Core.UnionAll($p, $acc)), params; init = T)
    Z = gensym(:Z)
    lib(s) = GlobalRef(@__MODULE__, s)
    out = Expr(:block)
    # 1. the type, open from its declaration (compiler §4.1)
    push!(out.args, :(Core.declare_global($mod, $(QuoteNode(name)), false)), Expr(:latestworld))
    push!(out.args, Expr(:let, Expr(:block, tvdefs...), quote
        local $t = Core._abstracttype($mod, $(QuoteNode(name)), Core.svec($(params...)))
        $(lib(:_open_set!))($t)
        Core._setsuper!($t, Any)
        Core._typebody!(false, $t)
        Core.declare_const($mod, $(QuoteNode(name)), $t)
    end), Expr(:latestworld))
    # 2. the supertraits' memberships: X{P…} where {P…} in A{q…}
    for s in supers
        push!(out.args, Expr(:let, Expr(:block, tvdefs...),
            :($(lib(:_declare!))($wrapped, $s, $mod, nothing, :self))), Expr(:latestworld))
    end
    # 3. the operations' functions: a plain name makes a function of the module
    for op in items.ops
        op.fname isa Symbol && push!(out.args, Expr(:function, op.fname))
    end
    # 4. the trait's method for each operation
    arities = Dict{Tuple{Any,Int},Int}()
    for op in items.ops
        k = (op.fname, length(op.args))
        arities[k] = get(arities, k, 0) + 1
    end
    for op in items.ops
        push!(out.args, _trait_method(name, params, bounds, op, arities[(op.fname, length(op.args))] > 1))
        # its declared result, covering every member (compiler §6.8), unless it names Self
        _mentions(op.result, :Self) && continue
        push!(out.args, Expr(:latestworld),
              :($(lib(:_set_declared!))($(op.fname), $mod, $(length(op.args) + 1), $(QuoteNode(op.result)))))
    end
    push!(out.args, Expr(:latestworld))
    # 5. the contract on the TypeName
    opdecls = Any[:($(lib(:OperationDecl))($(QuoteNode(_opname(op.fname))), $(op.fname),
                     Pair{Symbol,Any}[$([:($(QuoteNode(a)) => $(QuoteNode(ty))) for (a, ty) in op.args]...)],
                     $(op.vararg), $(op.receiver), $(QuoteNode(op.result)),
                     Any[$(QuoteNode.(op.wherevars)...)], $(op.body !== nothing))) for op in items.ops]
    fielddecls = Any[:($(lib(:FieldDecl))($(QuoteNode(f[1])), $(QuoteNode(f[2])), $(f[3]))) for f in items.fields]
    eqs = Any[:($(QuoteNode(p)) => $(QuoteNode(e))) for (p, e) in items.equations]
    push!(out.args, :($(lib(:_set_contract!))($name, $(lib(:Contract))($name, $mod,
        Symbol[$(QuoteNode.(params)...)], Any[$(QuoteNode.(bounds)...)], Symbol[$(QuoteNode.(items.inputs)...)],
        Any[$(QuoteNode.(supers)...)], $(lib(:OperationDecl))[$(opdecls...)],
        $(lib(:FieldDecl))[$(fielddecls...)], Pair{Symbol,Any}[$(eqs...)], $(QuoteNode(items.attribute))))))
    # the declared fields' names and types, read by inference (compiler §7.1)
    isempty(items.fields) || push!(out.args, :($(lib(:_set_declared_fields!))($name, $mod,
        Symbol[$([QuoteNode(f[1]) for f in items.fields]...)], Any[$([QuoteNode(f[2]) for f in items.fields]...)])))
    # 6. Dynamic{X}'s membership: Dynamic{Z} where {P…, Z <: X{P…}}, forwarding by `object`
    dynpat = foldr((p, acc) -> :(Core.UnionAll($p, $acc)), params;
                   init = :(Core.UnionAll($Z, $(lib(:Dynamic)){$Z})))
    push!(out.args, Expr(:let, Expr(:block, tvdefs..., :($Z = Core.TypeVar($(QuoteNode(:Z)), $T))),
        :($(lib(:_declare!))($dynpat, $T, $mod, :object, :field))), Expr(:latestworld))
    push!(out.args, nothing)
    return esc(out)
end

_opname(f) = f isa Symbol ? f : (f::Expr).args[end] isa QuoteNode ? (f.args[end]::QuoteNode).value : f.args[end]

# `X` | `X{P…}` | `X <: S` | `X{P…} <: (S, …)`  →  (name, params, bounds, supertraits)
function _parse_head(head)
    supers = Any[]
    if Meta.isexpr(head, :<:)
        s = head.args[2]
        supers = Meta.isexpr(s, :tuple) ? Any[s.args...] : Any[s]
        head = head.args[1]
    end
    head isa Symbol && return head, Symbol[], Any[], supers
    if Meta.isexpr(head, :curly) && head.args[1] isa Symbol
        params = Symbol[]
        bounds = Any[]
        for p in head.args[2:end]
            if p isa Symbol
                push!(params, p); push!(bounds, nothing)
            elseif Meta.isexpr(p, :<:) && p.args[1] isa Symbol
                push!(params, p.args[1]); push!(bounds, p.args[2])
            else
                error("@trait: a parameter is a name, with a bound or not: $p")
            end
        end
        return head.args[1]::Symbol, params, bounds, supers
    end
    error("@trait expects X, X{P…}, X <: A or X{P…} <: (A, …); got $head")
end

function _parse_body(name::Symbol, params::Vector{Symbol}, body)
    ops = Any[]
    fields = Tuple{Symbol,Any,Bool}[]
    equations = Pair{Symbol,Any}[]
    inputs = Symbol[]
    attribute = :none
    if body !== nothing
        Meta.isexpr(body, :block) || error("@trait $name: the body is a begin … end block")
        for item in body.args
            item isa LineNumberNode && continue
            if Meta.isexpr(item, :macrocall)
                m = item.args[1]
                margs = Any[a for a in item.args[2:end] if !(a isa LineNumberNode)]
                if m === Symbol("@const")
                    f = margs[1]
                    (Meta.isexpr(f, :(::)) && length(f.args) == 2 && f.args[1] isa Symbol) ||
                        error("@trait $name: @const declares a field, name::Type: $f")
                    push!(fields, (f.args[1], f.args[2], true))
                elseif m === Symbol("@input")
                    for a in margs
                        a in params || error("@trait $name: @input $a names no parameter")
                        push!(inputs, a)
                    end
                elseif m === Symbol("@default_dynamic")
                    attribute = :dynamic
                elseif m === Symbol("@default_compiled")
                    attribute = :compiled
                else
                    error("@trait $name: $m is not an item of a trait's body")
                end
            elseif Meta.isexpr(item, :(::)) && length(item.args) == 2 && item.args[1] isa Symbol
                push!(fields, (item.args[1], item.args[2], false))
            elseif Meta.isexpr(item, :(::)) || Meta.isexpr(item, :where) || Meta.isexpr(item, :call)
                push!(ops, _parse_op(name, item, nothing))
            elseif Meta.isexpr(item, :(=)) || Meta.isexpr(item, :function)
                lhs, rhs = item.args[1], item.args[2]
                if lhs isa Symbol
                    lhs in params || error("@trait $name: $lhs = … defines no parameter of $name")
                    any(e -> e[1] === lhs, equations) && error("@trait $name: $lhs is defined twice")
                    push!(equations, lhs => rhs)
                else
                    push!(ops, _parse_op(name, lhs, rhs))
                end
            else
                error("@trait $name: cannot read $item")
            end
        end
    end
    for (p, _) in equations, f in fields
        # a parameter defined by an equation and by a field is defined twice
        _mentions(f[2], p) && f[2] === p && error("@trait $name: $p is defined by a field and by an equation")
    end
    return (ops = ops, fields = fields, equations = equations, inputs = inputs, attribute = attribute)
end

function _parse_op(trait::Symbol, sig, body)
    wherevars = Any[]
    while Meta.isexpr(sig, :where)
        append!(wherevars, sig.args[2:end])
        sig = sig.args[1]
    end
    (Meta.isexpr(sig, :(::)) && length(sig.args) == 2 && Meta.isexpr(sig.args[1], :call)) ||
        error("@trait $trait: an operation declares its result type, f(x::$trait, …)::R; got $sig")
    call, result = sig.args[1], sig.args[2]
    fname = call.args[1]
    (fname isa Symbol || Meta.isexpr(fname, :.)) || error("@trait $trait: an operation's name is f or Module.f: $fname")
    args = Pair{Symbol,Any}[]
    vararg = false
    receiver = 0
    cargs = call.args[2:end]
    for (i, a) in enumerate(cargs)
        Meta.isexpr(a, :parameters) && error("@trait $trait: an operation has no keyword arguments: $call")
        if Meta.isexpr(a, :...)
            i == length(cargs) || error("@trait $trait: only the last argument is a vararg: $call")
            vararg = true
            a = a.args[1]
        end
        local nm, ty
        if a isa Symbol
            nm, ty = a, nothing
        elseif Meta.isexpr(a, :(::)) && length(a.args) == 2 && a.args[1] isa Symbol
            nm, ty = a.args[1], a.args[2]
        elseif Meta.isexpr(a, :(::)) && length(a.args) == 1
            nm, ty = gensym(:arg), a.args[1]
        else
            error("@trait $trait: an argument is name, name::T or ::T: $a")
        end
        if receiver == 0 && !vararg && (ty === nothing || _is_self(ty, trait))
            receiver = i
        end
        push!(args, nm => ty)
    end
    receiver == 0 && error("@trait $trait: $call has no argument typed by $trait or Self, the receiver")
    return (fname = fname, args = args, vararg = vararg, receiver = receiver, result = result,
            wherevars = wherevars, body = body)
end

_is_self(ty, trait::Symbol) = ty === trait || ty === :Self || (Meta.isexpr(ty, :curly) && ty.args[1] === trait)

_mentions(ex, s::Symbol) = ex === s || (ex isa Expr && any(a -> _mentions(a, s), ex.args))

_subst(ex, s::Symbol, by) = ex === s ? by : ex isa Expr ? Expr(ex.head, Any[_subst(a, s, by) for a in ex.args]...) : ex

# The trait's method for an operation (lowering §2): a method at the trait with the declared
# signature and result. A member that forwards gets the operation called on its field; one
# that a default serves, the default's body; any other member was refused at its check.
#
# Its further arguments are untyped, so that a member's own method, written at the member's type,
# is more specific and wins (traits §4.2) however it types them. An argument keeps its declared
# type where it binds a parameter or one of the operation's own `where` variables, or where two
# declarations of the operation at one arity differ (traits §4.1). The checks use the declared
# types (traits §5.10).
function _trait_method(trait::Symbol, params::Vector{Symbol}, bounds::Vector{Any}, op, overloaded::Bool = false)
    lib(s) = GlobalRef(@__MODULE__, s)
    full = isempty(params) ? trait : Expr(:curly, trait, params...)
    args = copy(op.args)
    rname, rty = args[op.receiver]
    selfy = rty === nothing || rty === :Self || rty === trait
    args[op.receiver] = rname => (selfy ? full : _subst(rty, :Self, full))
    wnames = Symbol[w isa Symbol ? w : Meta.isexpr(w, :<:) ? w.args[1] : w.args[1] for w in op.wherevars]
    sigargs = Any[]
    for (i, (nm, ty)) in enumerate(args)
        ty = ty === nothing ? nothing : _subst(ty, :Self, full)
        if i != op.receiver && ty !== nothing && !overloaded &&
           !any(p -> _mentions(ty, p), params) && !any(w -> _mentions(ty, w), wnames)
            ty = nothing
        end
        a = ty === nothing ? nm : Expr(:(::), nm, ty)
        (op.vararg && i == length(args)) && (a = Expr(:..., a))
        push!(sigargs, a)
    end
    resultself = _mentions(op.result, :Self)
    sigcore = Expr(:call, op.fname, sigargs...)
    sig = resultself ? sigcore : Expr(:(::), sigcore, op.result)
    sigex = Expr(:block, sig)
    used = Any[]
    for (i, p) in enumerate(params)
        (selfy || _mentions(sigex, p) || _mentions(op.result, p)) || continue
        push!(used, bounds[i] === nothing ? p : Expr(:<:, p, bounds[i]))
    end
    if !selfy && any(p -> _mentions(op.result, p) && !_mentions(sigex, p), params)
        error("@trait $trait: $(sigcore)'s result names a parameter its arguments do not: type the receiver $trait")
    end
    wheres = Any[used..., op.wherevars...]
    isempty(wheres) || (sig = Expr(:where, sig, wheres...))
    fwd = gensym(:fwd)
    names = Any[nm for (nm, _) in args]
    callargs = Any[i == op.receiver ? fwd : nm for (i, nm) in enumerate(names)]
    op.vararg && (callargs[end] = Expr(:..., callargs[end]))
    fwdcall = Expr(:call, op.fname, callargs...)
    resultself && (fwdcall = :($fwdcall::typeof($fwd)))
    plainargs = Any[nm for nm in names]
    op.vararg && (plainargs[end] = Expr(:..., plainargs[end]))
    serve = op.body === nothing ?
        :(throw(MethodError($(op.fname), ($(plainargs...),)))) :
        _subst(op.body, :Self, :(typeof($rname)))
    body = quote
        $fwd = $(lib(:_fwd))($rname, $trait)
        if $fwd isa $(lib(:NoForward))
            $serve
        else
            $fwdcall
        end
    end
    return Expr(:function, sig, body)
end
