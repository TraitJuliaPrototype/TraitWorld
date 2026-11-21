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
    return _at_source!(_trait(__module__, head, body), __source__)
end

# the code a declaration makes lies where the declaration is written: a message's "@ file:line" and a
# stack frame name the user's `@trait`, not this library's source
const _SRC_DIR = @__DIR__
function _at_source!(@nospecialize(ex), src::LineNumberNode)
    ex isa Expr || return ex
    for (i, a) in enumerate(ex.args)
        if a isa LineNumberNode
            # the user's own lines (a default's body) stay
            startswith(string(a.file), _SRC_DIR) && (ex.args[i] = src)
        elseif a isa Expr
            a.head === :quote || _at_source!(a, src)
        end
    end
    return ex
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
        $(isempty(items.inputs) ? nothing : :($(lib(:_set_inputs!))($t, $(_input_mask(name, params, items.inputs)))))
        Core._setsuper!($t, Any)
        Core._typebody!(false, $t)
        Core.declare_const($mod, $(QuoteNode(name)), $t)
    end), Expr(:latestworld))
    # 2. the supertraits' memberships: X{P…} where {P…} in A{q…}
    for s in supers
        push!(out.args, Expr(:let, Expr(:block, tvdefs...),
            :($(lib(:_declare_checked!))($wrapped, $s, $mod, nothing, :self))), Expr(:latestworld))
    end
    # 3. the operations' functions: a plain name makes a function of the module
    for op in items.ops
        op.fname isa Symbol && push!(out.args, Expr(:function, op.fname))
    end
    # 4. a method at the trait for each default, at each arity it is declared at (traits §4.2; lowering §2). An
    # operation without a default is an entry of the contract and no method (traits §4.1): each member serves it by
    # a method of its own type, and the kept forms by their forwarding methods (4b)
    arities = Dict{Tuple{Any,Int},Int}()
    for op in items.ops
        k = (op.fname, length(op.args))
        arities[k] = get(arities, k, 0) + 1
    end
    for op in items.ops
        op.body === nothing && continue
        push!(out.args, _trait_method(name, params, bounds, op, arities[(op.fname, length(op.args))] > 1, items.inputs))
    end
    push!(out.args, Expr(:latestworld))
    # 4b. the kept forms' forwarding methods for each operation without a default (lowering §2, §7): at
    # `Dynamic{<:X}`, the operation called on the box's object, a value typed by the set (an operation's call,
    # compiler §7.1); at `Compiled{<:X}`, on the wrapper's object, a static call of its own method
    seen = Set{Any}()
    for op in items.ops
        op.body === nothing || continue
        overloaded = arities[(op.fname, length(op.args))] > 1
        key = (op.fname, length(op.args), op.vararg, overloaded ? Any[ty for (_, ty) in op.args] : nothing)
        key in seen && continue
        push!(seen, key)
        append!(out.args, _kept_forwarders(name, params, bounds, op, overloaded))
    end
    # 4c. the kept forms' methods of each equation's function (lowering §2; traits §7.3, §7.4): a function of `Self`
    # that an equation names answers through a kept form as for its object
    vm = _equation_value_method(name, params, bounds, supers, items.equations)
    vm === nothing || push!(out.args, vm)
    for (p, e) in items.equations
        append!(out.args, _kept_equation(p, e))
    end
    push!(out.args, Expr(:latestworld))
    # 4d. the operations as entries the compiler reads (compiler §4.1): the function, the declared signature and
    # result as types in the trait's and the operation's variables, the default's method or nothing
    entries = Any[_operation_entry(name, params, op, mod) for op in items.ops]
    push!(out.args, Expr(:let, Expr(:block, tvdefs...),
        :($(lib(:_set_operations!))($name, Any[$(entries...)]))))
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
        $(lib(:FieldDecl))[$(fielddecls...)], Pair{Symbol,Any}[$(eqs...)], $(QuoteNode(items.attribute)),
        Pair{Symbol,Symbol}[$([:($(QuoteNode(n)) => $(QuoteNode(l))) for (n, l) in items.concrete]...)]))))
    # the trait's default (traits §4.6): `@default_dynamic` is recorded on the contract, where the expansion hook
    # reads it to make the forwarders (erasing.jl)
    # the declared fields' names and types, read by inference (compiler §7.1)
    isempty(items.fields) || push!(out.args, :($(lib(:_set_declared_fields!))($name, $mod,
        Symbol[$([QuoteNode(f[1]) for f in items.fields]...)], Any[$([QuoteNode(f[2]) for f in items.fields]...)],
        Symbol[$(QuoteNode.(items.inputs)...)])))
    # 6. Dynamic{X}'s membership: Dynamic{Z} where {P…, Z <: X{P…}}, forwarding by `object`
    dynpat = foldr((p, acc) -> :(Core.UnionAll($p, $acc)), params;
                   init = :(Core.UnionAll($Z, $(lib(:Dynamic)){$Z})))
    push!(out.args, Expr(:let, Expr(:block, tvdefs..., :($Z = Core.TypeVar($(QuoteNode(:Z)), $T))),
        :($(lib(:_declare_checked!))($dynpat, $T, $mod, :object, :field))), Expr(:latestworld))
    # 7. the wrapper's membership (W-151): Compiled{Z} where {P…, Z <: X{P…}}, forwarding by `object`, so that
    # the wrapper of a member of X is a member of X
    wpat = foldr((p, acc) -> :(Core.UnionAll($p, $acc)), params;
                 init = :(Core.UnionAll($Z, $(lib(:Compiled)){$Z})))
    push!(out.args, Expr(:let, Expr(:block, tvdefs..., :($Z = Core.TypeVar($(QuoteNode(:Z)), $T))),
        :($(lib(:_declare_checked!))($wpat, $T, $mod, :object, :field))), Expr(:latestworld))
    # a docstring written before `@trait` documents the trait's binding
    push!(out.args, :(Core.@__doc__ $name))
    push!(out.args, nothing)
    return esc(out)
end

"the mask of a trait's input parameters for the runtime (compiler §4.6): bit i for parameter i"
function _input_mask(name::Symbol, params::Vector{Symbol}, inputs::Vector{Symbol})
    m = 0x00
    for a in inputs
        i = findfirst(==(a), params)::Int
        i <= 8 || error("@trait $name: @input $a: only the first eight parameters can be inputs")
        m |= 0x01 << (i - 1)
    end
    return m
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
    concrete = Pair{Symbol,Symbol}[]
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
                elseif m === Symbol("@enforce_concrete_only") || m === Symbol("@warn_on_abstract")
                    level = m === Symbol("@enforce_concrete_only") ? :enforce : :warn
                    ns = isempty(margs) ? vcat(params, :Self) : margs
                    for a in ns
                        (a isa Symbol && (a in params || a === :Self)) ||
                            error("@trait $name: $m names the trait's parameters and Self; got $a")
                        push!(concrete, a => level)
                    end
                elseif m === Symbol("@default_dynamic")
                    attribute = :dynamic
                elseif m === Symbol("@default_compiled")
                    error("@trait $name: a trait without `@default_dynamic` takes a plain member as it is, compiled for ",
                          "its type (traits §4.6, §7.5); `@default_compiled` is not an item of a trait's body")
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
    for f in fields
        # a field named by a parameter is a property named by an input (`HasProperty{N, R}`: `N::R`)
        f[1] in params && !(f[1] in inputs) &&
            error("@trait $name: the field $(f[1]) is named by a parameter that is not an input: mark it @input $(f[1])")
    end
    for (p, _) in equations, f in fields
        # a parameter defined by an equation and by a field is defined twice
        _mentions(f[2], p) && f[2] === p && error("@trait $name: $p is defined by a field and by an equation")
    end
    return (ops = ops, fields = fields, equations = equations, inputs = inputs, attribute = attribute,
            concrete = concrete)
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
    # `f(…)::R where {D}` parses as `f(…)::(R where {D})`: the grammar's `where` is the operation's
    while Meta.isexpr(result, :where)
        append!(wherevars, result.args[2:end])
        result = result.args[1]
    end
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

# The trait's method for an operation with a default (lowering §2): a method at the trait with the declared
# signature and result. A kept form and a member that forwards get the operation called on the object or the
# field; any other member, the default's body.
#
# Its further arguments are untyped, so that a member's own method, written at the member's type,
# is more specific and wins (traits §4.2) however it types them. An argument keeps its declared
# type where it binds a parameter or one of the operation's own `where` variables, or where two
# declarations of the operation at one arity differ (traits §4.1). The checks use the declared
# types (traits §5.10).
# A further argument keeps its declared type only where it binds an input parameter or one of the
# operation's own `where` variables, or where two declarations at one arity differ (lowering §2): a
# parameter the receiver fixes (an equation of Self, or the instance a membership states) is bound by
# the receiver, so a member's own method, typed loosely there, still wins
function _trait_method(trait::Symbol, params::Vector{Symbol}, bounds::Vector{Any}, op, overloaded::Bool = false,
                       inputs::Vector{Symbol} = Symbol[])
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
           !any(p -> _mentions(ty, p), inputs) && !any(w -> _mentions(ty, w), wnames)
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
    serve = _subst(op.body, :Self, :(typeof($rname)))
    # a method `@trait` makes is not forwarded where its trait erases by default (compiler §6.3): a plain member
    # served by a default runs it as itself
    body = quote
        $(Expr(:meta, :no_forwarder))
        $fwd = $(lib(:_fwd))($rname, $trait)
        if $fwd isa $(lib(:NoForward))
            $serve
        else
            $fwdcall
        end
    end
    return Expr(:function, sig, body)
end

# The kept forms' forwarding methods for an operation without a default (lowering §2, §7): the receiver at
# `Dynamic{<:R}` and at `Compiled{<:R}`, `R` the declared receiver type, the operation called on its object,
# `getfield(d, :object)`: read so, a closed build knows the value for the object a box holds, never a box (compiler
# §7.6). Marked `:kept_forwarding`, so that the library's readers take them as the contract's own, as a trait's
# method that reads its receiver through `_fwd` (not checked at the box, no forwarder).
# A further argument keeps its declared type where that type names neither the trait's parameters, nor `Self`, nor
# the operation's own variables (`io::IO`, `i::Int`), so that the method is more specific than one of the function
# that types those arguments and takes any receiver (Base's `show(io::IO, x)`); the others are untyped, but where
# two declarations at one arity differ in them.
function _kept_forwarders(trait::Symbol, params::Vector{Symbol}, bounds::Vector{Any}, op, overloaded::Bool)
    lib(s) = GlobalRef(@__MODULE__, s)
    full = isempty(params) ? trait : Expr(:curly, trait, params...)
    rname, rty = op.args[op.receiver]
    selfy = rty === nothing || rty === :Self || rty === trait
    recty = selfy ? trait : _subst(rty, :Self, full)
    wnames = Symbol[w isa Symbol ? w : w.args[1] for w in op.wherevars]
    out = Any[]
    for K in (:Dynamic, :Compiled)
        sigargs = Any[]
        for (i, (nm, ty)) in enumerate(op.args)
            a = if i == op.receiver
                Expr(:(::), nm, Expr(:curly, lib(K), Expr(:<:, recty)))
            elseif ty !== nothing && (overloaded || !_mentions_any(ty, vcat(params, Symbol[:Self], wnames)))
                Expr(:(::), nm, _subst(ty, :Self, full))
            else
                nm
            end
            (op.vararg && i == length(op.args)) && (a = Expr(:..., a))
            push!(sigargs, a)
        end
        callargs = Any[i == op.receiver ? :($(GlobalRef(Core, :getfield))($rname, :object)) : nm for (i, (nm, _)) in enumerate(op.args)]
        op.vararg && (callargs[end] = Expr(:..., callargs[end]))
        sig = Expr(:call, op.fname, sigargs...)
        sigex = Expr(:block, sigargs...)
        wheres = Any[]
        for (i, p) in enumerate(params)
            _mentions(sigex, p) || continue
            push!(wheres, bounds[i] === nothing ? p : Expr(:<:, p, bounds[i]))
        end
        for w in op.wherevars
            wn = w isa Symbol ? w : w.args[1]
            _mentions(sigex, wn) && push!(wheres, w)
        end
        isempty(wheres) || (sig = Expr(:where, sig, wheres...))
        # (a line of this file: `_at_source!` puts the user's `@trait` there)
        body = Expr(:block, LineNumberNode(@__LINE__, Symbol(@__FILE__)), Expr(:meta, :no_forwarder),
                    Expr(:meta, :kept_forwarding), Expr(:call, op.fname, callargs...))
        push!(out, Expr(:function, sig, body))
    end
    return out
end

# The kept forms' methods of an equation's function, for an equation `P = f(Self)` of the trait (lowering §2; traits
# §7.3, §7.4): `f` answers through a kept form as for its object. At the type, since the equation's `Self` is a type:
# - the box: `f(::Type{Dynamic{Z}})` is the parameter's value at the box's trait instance `Z` (`_equation_value`): the
#   box's object is a member of that instance, and the equation is what the parameter's value is. Where no equation
#   of `Z` or a supertrait names `f`, `f`'s own method at `Type` answers;
# - the wrapper: `f(::Type{Compiled{W}}) = f(W)`, the object's own answer, which for each trait the object is a
#   member of is the parameter's value (its membership's check).
# At the value too, where `f` has no method at `Any` of its own (Base's `eltype(x)` passes the value's type on;
# `keytype` has none): `f(d::Dynamic) = f(typeof(d))`, `f(w::Compiled) = f(object)`.
# One method per function and kept form, not per trait: methods per trait at `Dynamic{Z}` for `Z <: X{P…}` would meet
# at the box of an intersection, and at the wrapper of a member of two traits whose equations name `f` (`Iterable{T}`,
# `Indexable{T}`: a `Vector`), neither more specific. The first trait that names `f` defines them; a later one finds
# them. An equation of another form (`N = length(fieldnames(Self))`) names no single function: none is made; nor for a
# function not yet defined where the trait is declared.
function _kept_equation(p::Symbol, e)
    (Meta.isexpr(e, :call) && length(e.args) == 2 && e.args[2] === :Self) || return Any[]
    lib(s) = GlobalRef(@__MODULE__, s)
    f = e.args[1]
    Z, W, T, v, x = gensym(:Z), gensym(:W), gensym(:T), gensym(:v), gensym(:x)
    meta = Expr(:meta, :no_forwarder)
    here() = LineNumberNode(@__LINE__, Symbol(@__FILE__))
    fsig(args...) = Expr(:call, Expr(:(::), Expr(:call, :typeof, f)), args...)
    boxtype = Expr(:function, Expr(:where, fsig(Expr(:(::), T, :(Type{$(lib(:Dynamic)){$Z}}))), Z), Expr(:block, here(), meta,
        :(local $v = $(lib(:_equation_value))($f, $Z)),
        :($v isa $(lib(:NoEquation)) ? invoke($f, Tuple{Type}, $T) : $v)))
    wraptype = Expr(:function, Expr(:where, fsig(Expr(:(::), :(Type{$(lib(:Compiled)){$W}}))), W),
        Expr(:block, here(), meta, Expr(:call, f, W)))
    boxval = Expr(:function, fsig(Expr(:(::), x, lib(:Dynamic))), Expr(:block, here(), meta, Expr(:call, f, :(typeof($x)))))
    wrapval = Expr(:function, fsig(Expr(:(::), x, lib(:Compiled))),
        Expr(:block, here(), meta, Expr(:call, f, :(getfield($x, :object)))))
    known = f isa Symbol ? Expr(:isdefined, f) : true     # a function the module defines after the trait: none
    return Any[Expr(:if, :($known && !$(lib(:_kept_answers))($f)), Expr(:block, boxtype, wraptype,
        Expr(:if, :(!hasmethod($f, Tuple{Any})), Expr(:block, boxval, wrapval))))]
end

# whether the kept forms' methods of the equation's function `f` are defined already (`_kept_equation`)
function _kept_answers(@nospecialize(f))
    sig = Tuple{typeof(f), Type{Dynamic{Z}}} where Z
    return any(m -> m.sig == sig, methods(f))
end

"what `_equation_value` answers where no equation of the trait instance or a supertrait names the function"
struct NoEquation end

"""
    _equation_value(f, X) -> the parameter's value, or NoEquation()

The value at the trait instance `X` of the parameter that an equation `P = f(Self)` of `X` or of a supertrait defines.
Each `@trait` adds its method at its exact instances, `Type{X{P…}}`, so the methods of two traits never meet; it
compares `f` with its equations' functions and asks its supertraits' instances in order. An intersection asks its
components in order. Every step is a call at constant types, so the value folds where the code is compiled.
"""
_equation_value(f::F, ::Type{X}) where {F, X} =
    X isa DataType && X.name === _ALL_NAME ? _equation_value_first(f, X.parameters[1]) : NoEquation()
const _ALL_NAME = Base.unwrap_unionall(Core.All).name     # (a signature at `All{C}` with `C` free is at `C`)
_equation_value_first(f::F, ::Type{Tuple{}}) where {F} = NoEquation()
function _equation_value_first(f::F, ::Type{C}) where {F, C <: Tuple}
    v = _equation_value(f, fieldtype(C, 1))
    return v isa NoEquation ? _equation_value_first(f, Base.tuple_type_tail(C)) : v
end

# a trait's method of `_equation_value`: its equations `P = f(Self)`, then its supertraits' instances
function _equation_value_method(trait::Symbol, params::Vector{Symbol}, bounds::Vector{Any}, supers::Vector{Any},
                                equations)
    lib(s) = GlobalRef(@__MODULE__, s)
    eqs = [(p, e.args[1]) for (p, e) in equations if Meta.isexpr(e, :call) && length(e.args) == 2 && e.args[2] === :Self]
    (isempty(eqs) && isempty(supers)) && return nothing
    full = isempty(params) ? trait : Expr(:curly, trait, params...)
    F, f, v = gensym(:F), gensym(:f), gensym(:v)
    body = Expr(:block, LineNumberNode(@__LINE__, Symbol(@__FILE__)), Expr(:meta, :no_forwarder))
    for (p, g) in eqs
        push!(body.args, :($f === $g && return $p))
    end
    for s in supers
        push!(body.args, :(local $v = $(lib(:_equation_value))($f, $s)), :($v isa $(lib(:NoEquation)) || return $v))
    end
    push!(body.args, :(return $(lib(:NoEquation))()))
    wheres = Any[F, (bounds[i] === nothing ? params[i] : Expr(:<:, params[i], bounds[i]) for i in eachindex(params))...]
    sig = Expr(:where, Expr(:call, lib(:_equation_value), Expr(:(::), f, F), Expr(:(::), :(Type{$full}))), wheres...)
    return Expr(:function, sig, body)
end

# An operation's entry for the compiler (compiler §4.1), as an expression evaluated with the trait's parameters
# bound to their type variables: `(f, sig, rt, default, vars)`, the declared signature and result built with the
# operation's own `where` variables, `Self` the trait at its parameters. A result that names `Self` inside another
# type declares none: the entry is left out.
function _operation_entry(trait::Symbol, params::Vector{Symbol}, op, mod::Module)
    lib(s) = GlobalRef(@__MODULE__, s)
    full = isempty(params) ? trait : Expr(:curly, trait, params...)
    rname, rty = op.args[op.receiver]
    selfy = rty === nothing || rty === :Self || rty === trait
    tys = Any[]
    for (i, (nm, ty)) in enumerate(op.args)
        t = i == op.receiver ? (selfy ? full : _subst(rty, :Self, full)) :
            ty === nothing ? :Any : _subst(ty, :Self, full)
        (op.vararg && i == length(op.args)) && (t = :(Vararg{$t}))
        push!(tys, t)
    end
    rt = op.result
    if _mentions(rt, :Self)
        (rt === :Self && selfy) || return :nothing
        rt = full
    end
    wdefs = Any[]
    wnames = Any[]
    for w in op.wherevars
        if w isa Symbol
            push!(wdefs, :($w = Core.TypeVar($(QuoteNode(w)))))
            push!(wnames, w)
        elseif Meta.isexpr(w, :<:)
            push!(wdefs, :($(w.args[1]) = Core.TypeVar($(QuoteNode(w.args[1])), $(w.args[2]))))
            push!(wnames, w.args[1])
        end
    end
    default = op.body === nothing ? :nothing :
        :($(lib(:_default_method))($(op.fname), $mod, $(length(op.args) + 1)))
    return Expr(:let, Expr(:block, wdefs...),
        :(($(op.fname), Tuple{typeof($(op.fname)), $(tys...)}, $rt, $default, Any[$(params...), $(wnames...)])))
end

_mentions_any(ex, names::Vector{Symbol}) = any(n -> _mentions(ex, n), names)
