# A trait's default as generated methods (W-151, the prototype of P1 as accepted; open issue 186).
#
# For a trait that declares `@default_dynamic` (and `Callable`, whose default is Julia's), a method at the trait
# is defined at the two kept forms, `Dynamic{<:X}` and `Compiled{<:X}`, and one forwarder takes a plain member
# and boxes it: `f(@nospecialize(t::X), …) = f(Dynamic{X}(t), …)`. Dispatch and the runtime do not change: the
# kept-form method is more specific than the forwarder, so a box and a wrapper reach the method as they are, and
# a plain member reaches it boxed. A trait without the default takes a plain member as it is (Julia's rule).
#
# The macro `@erasing` stands for a change in lowering: written at a method definition, it makes the methods
# that the definition would make by itself, as a positional default makes a second method. It decides by the
# traits' declarations when the definition is expanded; the runtime's method definition could decide by the
# evaluated signature instead, with nothing written.

"""
    erases(X) -> Bool

Whether a plain member passed at an argument typed by `X` is boxed by the forwarder `@erasing` makes: `X` is a
trait that declares `@default_dynamic`, or `Callable` (its default is `Dynamic`), or an intersection with such a
component.
"""
function erases(@nospecialize(X))
    u = Base.unwrap_unionall(X)
    u isa DataType || return false
    if u.name === Base.unwrap_unionall(Core.All).name
        tup = u.parameters[1]
        return tup isa DataType && any(erases, tup.parameters)
    end
    istrait(u) || return false
    c = contract(u)
    c === nothing || return c.attribute === :dynamic
    return ccall(:jl_get_default_attribute, Cint, (Any,), u) >= 2      # a set of Julia's own: `Callable`
end

# a kept form passes as it is; a plain member is boxed at the trait (a forwarder of several trait arguments)
_box_plain(@nospecialize(X::Type), @nospecialize(x)) = x isa Union{Dynamic, Compiled} ? x : Dynamic{X}(x)

"""
    @erasing function f(t::X, …) … end
    @erasing begin … end

The trait's default at a method (W-151): for each argument typed by a trait that erases by default (`erases`),
the method is defined at the two kept forms, `Dynamic{<:X}` and `Compiled{<:X}`, and one forwarder takes a plain
member and passes `Dynamic{X}(t)` on. In the body the argument is the kept form, not the object: `typeof(t)` is
the box's or the wrapper's type. An argument typed by a `where` variable bounded by such a trait (`t::C` with
`C <: X`) is treated so, with `C` the kept form's type. A trait whose parameters the signature leaves open
(`t::Column`, `t::Column{<:Real}`) cannot be boxed there: the argument takes a plain member as it is. Applied to a
block, each method definition in it.
"""
macro erasing(ex)
    return esc(_erasing(__module__, __source__, ex))
end

const _LIB = @__MODULE__
_g(s::Symbol) = GlobalRef(_LIB, s)

function _erasing(mod::Module, src::LineNumberNode, @nospecialize(ex))
    if Meta.isexpr(ex, :block) || Meta.isexpr(ex, :toplevel)
        out = Any[]
        for a in ex.args
            a isa LineNumberNode && (src = a)
            push!(out, _erasing(mod, src, a))
        end
        return Expr(ex.head, out...)
    end
    if Meta.isexpr(ex, :macrocall)
        # a docstring: the definition it documents
        if ex.args[1] === GlobalRef(Core, Symbol("@doc")) || ex.args[1] === Symbol("@doc")
            out = copy(ex)
            out.args[end] = _erasing(mod, src, ex.args[end])
            return out
        end
        # another macro at the definition (`@unbounded`, `@inline`, `Base.@nospecializeinfer`): its expansion
        ex2 = macroexpand(mod, ex; recursive = false)
        ex2 isa Expr && _split_def(ex2) !== nothing && return _erasing(mod, src, ex2)
        return ex
    end
    d = _split_def(ex)
    d === nothing && return ex
    return _erasing_def(mod, src, ex, d)
end

# f(args…; kws…)::R where {W…} → its parts, or nothing where `ex` is no method definition
function _split_def(@nospecialize(ex))
    (Meta.isexpr(ex, :function) || Meta.isexpr(ex, :(=))) && length(ex.args) == 2 || return nothing
    sig = ex.args[1]
    wheres = Any[]
    while Meta.isexpr(sig, :where)
        append!(wheres, sig.args[2:end])            # the outer variables first
        sig = sig.args[1]
    end
    rtype = nothing
    if Meta.isexpr(sig, :(::)) && length(sig.args) == 2
        rtype = sig.args[2]
        sig = sig.args[1]
    end
    Meta.isexpr(sig, :call) || return nothing
    return (call = sig, rtype = rtype, wheres = wheres)
end

# one positional argument as written
struct _Arg
    name::Any            # a Symbol; a gensym where the argument is unnamed
    named::Bool
    type::Any            # the type expression, or nothing
    default::Any         # the default's expression, or nothing
    hasdefault::Bool
    vararg::Bool
    nospec::Bool
end

function _parse_arg(@nospecialize(a))
    nospec = false
    if Meta.isexpr(a, :macrocall) && (a.args[1] === Symbol("@nospecialize") || a.args[1] == GlobalRef(Base, Symbol("@nospecialize")))
        nospec = true
        a = a.args[end]
    end
    default, hasdefault, vararg = nothing, false, false
    if Meta.isexpr(a, :kw)
        default, hasdefault = a.args[2], true
        a = a.args[1]
    end
    if Meta.isexpr(a, :...)
        vararg = true
        a = a.args[1]
    end
    a isa Symbol && return _Arg(a, true, nothing, default, hasdefault, vararg, nospec)
    if Meta.isexpr(a, :(::)) && length(a.args) == 2
        return _Arg(a.args[1], true, a.args[2], default, hasdefault, vararg, nospec)
    elseif Meta.isexpr(a, :(::)) && length(a.args) == 1
        return _Arg(gensym(:arg), false, a.args[1], default, hasdefault, vararg, nospec)
    end
    return nothing
end

_where_name(@nospecialize(w)) = w isa Symbol ? w : Meta.isexpr(w, :<:) || Meta.isexpr(w, :>:) ? w.args[1] :
    Meta.isexpr(w, :comparison) ? w.args[3] : w
_where_bound(@nospecialize(w)) = Meta.isexpr(w, :<:) ? w.args[2] : Meta.isexpr(w, :comparison) ? w.args[5] : nothing

# the value a type expression's head names in `mod`, where it is a name or a module path; else nothing
function _head_value(mod::Module, @nospecialize(h), wnames)
    (h isa Symbol && !(h in wnames)) || (Meta.isexpr(h, :.) && h.args[1] isa Symbol && !(h.args[1] in wnames)) ||
        h isa GlobalRef || return nothing
    try
        return Core.eval(mod, h)
    catch
        return nothing
    end
end

# The trait an argument's type names, as the box's type parameter, where it erases by default and the box can
# be formed there: `(X, via)` with `via` the `where` variable that types the argument, or nothing.
function _erasing_trait(mod::Module, @nospecialize(T), wheres::Vector{Any})
    wnames = Any[_where_name(w) for w in wheres]
    via = nothing
    if T isa Symbol && T in wnames
        via = T
        T = _where_bound(wheres[findfirst(==(T), wnames)])
        T === nothing && return nothing
    end
    _box_formable(mod, T, wnames) || return nothing
    return (T, via)
end

# whether `T` names a trait (or an intersection) that erases, with every parameter given (`X`, `X{A, B}`,
# `All{X{A}, Y}`): a parameter `<: B` or a parametric trait written bare leaves the instance open
function _box_formable(mod::Module, @nospecialize(T), wnames)
    h = Meta.isexpr(T, :curly) ? T.args[1] : T
    v = _head_value(mod, h, wnames)
    v isa Type || return false
    if v === Core.All
        Meta.isexpr(T, :curly) || return false
        comps = T.args[2:end]
        any(c -> _box_formable(mod, c, wnames), comps) || return false
        return all(c -> _params_given(mod, c, wnames), comps)
    end
    erases(v) || return false
    return _params_given(mod, T, wnames)
end
function _params_given(mod::Module, @nospecialize(T), wnames)
    h = Meta.isexpr(T, :curly) ? T.args[1] : T
    v = _head_value(mod, h, wnames)
    v isa Type || return false
    n = v isa UnionAll ? length(Base.unwrap_unionall(v).parameters) : 0
    given = Meta.isexpr(T, :curly) ? T.args[2:end] : Any[]
    length(given) == n || return false
    return !any(p -> Meta.isexpr(p, :<:) || Meta.isexpr(p, :>:), given)
end

_kept_forms(@nospecialize(X)) = Expr(:curly, GlobalRef(Core, :Union),
    Expr(:curly, _g(:Dynamic), Expr(:<:, X)), Expr(:curly, _g(:Compiled), Expr(:<:, X)))

_mentions_any(@nospecialize(ex), names) = any(n -> _mentions(ex, n), names)

function _erasing_def(mod::Module, src::LineNumberNode, @nospecialize(ex), d)
    callee = d.call.args[1]
    rest = d.call.args[2:end]
    params = filter(a -> Meta.isexpr(a, :parameters), rest)
    pos = filter(a -> !Meta.isexpr(a, :parameters), rest)
    args = _Arg[]
    for a in pos
        p = _parse_arg(a)
        p === nothing && return ex                       # a form this macro does not read: unchanged
        push!(args, p)
    end
    erasing = Any[]                                      # per argument: (X, via) or nothing
    for a in args
        push!(erasing, (a.type === nothing || a.vararg) ? nothing : _erasing_trait(mod, a.type, d.wheres))
    end
    all(isnothing, erasing) && return ex
    # the method at the kept forms: an argument's type, or the bound of the `where` variable that types it
    wheres = copy(d.wheres)
    newpos = Any[]
    for (i, a) in enumerate(pos)
        e = erasing[i]
        if e === nothing || e[2] !== nothing
            push!(newpos, a)
        else
            push!(newpos, _retype_arg(a, _kept_forms(e[1])))
        end
    end
    for e in erasing
        (e === nothing || e[2] === nothing) && continue
        k = findfirst(w -> _where_name(w) === e[2], wheres)
        wheres[k] = Expr(:<:, e[2], _kept_forms(e[1]))
    end
    kept = _rebuild(ex, Expr(:call, callee, params..., newpos...), d.rtype, wheres)
    # the forwarder, one per positional arity that holds an erasing argument
    fwds = Any[]
    fname = callee
    fcallee = callee
    if Meta.isexpr(callee, :(::)) && length(callee.args) == 1          # `(::Type{T})(…)`: named for the call
        fname = gensym(:self)
        fcallee = Expr(:(::), fname, callee.args[1])
    elseif Meta.isexpr(callee, :(::))
        fname = callee.args[1]
    end
    nreq = count(a -> !a.hasdefault && !a.vararg, args)
    hasva = !isempty(args) && args[end].vararg
    nfix = hasva ? length(args) - 1 : length(args)
    kws = isempty(params) ? nothing : gensym(:kws)
    nerase = count(!isnothing, erasing)
    for n in nreq:nfix
        idx = Int[i for i in 1:n]
        hasva && n == nfix && push!(idx, length(args))
        any(i -> erasing[i] !== nothing, idx) || continue
        fargs, cargs, types = Any[], Any[], Any[]
        for i in idx
            a = args[i]
            nm = a.name
            ty = a.type
            ty === nothing || push!(types, ty)
            fa = ty === nothing ? nm : Expr(:(::), nm, ty)
            if a.vararg
                push!(fargs, Expr(:..., fa)); push!(cargs, Expr(:..., nm))
            elseif erasing[i] !== nothing
                X = erasing[i][1]
                push!(fargs, Expr(:macrocall, GlobalRef(Base, Symbol("@nospecialize")), src, fa))
                push!(cargs, nerase == 1 ? Expr(:call, Expr(:curly, _g(:Dynamic), X), nm) :
                                           Expr(:call, _g(:_box_plain), X, nm))
            else
                push!(fargs, fa); push!(cargs, nm)
            end
        end
        fsig = Expr(:call, fcallee, (kws === nothing ? () : (Expr(:parameters, Expr(:..., kws)),))..., fargs...)
        fcall = Expr(:call, fname, (kws === nothing ? () : (Expr(:parameters, Expr(:..., kws)),))..., cargs...)
        # the `where` variables this arity's types name, with the variables their bounds name
        used = Any[]
        for w in reverse(d.wheres)
            nm = _where_name(w)
            if _mentions_any(Expr(:block, types...), (nm,)) || any(u -> _mentions(u, nm), used)
                pushfirst!(used, w)
            end
        end
        body = Expr(:block, src, Expr(:meta, :bounded, false), Expr(:meta, :erasing_forwarder), fcall)
        sig = isempty(used) ? fsig : Expr(:where, fsig, used...)
        push!(fwds, Expr(:function, sig, body))
    end
    # the method at the kept forms first: a definition that waits for this name (a `bounded` method that calls it) is
    # read again with it in place
    return Expr(:block, src, Expr(:macrocall, GlobalRef(Core, Symbol("@__doc__")), src, kept), fwds..., nothing)
end

# a positional argument as written, with its type replaced
function _retype_arg(@nospecialize(a), @nospecialize(T))
    if Meta.isexpr(a, :macrocall)
        b = copy(a); b.args[end] = _retype_arg(a.args[end], T); return b
    elseif Meta.isexpr(a, :kw)
        return Expr(:kw, _retype_arg(a.args[1], T), a.args[2])
    elseif Meta.isexpr(a, :(::)) && length(a.args) == 2
        return Expr(:(::), a.args[1], T)
    elseif Meta.isexpr(a, :(::))
        return Expr(:(::), T)
    end
    return a
end

function _rebuild(@nospecialize(ex), call::Expr, @nospecialize(rtype), wheres::Vector{Any})
    sig = rtype === nothing ? call : Expr(:(::), call, rtype)
    isempty(wheres) || (sig = Expr(:where, sig, wheres...))
    return Expr(ex.head, sig, ex.args[2])
end

"whether `m` is a forwarder `@erasing` made"
function _is_forwarder(m::Method)
    src = try Base.uncompressed_ast(m) catch; return false end
    for st in src.code
        Meta.isexpr(st, :meta) && length(st.args) == 1 && st.args[1] === :erasing_forwarder && return true
    end
    return false
end
