# A trait's default as methods made where a method is defined (W-160; D-1; traits §7, lowering §5,
# compiler §10.1).
#
# For a trait that erases by default (`@default_dynamic`, and `Callable`, whose default is Julia's), one method
# definition `f(t::X, …)` makes two methods, as a positional default makes a second one: the method as written
# at the two kept forms, `Union{Dynamic{<:X}, Compiled{<:X}}`, and a forwarder at the signature as written,
# which takes a plain member and passes `Dynamic{X}(t)` on. The runtime asks the library at each method
# definition whose signature names a set (the expansion hook, compiler §10.1), before the method is made: whether
# an argument erases is known only once the signature's types exist. Dispatch and the runtime do not change: the
# kept-form method is more specific than the forwarder, so a box and a wrapper reach the method as they are, and a
# plain member reaches it boxed. A trait without the default takes a plain member as it is (Julia's rule).
#
# The forwarder is Julia's `@nospecialize` method at the trait: compiled once, its argument at the declared type
# `X`, so the box's field test holds by the declared type and the box is made with no test and no heap of its own.
# Where a caller that knows the member's type inlines it, the test holds through the membership's entry, which
# inference records (compiler §4.8). Where the trait's parameters are the method's variables (`X{T}`), the
# forwarder is compiled per member type (`@specialize`), so that the box's parameters are known.

"""
    erases(X) -> Bool

Whether a plain member passed at an argument typed by `X` is boxed by the forwarder that the method's definition
makes: `X` is a trait that declares `@default_dynamic`, or `Callable` (its default is `Dynamic`), or an
intersection with such a component.
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

# The forwarder's box. The forwarder's own signature has matched the argument at the trait, so the box is made by
# `new`, with no constructor: its field test holds by the argument's declared type, or, where a caller inlines the
# forwarder, through the membership's entry, which inference records. A kept form reaches a forwarder only where
# the kept-form method could not take it (a wrapper of a function without a method at a `Callable`'s signature, a
# member of every `Callable` by its own call method): the constructor decides then, and refuses it.
@inline _box(::Type{D}, @nospecialize(x)) where {D<:Dynamic} = x isa Union{Dynamic, Compiled} ? D(x) : _new_box(D, x)
@eval @inline _new_box(::Type{D}, @nospecialize(x)) where {D<:Dynamic} = $(Expr(:new, :D, :x))
# a kept form passes as it is; a plain member is boxed at the trait (a forwarder of several trait arguments)
@inline _box_plain(::Type{D}, @nospecialize(x)) where {D<:Dynamic} = x isa Union{Dynamic, Compiled} ? x : _new_box(D, x)

# a trait's own method reads its receiver through `_fwd` (lowering §2); no other method does
_code_names_fwd(src::Core.CodeInfo) = any(_names_fwd, src.code)
_names_fwd(@nospecialize(a)) = (a isa GlobalRef && a.mod === TraitWorld && a.name === :_fwd) ||
                               (a isa Expr && any(_names_fwd, a.args))

"whether `m` is a forwarder that a method's definition made"
function _is_forwarder(m::Method)
    src = try Base.uncompressed_ast(m) catch; return false end
    return _has_forwarder_meta(src)
end
_has_forwarder_meta(src::Core.CodeInfo) = _has_meta(src, :erasing_forwarder)
function _has_meta(src::Core.CodeInfo, name::Symbol)
    for st in src.code
        Meta.isexpr(st, :meta) && length(st.args) == 1 && st.args[1] === name && return true
    end
    return false
end

# The trait a declared argument type erases at, where the box can be formed there: every parameter given (`X`,
# `X{A, B}`, `X{T}` with `T` the method's variable, `All{X{A}, Y}`); a trait written bare or with a `<:`
# parameter (`Column`, `Column{<:Real}`) leaves the instance open, and the argument takes a plain member as it is.
function _erasing_trait(@nospecialize(T))
    T isa DataType || return nothing
    erases(T) || return nothing
    return T
end

_kept_forms(@nospecialize(X)) = Union{Dynamic{<:X}, Compiled{<:X}}

# `t` with the variable `v` replaced by `x`
function _subst(@nospecialize(t), v::TypeVar, @nospecialize(x))
    t === v && return x
    (t isa Type || t isa TypeVar) && any(w -> w === v, _free_vars(t)) || return t
    return (UnionAll(v, t)){x}
end
function _subst_vararg(@nospecialize(t), v::TypeVar, @nospecialize(x))
    t isa Core.TypeofVararg || return _subst(t, v, x)
    T = isdefined(t, :T) ? _subst(t.T, v, x) : Any
    return isdefined(t, :N) ? Vararg{T, t.N isa TypeVar ? _subst(t.N, v, x) : t.N} : Vararg{T}
end

"""
    _expand_definition(argdata, code, mod) -> nothing or svec of (argdata, code) pairs

The expansion hook (compiler §10.1): for a definition whose signature has an argument at a trait that erases by
default, the method as written at the kept forms, then the forwarder at the signature as written. `nothing`
otherwise, and for a forwarder's own definition.
"""
function _expand_definition(argdata::Core.SimpleVector, code::Core.CodeInfo, mod::Module)
    atypes = argdata[1]::Core.SimpleVector
    tvars = argdata[2]::Core.SimpleVector
    loc = argdata[3]
    _has_forwarder_meta(code) && return nothing
    _has_meta(code, :no_forwarder) && return nothing   # a method `@trait` makes (a default, lowering §2)
    _code_names_fwd(code) && return nothing             # likewise, a trait's method of an image made before the meta
    n = length(atypes)
    pos = Int[]                       # the erasing arguments
    traits = Any[]                    # the trait each erases at
    vias = Any[]                      # the `where` variable that types it, or nothing
    for i in 2:n
        T = atypes[i]
        T isa Core.TypeofVararg && continue
        via = nothing
        if T isa TypeVar && any(v -> v === T, tvars)
            via = T
            T = T.ub
        end
        X = _erasing_trait(T)
        X === nothing && continue
        _box_formable(X, i, via, atypes) || continue
        push!(pos, i); push!(traits, X); push!(vias, via)
    end
    isempty(pos) && return nothing
    # the method as written, at the kept forms: an argument's type, or a `where` variable's bound
    katypes = Any[atypes...]
    ktvars = Any[tvars...]
    for (k, i) in enumerate(pos)
        v = vias[k]
        if v === nothing
            katypes[i] = _kept_forms(traits[k])
        else
            v = v::TypeVar
            nv = TypeVar(v.name, v.lb, _kept_forms(traits[k]))
            for j in 1:n
                katypes[j] = _subst_vararg(katypes[j], v, nv)
            end
            for j in eachindex(ktvars)
                w = ktvars[j]::TypeVar
                if w === v
                    ktvars[j] = nv
                elseif Base.has_free_typevars(w.ub) || Base.has_free_typevars(w.lb)
                    ktvars[j] = TypeVar(w.name, _subst(w.lb, v, nv), _subst(w.ub, v, nv))
                end
            end
        end
    end
    kept = Core.svec(Core.svec(katypes...), Core.svec(ktvars...), loc)
    fwd = _forwarder_code(atypes, tvars, loc, code, pos, traits, mod)
    fwd === nothing && return nothing
    return Core.svec(Core.svec(kept, code), Core.svec(argdata, fwd))
end

# Whether the box `Dynamic{X}` can be formed at argument `i` once a call's types are known. A variable of `X` is
# bound by dispatch: by another argument, or by the member's own membership (`X{T}` at a member of `X{Int}`); not
# for a component `Callable{A, S}`, which a function's type does not fix, so its variables must be bound by another
# argument. A `where` variable that types the argument must occur nowhere else (a struct's constructor
# `T{F}(f::F)`): the call fixes it to the member's type, which the box is not.
function _box_formable(@nospecialize(X), i::Int, @nospecialize(via), atypes)
    others = TypeVar[]
    for j in 2:length(atypes)
        j == i && continue
        _collect_vars_deep!(others, atypes[j])
    end
    _collect_vars_deep!(others, atypes[1])
    via isa TypeVar && any(v -> v === via, others) && return false
    for C in _components(X)      # classify.jl
        _is_callable(C) || continue
        for v in _free_vars(C)
            any(w -> w === v, others) || return false
        end
    end
    via isa TypeVar && any(v -> v === via, _free_vars(X)) && return false
    return true
end
_is_callable(@nospecialize(C)) = (u = Base.unwrap_unionall(C); u isa DataType && u.name === Base.unwrap_unionall(Core.Callable).name)
# the variables of `t`, with those their bounds name
function _collect_vars_deep!(vs, @nospecialize(t))
    for v in _free_vars(t)
        any(w -> w === v, vs) && continue
        push!(vs, v)
        _collect_vars_deep!(vs, v.ub); _collect_vars_deep!(vs, v.lb)
    end
    return vs
end

function _free_vars(@nospecialize(t))
    vs = TypeVar[]
    _collect_vars!(vs, t)
    return vs
end
function _collect_vars!(vs, @nospecialize(t))
    if t isa TypeVar
        any(v -> v === t, vs) || push!(vs, t)
    elseif t isa UnionAll
        _collect_vars!(vs, t.var.lb); _collect_vars!(vs, t.var.ub); _collect_vars!(vs, t.body)
    elseif t isa Union
        _collect_vars!(vs, t.a); _collect_vars!(vs, t.b)
    elseif t isa DataType
        for p in t.parameters
            _collect_vars!(vs, p)
        end
    elseif t isa Core.TypeofVararg
        isdefined(t, :T) && _collect_vars!(vs, t.T)
        isdefined(t, :N) && _collect_vars!(vs, t.N)
    end
    return vs
end

# The forwarder's code: `return #self#(box(a2), a3, …)`, made by lowering a
# definition of the same arguments with the method's variables (so the box's type reads them as static
# parameters, in the method's order) and taking its code. The forwarder's line is the definition's.
function _forwarder_code(atypes, tvars, loc, code::Core.CodeInfo, pos, traits, mod::Module)
    n = length(atypes)
    names = Symbol[]
    for i in 2:n
        s = i <= length(code.slotnames) ? code.slotnames[i] : Symbol("#unused#")
        nm = string(s)
        push!(names, (isempty(nm) || startswith(nm, "#") || s in names) ? Symbol("#a", i) : s)
    end
    vnames = Symbol[Symbol("#sp", k) for k in 1:length(tvars)]
    single = length(pos) == 1
    fargs, cargs = Any[], Any[]
    for i in 2:n
        nm = names[i - 1]
        if atypes[i] isa Core.TypeofVararg
            push!(fargs, Expr(:..., nm)); push!(cargs, Expr(:..., nm))
            continue
        end
        k = findfirst(==(i), pos)
        if k === nothing
            push!(fargs, nm); push!(cargs, nm)
        else
            D = Dynamic{traits[k]}
            vs = TypeVar[v for v in tvars if any(w -> w === v, _free_vars(D))]
            # compiled once where the box's trait is fixed; per member type where the call's types fix it
            push!(fargs, Expr(:macrocall, GlobalRef(Base, isempty(vs) ? Symbol("@nospecialize") : Symbol("@specialize")), loc, nm))
            Dexpr = if isempty(vs)
                QuoteNode(D)
            else
                UA = D
                for v in reverse(vs)
                    UA = UnionAll(v, UA)
                end
                Expr(:call, GlobalRef(Core, :apply_type), QuoteNode(UA),
                     Any[vnames[findfirst(w -> w === v, collect(tvars))] for v in vs]...)
            end
            push!(cargs, Expr(:call, GlobalRef(TraitWorld, single ? :_box : :_box_plain), Dexpr, nm))
        end
    end
    body = Expr(:block, loc, Expr(:meta, :erasing_forwarder), Expr(:meta, :bounded, false),
                Expr(:return, Expr(:call, Symbol("#self#"), cargs...)))
    sig = Expr(:call, Symbol("#forwarder#"), fargs...)
    isempty(vnames) || (sig = Expr(:where, sig, vnames...))
    lowered = Meta.lower(mod, Expr(:function, sig, body))
    lowered isa Expr && lowered.head === :thunk || return nothing
    for st in (lowered.args[1]::Core.CodeInfo).code
        if Meta.isexpr(st, :method) && length(st.args) == 3 && st.args[3] isa Core.CodeInfo
            return st.args[3]::Core.CodeInfo
        end
    end
    return nothing
end

"""
    @erasing def

Nothing to write: a method at a trait that erases by default makes its forwarder where it is defined. Kept as the
definition itself, for code written for the prototype (W-151); it leaves with the attribute's machinery.
"""
macro erasing(ex)
    return esc(ex)
end
