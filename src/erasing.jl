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
# inference records (compiler §4.8). Where a parameter of the trait is a variable only the argument itself binds
# (`ip::IndexProvider{I}`), the forwarder is compiled per member type (`@specialize`), so that the box's
# parameters are known.

"""
    erases(X) -> Bool

Whether a plain member passed at an argument typed by `X` is boxed by the forwarder that the method's definition
makes: `X` is a trait that declares `@default_dynamic`, or `Callable` (whose erasing bit Core's build sets), or an
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
    return ccall(:jl_set_erases, Cint, (Any,), u) != 0                  # a set of Julia's own: `Callable`
end

# A box made by `new`, with no constructor (a box of a subtrait's box, `compiled.jl`): its field test holds by the
# argument's type, decided where the code is compiled (compiler §4.8). The forwarder makes its box the same way in
# its own body (`_forwarder_code`).
@eval @inline _new_box(::Type{D}, @nospecialize(x)) where {D<:Dynamic} = $(Expr(:new, :D, :x))

# A forwarder with several arguments that erase boxes each by a call of its own (compiler §6.3, §7.6), inlined where
# the forwarder is compiled for the members' types: the method at the kept forms passes one as it is; the other
# tests a function's signature (`Callable`'s, else nothing) and makes the box by `new`, so code compiled by facts
# knows the box as before. A closed build that knows an argument only by its trait branches at this call over that
# argument's own members, apart from the other arguments'.
@inline _forward_box(::Type{D}, x::Union{Dynamic, Compiled}, @nospecialize(self), args::Tuple) where {D<:Dynamic} = x
@inline _forward_box(::Type{D}, x, @nospecialize(self), args::Tuple) where {D<:Dynamic} =
    (_callable_box_check(D, x, self, args); _new_box(D, x))

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
# `X{A, B}`, `X{T}` with `T` the method's variable, `All{X{A}, Y}`). A trait written bare or with a `<:` parameter
# (`Column`, `Column{<:Real}`) is given here with its open parameters lifted into the forwarder's own variables
# (`_expand_definition`).
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
    # an argument at a trait with its parameters left open (`c::Column`, `c::Column{<:Real}`; traits §7.8): the
    # forwarder takes their variables as static parameters of its own (`c::Column{T} where T`, the same
    # signature), so that its box names the instance the member is in. The method as written keeps the type as
    # written at the kept forms. Where an open parameter is an input (`Callable`'s, `HasProperty`'s name), the member
    # does not determine it: the argument takes the plain member as it is.
    fatypes = Any[atypes...]
    ftvars = Any[tvars...]
    for i in 2:n
        T = atypes[i]
        (T isa UnionAll && _erasing_trait(Base.unwrap_unionall(T)) !== nothing && _member_fixes_open(T)) || continue
        while T isa UnionAll
            v = TypeVar(Symbol("#", T.var.name, i), T.var.lb, T.var.ub)
            push!(ftvars, v)
            T = T{v}
        end
        fatypes[i] = T
    end
    pos = Int[]                       # the erasing arguments
    traits = Any[]                    # the trait each erases at (in the forwarder's variables)
    vias = Any[]                      # the `where` variable that types it, or nothing
    for i in 2:n
        T = fatypes[i]
        T isa Core.TypeofVararg && continue
        via = nothing
        if T isa TypeVar && any(v -> v === T, tvars)
            via = T
            T = T.ub
        end
        X = _erasing_trait(T)
        X === nothing && continue
        _box_formable(X, i, via, fatypes) || continue
        push!(pos, i); push!(traits, X); push!(vias, via)
    end
    isempty(pos) && return nothing
    # the method as written, at the kept forms: an argument's type, or a `where` variable's bound
    katypes = Any[atypes...]
    ktvars = Any[tvars...]
    for (k, i) in enumerate(pos)
        v = vias[k]
        if v === nothing
            katypes[i] = _kept_forms(fatypes[i] === atypes[i] ? traits[k] : atypes[i])
        else
            # the variable as it stands now (an earlier replacement may have rebuilt it), with its bound replaced
            vi = findfirst(w -> w === v, collect(tvars))::Int
            cur = ktvars[vi]::TypeVar
            X = traits[k]
            X = foldl((t, j) -> ktvars[j] === tvars[j] ? t : _subst(t, tvars[j]::TypeVar, ktvars[j]), eachindex(ktvars); init = X)
            _replace_var!(katypes, ktvars, cur, TypeVar(cur.name, cur.lb, _kept_forms(X)))
        end
    end
    kept = Core.svec(Core.svec(katypes...), Core.svec(ktvars...), loc)
    fwd = _forwarder_code(fatypes, ftvars, loc, code, pos, traits, mod)
    fwd === nothing && return nothing
    fdata = length(ftvars) == length(tvars) ? argdata : Core.svec(Core.svec(fatypes...), Core.svec(ftvars...), loc)
    entry = _wrapper_entry(atypes, katypes, ktvars, loc, code, pos, traits, vias, fatypes, mod)
    entry === nothing && return Core.svec(Core.svec(kept, code), Core.svec(fdata, fwd))
    return Core.svec(Core.svec(kept, code), entry, Core.svec(fdata, fwd))
end

# A wrapper given at a `Callable{A, S}` argument is checked where it enters (traits §9; compiler §6.3, §7.4): a
# method at the wrapper's form of that argument, more specific than the method as written, tests the wrapper's
# function at `A` (and its result inferred there against `S`), then invokes the method as written, which is compiled
# for the wrapper's type. Made where one argument has a `Callable` component, its trait given as written, in a
# method that is not a keyword method's body; elsewhere the wrapper is not tested at entry (traits T-156).
function _wrapper_entry(atypes, katypes, ktvars, loc, code::Core.CodeInfo, pos, traits, vias, fatypes, mod::Module)
    n = length(atypes)
    (n >= 2 && atypes[1] !== typeof(Core.kwcall)) || return nothing
    ks = [k for k in eachindex(pos) if any(_is_callable, _components(traits[k]))]
    length(ks) == 1 || return nothing
    k = only(ks); i = pos[k]
    (vias[k] === nothing && fatypes[i] === atypes[i]) || return nothing
    X = traits[k]
    any(t -> t isa Core.TypeofVararg, katypes[2:end-1]) && return nothing
    Z = TypeVar(:Z, X)
    eatypes = Any[katypes...]
    eatypes[i] = UnionAll(Z, Compiled{Z})
    names = Symbol[]
    for j in 2:n
        sl = j <= length(code.slotnames) ? code.slotnames[j] : Symbol("#unused#")
        nm = string(sl)
        push!(names, (isempty(nm) || startswith(nm, "#") || sl in names) ? Symbol("#a", j) : sl)
    end
    va = katypes[end] isa Core.TypeofVararg
    fargs = Any[(va && j == n) ? Expr(:..., names[j - 1]) : names[j - 1] for j in 2:n]
    vnames = Symbol[Symbol("#sp", j) for j in 1:length(ktvars)]
    vs = TypeVar[v for v in ktvars if any(w -> w === v, _free_vars(X))]
    Xexpr = if isempty(vs)
        QuoteNode(X)
    else
        UA = X
        for v in reverse(vs)
            UA = UnionAll(v, UA)
        end
        Expr(:call, GlobalRef(Core, :apply_type), QuoteNode(UA), Any[vnames[findfirst(w -> w === v, ktvars)] for v in vs]...)
    end
    invsig = Tuple{katypes[2:end]...}
    for v in reverse(ktvars)
        any(w -> w === v, _free_vars(invsig)) && (invsig = UnionAll(v, invsig))
    end
    body = Expr(:block, loc, Expr(:meta, :erasing_forwarder), Expr(:meta, :bounded, false),
                Expr(:call, GlobalRef(TraitWorld, :_callable_entry_check), Xexpr,
                     Expr(:call, GlobalRef(Core, :getfield), names[i - 1], QuoteNode(:object)), Symbol("#self#"), Expr(:tuple, fargs...)),
                Expr(:return, Expr(:call, GlobalRef(Core, :invoke), Symbol("#self#"), QuoteNode(invsig), fargs...)))
    sig = Expr(:call, Symbol("#entry#"), fargs...)
    isempty(vnames) || (sig = Expr(:where, sig, vnames...))
    lowered = Meta.lower(mod, Expr(:function, sig, body))
    lowered isa Expr && lowered.head === :thunk || return nothing
    for st in (lowered.args[1]::Core.CodeInfo).code
        if Meta.isexpr(st, :method) && length(st.args) == 3 && st.args[3] isa Core.CodeInfo
            return Core.svec(Core.svec(Core.svec(eatypes...), Core.svec(ktvars...), loc), st.args[3]::Core.CodeInfo)
        end
    end
    return nothing
end

# Whether a member's type determines every parameter a trait's type leaves open (`Column`, `Column{<:Real}`): each
# member is in one instance of a trait but at its inputs (compiler §4.6), so an open parameter that is no input is
# fixed by the member's membership. `Callable`'s parameters are inputs: a function's type fixes none of them.
function _member_fixes_open(T::UnionAll)
    B = Base.unwrap_unionall(T)
    B isa DataType || return false
    vars = TypeVar[]
    t = T
    while t isa UnionAll
        push!(vars, t.var)
        t = t.body
    end
    ins = _input_positions(B)
    for (k, p) in enumerate(B.parameters)
        k in ins || continue
        any(v -> any(w -> w === v, _free_vars(p)), vars) && return false
    end
    return true
end
function _input_positions(B::DataType)
    _is_callable(B) && return 1:length(B.parameters)
    c = contract(B)
    c === nothing && return Int[]
    return Int[findfirst(==(s), c.params)::Int for s in c.inputs]
end

# Whether the box `Dynamic{X}` can be formed at argument `i` once a call's types are known. A variable of `X` is
# bound by dispatch: by another argument, or by the member's own membership (`X{T}` at a member of `X{Int}`); not
# for a component `Callable{A, S}`, which a function's type does not fix, so its variables must be bound by another
# argument. A `where` variable that types the argument must occur nowhere else (a struct's constructor
# `T{F}(f::F)`): the call fixes it to the member's type, which the box is not.
function _box_formable(@nospecialize(X), i::Int, @nospecialize(via), atypes)
    others = _others_vars(atypes, i)
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
# `old` replaced by `new` in the argument types and the variables' bounds; a variable whose bound names `old` is
# rebuilt, and replaced in turn
function _replace_var!(katypes::Vector{Any}, ktvars::Vector{Any}, old::TypeVar, new::TypeVar)
    for j in eachindex(katypes)
        katypes[j] = _subst_vararg(katypes[j], old, new)
    end
    for j in eachindex(ktvars)
        w = ktvars[j]::TypeVar
        if w === old
            ktvars[j] = new
        elseif any(x -> x === old, _free_vars(w.ub)) || any(x -> x === old, _free_vars(w.lb))
            _replace_var!(katypes, ktvars, w, TypeVar(w.name, _subst(w.lb, old, new), _subst(w.ub, old, new)))
        end
    end
    return nothing
end

# the variables the arguments other than `i` bind, with those their bounds name
function _others_vars(atypes, i::Int)
    others = TypeVar[]
    for j in 1:length(atypes)
        j == i && continue
        _collect_vars_deep!(others, atypes[j])
    end
    return others
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

# the free variables of `t`: those no `UnionAll` inside `t` binds
function _free_vars(@nospecialize(t))
    vs = TypeVar[]
    _collect_vars!(vs, t, TypeVar[])
    return vs
end
function _collect_vars!(vs, @nospecialize(t), bound::Vector{TypeVar})
    if t isa TypeVar
        any(v -> v === t, bound) || any(v -> v === t, vs) || push!(vs, t)
    elseif t isa UnionAll
        _collect_vars!(vs, t.var.lb, bound); _collect_vars!(vs, t.var.ub, bound)
        _collect_vars!(vs, t.body, push!(copy(bound), t.var))
    elseif t isa Union
        _collect_vars!(vs, t.a, bound); _collect_vars!(vs, t.b, bound)
    elseif t isa DataType
        for p in t.parameters
            _collect_vars!(vs, p, bound)
        end
    elseif t isa Core.TypeofVararg
        isdefined(t, :T) && _collect_vars!(vs, t.T, bound)
        isdefined(t, :N) && _collect_vars!(vs, t.N, bound)
    end
    return vs
end

# The forwarder's code: each plain argument boxed by `new`, then `return #self#(b2, a3, …)`. With one argument
# that erases, the box is made in the forwarder's own body, not by a call: compiled once, its argument is typed by
# the set, and in code compiled by facts a call whose argument is typed by the set is a run-time site, and its
# result would be unknown. A kept form reaches that forwarder only where the kept-form method could not take it (a
# wrapper of a function without a method at a `Callable`'s signature): the constructor decides then, and refuses
# it. With several, each is boxed by its own call `_forward_box(D, x, #self#, args)`, inlined where the forwarder
# is compiled per member type (a call at the member's type); a kept form passes as it is, and the call at the
# boxes dispatches it. Made by lowering a definition of the
# same arguments with the method's variables (so the box's type reads them as static parameters, in the
# method's order) and taking its code. The forwarder's line is the definition's.
#
# Compiled once (`@nospecialize`) where one argument erases and the other arguments fix its trait's parameters;
# per member type (`@specialize`) where only the member's own type fixes a parameter (`ip::IndexProvider{I}`), or
# where several arguments erase: the call with a box at each is then at concrete types.
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
    KF = QuoteNode(Union{Dynamic, Compiled})
    fargs, cargs, boxes = Any[], Any[], Any[]
    origargs = Any[atypes[i] isa Core.TypeofVararg ? Expr(:..., names[i - 1]) : names[i - 1] for i in 2:n]
    for i in 2:n
        nm = names[i - 1]
        if atypes[i] isa Core.TypeofVararg
            push!(fargs, Expr(:..., nm)); push!(cargs, Expr(:..., nm))
            continue
        end
        k = findfirst(==(i), pos)
        if k === nothing
            push!(fargs, nm); push!(cargs, nm)
            continue
        end
        D = Dynamic{traits[k]}
        vs = TypeVar[v for v in tvars if any(w -> w === v, _free_vars(D))]
        others = _others_vars(atypes, i)
        # a `Callable` argument is compiled per function: its signature's test then folds (traits §9)
        callable = any(_is_callable, _components(traits[k]))
        once = single && !callable && all(v -> any(w -> w === v, others), vs)
        push!(fargs, Expr(:macrocall, GlobalRef(Base, once ? Symbol("@nospecialize") : Symbol("@specialize")), loc, nm))
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
        Dn, bn = Symbol("#D", i), Symbol("#b", i)
        push!(boxes, Expr(:(=), Dn, Dexpr))
        if !single
            # several arguments erase: each boxed by its own call (`_forward_box`)
            push!(boxes, Expr(:(=), bn, Expr(:call, GlobalRef(TraitWorld, :_forward_box), Dn, nm, Symbol("#self#"),
                                             Expr(:tuple, origargs...))))
            push!(cargs, bn)
            continue
        end
        kept = Expr(:call, GlobalRef(Core, :typeassert), Expr(:call, Dn, nm), Dn)
        # a function boxed at `Callable{A, S}` has a method at `A`, or the call that passes it raises (traits §9)
        plain = callable ? Expr(:block, Expr(:call, GlobalRef(TraitWorld, :_callable_box_check), Dn, nm, Symbol("#self#"),
                                             Expr(:tuple, origargs...)), Expr(:new, Dn, nm)) : Expr(:new, Dn, nm)
        push!(boxes, Expr(:(=), bn, Expr(:if, Expr(:call, GlobalRef(Core, :isa), nm, KF), kept, plain)))
        push!(cargs, bn)
    end
    body = Expr(:block, loc, Expr(:meta, :erasing_forwarder), Expr(:meta, :bounded, false), boxes...,
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
