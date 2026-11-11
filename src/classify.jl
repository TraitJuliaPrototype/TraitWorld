# The classification of methods at traits (traits §7.3; compiler §6.7). A method is fully bounded
# at an argument typed by a trait when its body reaches the argument only through the contract;
# any other use makes it open there. The library infers the method at its own signature with the
# compiler's check interpreter, whose hook records each call that takes a value typed by a trait
# outside the contract, with its line; inference continues past it (compiler §6.7, C-40).

const CC = Core.Compiler

"A use of a value typed by a trait outside the contract: what was called, where, at which trait."
struct TraitUse
    what::String
    method::Method
    line::Int
    trait::Any
end

# The record of one check: the uses found, the calls that reach no method yet (decided once one is
# defined, compiler §6.7), the module whose functions are followed, the method classified (its own
# uses always count), the traits of its trait arguments (a value of another trait is not tracked).
struct ClassifyState
    uses::Vector{TraitUse}
    pending::Vector{TraitUse}
    waits_for::Vector{Symbol}        # the names whose definition decides the pending calls
    mod::Module
    method::Union{Nothing,Method}
    traits::Vector{Any}
end

# The compiler's interpreter of the definition-time check (compiler §6.7): Julia's inference with an
# ephemeral cache, so that every function the method reaches is inferred again, calling `_check_hook`
# at each known call. The library defines no method of the compiler's functions, so loading it
# invalidates none of the compiler's code (C-40, E-281).
const ClassifyInterp = CC.DefinitionCheckInterpreter
_state(interp::ClassifyInterp) = interp.state::ClassifyState
_check_hook(interp::ClassifyInterp, @nospecialize(f), argtypes::Vector{Any}, sv::CC.AbsIntState) =
    (_record_use!(interp, f, argtypes, sv); nothing)
_classify_interp(mod::Module; world::UInt = Base.get_world_counter(), method::Union{Nothing,Method} = nothing) =
    CC.DefinitionCheckInterpreter(world, _check_hook,
                                  ClassifyState(TraitUse[], TraitUse[], Symbol[], mod, method, method === nothing ? Any[] : _argument_traits(method)))

# the trait a value of type T is known by: a trait instance or an intersection, not a concrete member
function _trait_of(@nospecialize(T))
    T isa Core.TypeofVararg && (T = Base.unwrapva(T))   # a splatted call's tail: its element's type
    T = CC.widenconst(T)
    (isconcretetype(T) || !(T isa Type)) && return nothing
    u = Base.unwrap_unionall(T)
    u isa DataType || return nothing
    (istrait(u) || u.name === Base.unwrap_unionall(Core.All).name) || return nothing
    return T
end

# whether the call stores the argument `k` (known by the trait `X`) in a slot typed by `X` or a
# supertype: a field (`setproperty!`, `setfield!`), an element (`push!`, `pushfirst!`, `setindex!`)
function _stores_in_slot(@nospecialize(f), argtypes::Vector{Any}, k::Int, @nospecialize(X))
    if (f === setproperty! || f === setfield!) && k == 4 && length(argtypes) >= 4
        T = CC.widenconst(argtypes[2])
        name = argtypes[3]
        (name isa CC.Const && (name.val isa Symbol || name.val isa Int) && T isa DataType && isconcretetype(T)) || return false
        Base.fieldindex(T, name.val, false) == 0 && return false
        return X <: fieldtype(T, name.val)
    elseif (f === push! || f === pushfirst!) && k >= 3
        V = CC.widenconst(argtypes[2])
        return V <: AbstractArray && X <: eltype(V)
    elseif f === setindex! && k == 3
        V = CC.widenconst(argtypes[2])
        return V <: AbstractArray && X <: eltype(V)
    end
    return false
end

# the type an argument of type `Type{…}` names, or its upper bound where it is `Type{<:Y}`; else nothing
function _type_bound(@nospecialize(t))
    t isa CC.Const && return t.val isa Type ? t.val : nothing
    w = CC.widenconst(t)
    u = Base.unwrap_unionall(w)
    (u isa DataType && u.name === Type.body.name) || return nothing
    a = u.parameters[1]
    a isa TypeVar && return a.ub
    return a isa Type ? a : nothing
end

# whether `f` is a function of `Self` that an equation of the trait `X` or a supertrait names,
# `P = f(Self)`
function _equation_function(@nospecialize(X), @nospecialize(f))
    for (c, _) in _contracts_of(X), (_, e) in c.equations
        (Meta.isexpr(e, :call) && length(e.args) == 2 && e.args[2] === :Self) || continue
        g = try
            Core.eval(c.mod, e.args[1])
        catch
            nothing
        end
        g === f && return true
    end
    return false
end

# whether the call of `f` at `argtypes` stays in the contract of the traits its arguments are known by
function _in_contract(interp::ClassifyInterp, @nospecialize(f), argtypes::Vector{Any}, k::Int, @nospecialize(X))
    # a splat of values known by a trait: not a call of the contract's (traits §7.3)
    any(a -> a isa Core.TypeofVararg, argtypes) && return false
    atype = CC.argtypes_to_type(argtypes)
    # an operation of the trait or a supertrait, or a declared field: the compiler's rule
    CC.declared_operation_result(interp, argtypes, atype) === nothing || return true
    # a call with cast arguments (traits §7.6): the call it makes
    if f === Core.attributed_call && length(argtypes) >= 3 && k >= 4
        g = CC.singleton_type(CC.widenconst(argtypes[3]))
        g === nothing && return false
        return _in_contract(interp, g, argtypes[3:end], k - 2, X)
    end
    # a struct's constructor storing it in a field typed by the trait or a supertype (traits §7.3): its `convert`
    # and `isa` against the field's type, which the struct's parameters make `Type{<:Y}` here
    if (f === convert && k == 3) || (f === isa && k == 2)
        Y = _type_bound(argtypes[f === convert ? 2 : 3])
        Y !== nothing && istrait(Base.unwrap_unionall(Y)) && X <: Y && return true
    end
    # writing a declared field (traits §7.3): `t.name = v` at a field the trait or a supertrait declares writable
    if f === setproperty! && k == 2 && length(argtypes) == 4
        name = argtypes[3]
        if name isa CC.Const && name.val isa Symbol
            for (c, _) in _contracts_of(X), fd in c.fields
                fd.name === name.val && !fd.isconst && return true
            end
        end
    end
    # a keyword method's sorter reporting an unknown keyword (lowering's `kwerr`): an error, no use
    f === Base.kwerr && return true
    # keeping it with its attribute (traits §7.8), or a cast's unwrapping of a `Dynamic{X}`
    (f === Core.keep || f === Core._cast_compiled) && return true
    # storing it in a slot typed by the trait or a supertype (traits §7.3): a field, or an element of a
    # container
    _stores_in_slot(f, argtypes, k, X) && return true
    # a function of `Self` that one of the trait's equations names, called on it: `eltype(t)` where
    # the trait defines `T = eltype(Self)` (traits §7.3); its value is the member's
    k == 2 && length(argtypes) == 2 && _equation_function(X, f) && return true
    if f isa Core.Builtin
        # `===` and `isa` against the trait or a supertrait; asserting it to such a type
        f === (===) && return true
        if (f === isa || f === typeassert) && length(argtypes) == 3
            t = argtypes[3]
            if t isa CC.Const && t.val isa Type
                return X <: t.val
            end
        end
        return false
    end
    # wrapping it as Dynamic{X}(t)
    f isa Type && Base.unwrap_unionall(f) isa DataType && Base.unwrap_unionall(f).name === Dynamic.body.name && return true
    # passing it on: every method the call reaches takes it as a trait the value is known by, or is
    # an unannotated function of the same module (followed: its own uses are recorded)
    ms = Base._methods_by_ftype(atype, -1, interp.world)
    ms isa Vector || return false
    isempty(ms) && return false
    for match in ms
        m = (match::Core.MethodMatch).method
        sig = Base.unwrap_unionall(m.sig)::DataType
        p = k <= length(sig.parameters) ? sig.parameters[k] : sig.parameters[end]
        p isa Core.TypeofVararg && (p = p.T)
        p isa TypeVar && (p = p.ub)
        pu = Base.unwrap_unionall(p)
        # the parameter with the callee's own variables bound (`getter(ip::IndexProvider{I}, …) where {I}`)
        if pu isa DataType && istrait(pu) && X <: Base.rewrap_unionall(p, m.sig)
            continue
        end
        p === Any && m.module === _state(interp).mod && continue
        return false
    end
    return true
end

function _record_use!(interp::ClassifyInterp, @nospecialize(f), argtypes::Vector{Any}, sv::CC.AbsIntState)
    sv isa CC.InferenceState || return nothing
    # uses count in the method and the functions of its module it is followed into; a call into
    # another module is judged where it is made (traits §7.3)
    d = sv.linfo.def
    (d isa Method && d.module === _state(interp).mod) || return nothing
    # a function marked `@open` is open on purpose: its uses are its own, not its callers' (traits §7.3)
    d !== _state(interp).method && _bounded_option(d) === false && return nothing
    # a trait's own method for an operation is the contract itself (its forwarding, its default)
    _is_trait_method(d) && return nothing
    for k in 2:length(argtypes)
        X = _trait_of(argtypes[k])
        X === nothing && continue
        # the classification is per trait argument (traits §7.3): a value typed by an unrelated trait (a
        # field of a plain struct, another operation's result) is not one of them
        _related(interp, X) || continue
        _in_contract(interp, f, argtypes, k, X) && continue
        m = sv.linfo.def
        m isa Method || return nothing
        u = TraitUse(_describe(f, argtypes), m, _line(sv, m), X)
        # a call that reaches no method yet is decided once one is defined (compiler §6.7): a default
        # argument's method, which Julia defines before the method it calls
        pending = _reaches_no_method(interp, f, argtypes)
        pending && push!(_state(interp).waits_for, _name_of(f))
        list = pending ? _state(interp).pending : _state(interp).uses
        # constant propagation infers a call again: each use once
        _has_use(list, u) || push!(list, u)
        return nothing
    end
    return nothing
end

# the name a definition of `f`'s methods carries; `:*` where it has none (any definition decides)
function _name_of(@nospecialize(f))
    f isa Function && return nameof(f)
    f isa Type && Base.unwrap_unionall(f) isa DataType && return nameof(Base.unwrap_unionall(f))
    return :*
end

function _has_use(list::Vector{TraitUse}, u::TraitUse)
    for v in list
        v.what == u.what && v.method === u.method && v.line == u.line && return true
    end
    return false
end

# whether a call of a generic function reaches no method in the check's world
function _reaches_no_method(interp::ClassifyInterp, @nospecialize(f), argtypes::Vector{Any})
    f isa Core.Builtin && return false
    for a in argtypes
        a isa Core.TypeofVararg && return false
    end
    ms = Base._methods_by_ftype(CC.argtypes_to_type(argtypes), -1, interp.world)
    return ms isa Vector && isempty(ms)
end

function _describe(@nospecialize(f), argtypes::Vector{Any})
    # lowering's capture of a variable in a closure (a generator, a comprehension, `x -> …`)
    f === Core._typeof_captured_variable && length(argtypes) == 2 &&
        return string("a closure capturing a ", CC.widenconst(argtypes[2]))
    # a call with keywords as written, `g(args…; name::T, …)`, not lowering's `kwcall`
    if f === Core.kwcall && length(argtypes) >= 3
        g = CC.singleton_type(CC.widenconst(argtypes[3]))
        NT = CC.widenconst(argtypes[2])
        if g !== nothing && NT <: NamedTuple && isconcretetype(NT)
            kws = join(["$n::$T" for (n, T) in zip(fieldnames(NT), fieldtypes(NT))], ", ")
            pos = join([string(CC.widenconst(a)) for a in argtypes[4:end]], ", ")
            return string(_describe_name(g), "(", pos, "; ", kws, ")")
        end
    end
    # a field read or written, by its name
    if (f === getproperty || f === getfield || f === setproperty!) && length(argtypes) >= 3 &&
       argtypes[3] isa Core.Const && argtypes[3].val isa Symbol
        return string("the field `", argtypes[3].val, "` of a ", CC.widenconst(argtypes[2]),
                      f === setproperty! ? " (written)" : "")
    end
    return string(_describe_name(f), "(", join([string(CC.widenconst(a)) for a in argtypes[2:end]], ", "), ")")
end
_describe_name(@nospecialize(f)) = f isa Function ? string(nameof(f)) : string(f)

function _line(sv::CC.InferenceState, m::Method)
    try
        nodes = Base.IRShow.buildLineInfoNode(sv.src.debuginfo, nothing, sv.currpc)
        isempty(nodes) || return Int(last(nodes).line)
    catch
    end
    return Int(m.line)
end

"""
    classify(m::Method) -> Vector{TraitUse}

The uses outside the contract of the values typed by a trait in `m`'s body and the unannotated
functions of its module it passes them to: empty where `m` is fully bounded at its trait
arguments (traits §7.3). A call that reaches no method counts, as at the end of `m`'s module.
"""
function classify(m::Method; world::UInt = Base.get_world_counter())
    st = _classify(m; world)
    return vcat(st.uses, st.pending)
end

# the check's record: the uses decided now, and the calls that reach no method yet
function _classify(m::Method; world::UInt = Base.get_world_counter())
    interp = _classify_interp(m.module; world, method = m)
    st = _state(interp)
    sig = m.sig
    tv = Any[]
    s = sig
    while s isa UnionAll
        push!(tv, s.var)
        s = s.body
    end
    CC.typeinf_frame(interp, m, sig, Core.svec(tv...), false)
    _names_undefined!(st.waits_for, m)
    return (uses = st.uses, pending = st.pending, waits_for = st.waits_for)
end

# the globals of its module that `m`'s body names and that are not yet defined: functions defined
# later, which inference cannot follow now (compiler §6.7)
function _names_undefined!(out::Vector{Symbol}, m::Method)
    src = try Base.uncompressed_ast(m) catch; return out end
    for stmt in src.code
        _names_undefined!(out, m.module, stmt)
    end
    return out
end
function _names_undefined!(out::Vector{Symbol}, M::Module, @nospecialize(x))
    if x isa GlobalRef
        x.mod === M && !isdefined(M, x.name) && !(x.name in out) && push!(out, x.name)
    elseif x isa Expr
        for a in x.args
            _names_undefined!(out, M, a)
        end
    end
    return out
end

# the bare traits of a method's trait arguments (each component of an intersection)
function _argument_traits(m::Method)
    out = Any[]
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return out
    for p in sig.parameters[2:end]
        Base.isvarargtype(p) && (p = Base.unwrapva(p))
        X = _trait_of(p isa TypeVar ? p.ub : p)
        X === nothing && continue
        for c in _components(X)
            push!(out, bare(c))
        end
    end
    return out
end
_components(@nospecialize(X)) = (u = Base.unwrap_unionall(X); u isa DataType && u.name === Base.unwrap_unionall(Core.All).name ?
    Any[c for c in (u.parameters[1]::DataType).parameters] : Any[X])
# whether a value known by the trait `X` may be one of the classified method's trait arguments
function _related(interp::ClassifyInterp, @nospecialize(X))
    _state(interp).method === nothing && return true
    for c in _components(X), A in _state(interp).traits
        b = bare(c)
        (b <: A || A <: b) && return true
    end
    return false
end

# whether a method is at a trait argument, and the option its body states (`@bounded`, `@open`). A
# trait's own method for an operation is the contract itself, and is not classified.
function _trait_arguments(m::Method)
    _is_trait_method(m) && return false
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return false
    for p in sig.parameters[2:end]
        Base.isvarargtype(p) && (p = Base.unwrapva(p))      # a varargs tail: its element type
        _trait_of(p isa TypeVar ? p.ub : p) === nothing || return true
    end
    return false
end
# whether `bounded` refuses `m` where it is open: its own `@bounded` or `@open`, else its module's
# option (`@trait_module`, traits §13)
function _bounded(m::Method)
    o = _bounded_option(m)
    o === nothing || return o
    return (ccall(:jl_get_module_trait_options, Cint, (Any,), m.module) & 1) != 0
end
function _bounded_option(m::Method)
    src = try Base.uncompressed_ast(m) catch; return nothing end
    for st in src.code
        if Meta.isexpr(st, :meta) && length(st.args) == 2 && st.args[1] === :bounded
            return st.args[2]::Bool
        end
    end
    return nothing
end

"""
    check_definitions(M::Module) -> Vector{String}

The methods of `M` at trait arguments that are open, each with its uses outside the contract
(traits §11.2); empty where every one is fully bounded. Methods marked `@open` are skipped.
"""
function check_definitions(M::Module)
    problems = String[]
    for name in names(M; all = true)
        isdefined(M, name) || continue
        f = try getglobal(M, name) catch; continue end
        f isa Function || continue
        for m in methods(f)
            m.module === M || continue
            _trait_arguments(m) || continue
            _bounded_option(m) === false && continue
            for u in classify(m)
                push!(problems, "$(m.name) at $(m.file):$(u.line): $(u.what) is not in the contract of $(u.trait)")
            end
        end
    end
    return problems
end

"""
    @bounded f(…) = …

The method must be fully bounded at its trait arguments: an open one is refused with
`TraitUseError` where it is defined (traits §7.3, §13).
"""
macro bounded(ex)
    return esc(_mark_bounded(ex, true))
end

"""
    @open f(…) = …

The method is open on purpose: `bounded` does not refuse it (traits §7.3).
"""
macro open(ex)
    return esc(_mark_bounded(ex, false))
end

function _mark_bounded(ex, on::Bool)
    (Meta.isexpr(ex, :(=)) || Meta.isexpr(ex, :function)) || error("@bounded and @open take a method definition")
    body = ex.args[2]
    body = Meta.isexpr(body, :block) ? body : Expr(:block, body)
    pushfirst!(body.args, Expr(:meta, :bounded, on))
    return Expr(ex.head, ex.args[1], body)
end

# Under `@bounded`, an open method is refused where it is defined (the definition hook, once the
# method is visible, so that inference can follow it). A method whose only questionable calls reach
# no method yet waits: a definition of a name it waits for classifies it again, and its module's end
# a last time (compiler §6.7).
const _PENDING_BOUNDED = Tuple{Method, Vector{Symbol}}[]

function _check_bounded(m::Method)
    _check_pending_bounded(m.module, m.name)
    _trait_arguments(m) || return nothing
    _bounded(m) || return nothing
    return _decide_bounded(m)
end

# classifies `m` now: refuses it where a use is outside the contract, keeps it waiting where a call
# reaches no method yet. At its module's end (`final`) a call that still reaches no method counts.
function _decide_bounded(m::Method; final::Bool = false)
    st = _classify(m)
    uses = final ? vcat(st.uses, st.pending) : st.uses
    if isempty(uses)
        final || isempty(st.waits_for) || push!(_PENDING_BOUNDED, (m, st.waits_for))
        return nothing
    end
    # the refused method goes; while an image is built a method cannot be deleted, and the error
    # fails the build
    ccall(:jl_generating_output, Cint, ()) == 0 && Base.delete_method(m)
    lines = ["$(u.what) at line $(u.line) is not in the contract of $(u.trait)" for u in uses]
    throw(TraitUseError("$(m.name) is declared bounded, and is open:\n  " * join(lines, "\n  ")))
end

# the module's end (the module-end hook): its waiting methods are classified a last time
function _end_pending_bounded(M::Module)
    isempty(_PENDING_BOUNDED) && return nothing
    waiting = Method[w for (w, _) in _PENDING_BOUNDED if w.module === M]
    isempty(waiting) && return nothing
    filter!(e -> e[1].module !== M, _PENDING_BOUNDED)
    for w in waiting
        _decide_bounded(w; final = true)
    end
    return nothing
end

# the waiting methods of the module `M` that wait for `name`, classified again at its definition
function _check_pending_bounded(M::Module, name::Symbol)
    isempty(_PENDING_BOUNDED) && return nothing
    waiting = Method[]
    i = 1
    while i <= length(_PENDING_BOUNDED)
        (w, names) = _PENDING_BOUNDED[i]
        if w.module === M && (name in names || :* in names)
            push!(waiting, w)
            deleteat!(_PENDING_BOUNDED, i)
        else
            i += 1
        end
    end
    for w in waiting
        _decide_bounded(w)
    end
    return nothing
end
