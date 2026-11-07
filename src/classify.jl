# The classification of methods at traits (traits §7.3; compiler §6.7). A method is fully bounded
# at an argument typed by a trait when its body reaches the argument only through the contract;
# any other use makes it open there. The library infers the method at its own signature with an
# interpreter of its own, which records each call that takes a value typed by a trait outside the
# contract, with its line; inference continues past it (compiler C-40: the reference puts this in
# the native interpreter, under a check flag).

const CC = Core.Compiler

"A use of a value typed by a trait outside the contract: what was called, where, at which trait."
struct TraitUse
    what::String
    method::Method
    line::Int
    trait::Any
end

struct ClassifyCache
    dict::IdDict{Core.MethodInstance,Core.CodeInstance}
end

# An interpreter of the classification: Julia's inference, with an ephemeral cache, so that every
# function the method reaches is inferred again and its uses recorded.
struct ClassifyInterp <: CC.AbstractInterpreter
    world::UInt
    inf_params::CC.InferenceParams
    opt_params::CC.OptimizationParams
    inf_cache::Vector{CC.InferenceResult}
    code_cache::ClassifyCache
    uses::Vector{TraitUse}
    mod::Module
end
ClassifyInterp(mod::Module; world::UInt = Base.get_world_counter()) =
    ClassifyInterp(world, CC.InferenceParams(), CC.OptimizationParams(), CC.InferenceResult[],
                   ClassifyCache(IdDict{Core.MethodInstance,Core.CodeInstance}()), TraitUse[], mod)
CC.InferenceParams(i::ClassifyInterp) = i.inf_params
CC.OptimizationParams(i::ClassifyInterp) = i.opt_params
CC.get_inference_world(i::ClassifyInterp) = i.world
CC.get_inference_cache(i::ClassifyInterp) = i.inf_cache
CC.cache_owner(::ClassifyInterp) = :TraitWorldClassify
CC.code_cache(i::ClassifyInterp) = CC.WorldView(i.code_cache, CC.WorldRange(i.world))
CC.get(wvc::CC.WorldView{ClassifyCache}, mi::Core.MethodInstance, default) = get(wvc.cache.dict, mi, default)
CC.getindex(wvc::CC.WorldView{ClassifyCache}, mi::Core.MethodInstance) = getindex(wvc.cache.dict, mi)
CC.haskey(wvc::CC.WorldView{ClassifyCache}, mi::Core.MethodInstance) = haskey(wvc.cache.dict, mi)
CC.setindex!(wvc::CC.WorldView{ClassifyCache}, ci::Core.CodeInstance, mi::Core.MethodInstance) = setindex!(wvc.cache.dict, ci, mi)

function CC.abstract_call_known(interp::ClassifyInterp, @nospecialize(f), arginfo::CC.ArgInfo,
                                si::CC.StmtInfo, sv::CC.AbsIntState,
                                max_methods::Int = CC.get_max_methods(interp, f, sv))
    _record_use!(interp, f, arginfo.argtypes, sv)
    return @invoke CC.abstract_call_known(interp::CC.AbstractInterpreter, f::Any, arginfo::CC.ArgInfo,
                                          si::CC.StmtInfo, sv::CC.AbsIntState, max_methods::Int)
end

# the trait a value of type T is known by: a trait instance or an intersection, not a concrete member
function _trait_of(@nospecialize(T))
    T = CC.widenconst(T)
    (isconcretetype(T) || !(T isa Type)) && return nothing
    u = Base.unwrap_unionall(T)
    u isa DataType || return nothing
    (istrait(u) || u.name === Base.unwrap_unionall(Core.All).name) || return nothing
    return T
end

# whether the call of `f` at `argtypes` stays in the contract of the traits its arguments are known by
function _in_contract(interp::ClassifyInterp, @nospecialize(f), argtypes::Vector{Any}, k::Int, @nospecialize(X))
    atype = CC.argtypes_to_type(argtypes)
    # an operation of the trait or a supertrait, or a declared field: the compiler's rule
    CC.declared_operation_result(interp, argtypes, atype) === nothing || return true
    # a call with cast arguments (traits §7.6): the call it makes
    if f === Core.attributed_call && length(argtypes) >= 3 && k >= 4
        g = CC.singleton_type(CC.widenconst(argtypes[3]))
        g === nothing && return false
        return _in_contract(interp, g, argtypes[3:end], k - 2, X)
    end
    # keeping it with its attribute (traits §7.8), or a cast's unwrapping of a `Dynamic{X}`
    (f === Core.keep || f === Core._cast_compiled) && return true
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
        if pu isa DataType && istrait(pu) && X <: p
            continue
        end
        p === Any && m.module === interp.mod && continue
        return false
    end
    return true
end

function _record_use!(interp::ClassifyInterp, @nospecialize(f), argtypes::Vector{Any}, sv::CC.AbsIntState)
    sv isa CC.InferenceState || return nothing
    for k in 2:length(argtypes)
        X = _trait_of(argtypes[k])
        X === nothing && continue
        _in_contract(interp, f, argtypes, k, X) && continue
        m = sv.linfo.def
        m isa Method || return nothing
        u = TraitUse(_describe(f, argtypes), m, _line(sv, m), X)
        # constant propagation infers a call again: each use once
        any(v -> v.what == u.what && v.method === u.method && v.line == u.line, interp.uses) ||
            push!(interp.uses, u)
        return nothing
    end
    return nothing
end

function _describe(@nospecialize(f), argtypes::Vector{Any})
    fs = f isa Function ? string(nameof(f)) : string(f)
    return string(fs, "(", join([string(CC.widenconst(a)) for a in argtypes[2:end]], ", "), ")")
end

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
arguments (traits §7.3).
"""
function classify(m::Method; world::UInt = Base.get_world_counter())
    interp = ClassifyInterp(m.module; world)
    sig = m.sig
    tv = Any[]
    s = sig
    while s isa UnionAll
        push!(tv, s.var)
        s = s.body
    end
    CC.typeinf_frame(interp, m, sig, Core.svec(tv...), false)
    return interp.uses
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
# method is visible, so that inference can follow it).
function _check_bounded(m::Method)
    _trait_arguments(m) || return nothing
    _bounded(m) || return nothing
    uses = classify(m)
    isempty(uses) && return nothing
    Base.delete_method(m)
    lines = ["$(u.what) at line $(u.line) is not in the contract of $(u.trait)" for u in uses]
    throw(TraitUseError("$(m.name) is declared bounded, and is open:\n  " * join(lines, "\n  ")))
end
