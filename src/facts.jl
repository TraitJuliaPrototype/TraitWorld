# ---------------------------------------------------------------------------
# The trait world's compiler policy (writeup/explorations/wrapping-by-facts.md, rule R):
# code compiled for the trait world depends on the method table only through facts at concrete
# signatures. An AbstractInterpreter with its own CodeInstance owner (`FactsOwner`) infers and
# compiles the workers an entry calls, and every callee they reach statically, into its own cache:
#   - a call whose argument types are concrete, or split into concrete signatures (union
#     splitting), is inferred as usual and records its edges (the facts);
#   - a call whose argument types are not concrete records nothing, not even for one or no
#     matching method: it is compiled as a run-time dispatch in the current world, typed `Any`.
# Julia's own invalidation of edges at concrete signatures is then exact (rule P), and plain
# Julia's code (the native cache) is untouched: a run-time site calls into it.
# ---------------------------------------------------------------------------

const CC = Base.Compiler

"The cache owner of code compiled under the trait world's policy."
struct FactsOwner end

struct FactsInterp <: CC.AbstractInterpreter
    world::UInt
    inf_params::CC.InferenceParams
    opt_params::CC.OptimizationParams
    inf_cache::Vector{CC.InferenceResult}
    codegen::IdDict{Core.CodeInstance,Core.CodeInfo}
end
FactsInterp(world::UInt = Base.get_world_counter()) =
    FactsInterp(world, CC.InferenceParams(), CC.OptimizationParams(), CC.InferenceResult[], IdDict{Core.CodeInstance,Core.CodeInfo}())

CC.InferenceParams(i::FactsInterp) = i.inf_params
CC.OptimizationParams(i::FactsInterp) = i.opt_params
CC.get_inference_world(i::FactsInterp) = i.world
CC.get_inference_cache(i::FactsInterp) = i.inf_cache
CC.cache_owner(::FactsInterp) = FactsOwner()
CC.codegen_cache(i::FactsInterp) = i.codegen
# keep the optimized IR in the CodeInstance: a package image then holds it (and, with piece 5 of
# the patched runtime, machine code compiled from it); a session can compile it again
CC.may_discard_trees(::FactsInterp) = false

"""
Whether `T` (a call's argument types) is concrete enough for a fact: a dispatch tuple, or a call of
a *closure* whose other arguments are kinds (`DataType`, `UnionAll`, `Union`: a type passed as a
value, as in Base's `any(p -> p === Union{}, types)` behind every broadcast's element type). A fact
at a kind is broken by any method of the function with an argument that admits a type value
(`Type{X}` for any `X`, `::Any`, a free type variable), so for a function others extend
(`zero`, a package's trait function) it would let unrelated packages invalidate trait code (final
review of 2026-10-17). Only a closure's owner adds methods to it.
"""
_fact_sig(@nospecialize(T)) = T isa DataType && (Base.isdispatchtuple(T) || _fact_splits(T) !== nothing ||
    (T <: Tuple && !isempty(T.parameters) && _is_closure_type(T.parameters[1]) && _kinds_ok(T.parameters)))

"The most concrete signatures one fact may stand for: Julia's own bound on union splitting."
const _MAX_FACT_SPLITS = 4

"""
The concrete signatures a fact at `T` stands for, or `nothing`: `T` itself when it is a dispatch
tuple, else the splits of unions of concrete types inside its tuple-typed arguments (at most
`_MAX_FACT_SPLITS`). A tuple value's type is always concrete, so `Tuple{Union{Missing, Int}, Int}`
admits exactly the values of `Tuple{Missing, Int}` and `Tuple{Int, Int}`: a fact there is the facts at
both, as top-level union splitting gives facts at each split. Such arguments are everywhere in
iteration over data with missing values (`item, state = iterate(v, s)` destructures a
`Tuple{Union{Missing, T}, Int}`); without this every one is a run-time site, once per element.
Top-level unions are left to union splitting (`find_method_matches`).
"""
function _fact_splits(@nospecialize(T))
    T isa DataType && T <: Tuple || return nothing
    Base.isdispatchtuple(T) && return Any[T]
    ps = T.parameters
    (isempty(ps) || Base.isvarargtype(ps[end])) && return nothing
    alts = Vector{Any}[]
    n = 1
    for p in ps
        a = Base.isdispatchelem(p) ? Any[p] : _tuple_splits(p)
        a === nothing && return nothing
        n *= length(a)
        n > _MAX_FACT_SPLITS && return nothing
        push!(alts, a)
    end
    return Any[Tuple{c...} for c in Iterators.product(alts...)][:]
end
"The concrete tuple types a tuple type with unions of concrete element types admits, or `nothing`."
function _tuple_splits(@nospecialize(P))
    P isa DataType && P <: Tuple || return nothing
    ps = P.parameters
    (isempty(ps) || Base.isvarargtype(ps[end])) && return nothing
    alts = Vector{Any}[]
    n = 1
    for q in ps
        a = Base.isdispatchelem(q) ? Any[q] :
            q isa Union ? (us = Base.uniontypes(q); all(Base.isdispatchelem, us) ? us : nothing) :
            _tuple_splits(q)
        a === nothing && return nothing
        n *= length(a)
        n > _MAX_FACT_SPLITS && return nothing
        push!(alts, a)
    end
    return Any[Tuple{c...} for c in Iterators.product(alts...)][:]
end
"""
A closure's type: a function type that is not a named function's (whose module binds its name to
its instance, as for `typeof(sum)`, also named `#sum`). Only its owner adds methods to it.
"""
function _is_closure_type(@nospecialize(F))
    (F isa DataType && F <: Function) || return false
    if isdefined(F, :instance)
        n = String(F.name.name)
        startswith(n, "#") || return false
        b = Symbol(n[2:end])
        m = F.name.module
        Base.invokelatest(_const_binding, m, b) === F.instance && return false   # a named function (bindings read in the latest world, not the compiler's)
    end
    return startswith(String(F.name.name), "#")
end
function _kinds_ok(ps::Core.SimpleVector)
    for p in ps
        (p isa Type && (Base.isdispatchelem(p) || p === DataType || p === UnionAll || p === Union)) || return false
    end
    return true
end

"""
Whether the call's function is the machinery's own (defined in TraitWorld): a call with abstract
argument types (a view's object held as `Any`, read at an offset) is inferred as usual, with its
edges, so this is sound whoever adds methods. It costs G2 only for the machinery, and only through
definitions of TraitWorld's functions: TraitWorld's own, and those trait modules make by design
(`param`, `implementation`, `_check_implementation`, which `@trait` and `@implement` extend), so
loading a trait library can invalidate some of the machinery's code under the policy.
"""
function _machinery_call(@nospecialize(ft))
    ft = CC.widenconst(ft)
    ft isa DataType || return false
    m = ft.name.module
    return Base.moduleroot(m) === TraitWorld
end

# (Session 26's facts at non-public functions, within the caller's package, were dropped in
# session 27: rule 3 lets a package that owns a type extend another package's internal function at
# that type, so such facts broke G2 (acceptance G2.1). Their purpose, the machinery's speed, came
# from bare invokes running native code, fixed by `_owner_invokes!`.)

"""
Concrete and semi-concrete evaluation under the policy. Both need foldable effects, which a run-time
site rules out, unless effects are asserted (`@assume_effects :foldable`, `Base.@pure`): then a
fold would run plain Julia's code, or resolve the site at constant arguments, and record only the
edge to the policy's CodeInstance, which holds no fact for the run-time site; a later definition
there would leave the folded value stale (G1). So no evaluation at compile time when the callee's
code under the policy (or code it invokes) has a run-time call, with one exception: a method of
Julia's own (Base, Core) whose effects Julia itself asserts foldable (`@_total_meta`,
`@assume_effects :foldable`), such as `eltype` of a tuple type behind every keyword splat's
`pairs`. Plain Julia folds such a call by the same assertion and records the same edge, so the
trait code is as fresh as plain Julia's precompiled code: only a pirate of Base's functions at
Base's types could make either stale, and strict mode refuses those.
"""
function CC.concrete_eval_eligible(interp::FactsInterp, @nospecialize(f), result::CC.MethodCallResult,
                                   arginfo::CC.ArgInfo, sv::CC.AbsIntState)
    r = @invoke CC.concrete_eval_eligible(interp::CC.AbstractInterpreter, f, result::CC.MethodCallResult,
                                          arginfo::CC.ArgInfo, sv::CC.AbsIntState)
    _FACTS_POLICY[] || return r
    (r === :concrete_eval || r === :semi_concrete_eval) || return r
    edge = result.edge
    edge isa Core.CodeInstance && _has_runtime_sites(edge) && !_julia_asserted_foldable(edge) && return :none
    return r
end
"Whether `ci` is the code of a method of Base or Core whose effects Julia asserts foldable."
function _julia_asserted_foldable(ci::Core.CodeInstance)
    m = Core.Compiler.get_ci_mi(ci).def
    m isa Method || return false
    r = Base.moduleroot(m.module)
    (r === Base || r === Core) || return false
    o = CC.decode_effects_override(m.purity)
    return o.consistent && o.effect_free && o.terminates_globally
end

const _RUNTIME_SITES = IdDict{Core.CodeInstance,Bool}()
const _RUNTIME_SITES_LOCK = Threads.SpinLock()
"Whether the policy's code `ci`, or code it invokes (at most `limit` CodeInstances), calls anything by run-time dispatch."
function _has_runtime_sites(ci::Core.CodeInstance; limit::Int = 500)
    r = @lock _RUNTIME_SITES_LOCK get(_RUNTIME_SITES, ci, nothing)
    r === nothing || return r
    seen = Base.IdSet{Core.CodeInstance}()
    todo = Core.CodeInstance[ci]
    found = false
    while !isempty(todo) && !found
        c = pop!(todo)
        c in seen && continue
        push!(seen, c)
        length(seen) > limit && (found = true; break)
        c.owner isa FactsOwner || (found = true; break)              # not the policy's code: unknown
        src = c.inferred
        if src === nothing
            # no IR: only a constant result is known to call nothing
            isdefined(c, :rettype_const) && continue
            found = true
            break
        end
        mi = Core.Compiler.get_ci_mi(c)
        mi.def isa Method || continue
        if !(src isa Core.CodeInfo)
            src isa String || (found = true; break)
            src = ccall(:jl_uncompress_ir, Ref{Core.CodeInfo}, (Any, Any, Any), mi.def, c, src)
        end
        for st in src.code
            if Meta.isexpr(st, :invoke)
                t = st.args[1]
                t isa Core.CodeInstance && push!(todo, t)
            elseif Meta.isexpr(st, :call)
                g = st.args[1]
                g isa GlobalRef && (g = Base.invokelatest(_const_binding, g.mod, g.name))
                g isa QuoteNode && (g = g.value)
                if !(g isa Core.Builtin) || g === Core._apply_iterate || g === Core._call_latest ||
                   g === Core._call_in_world || g === Core.invoke || g === Core.finalizer
                    found = true
                    break
                end
            elseif Meta.isexpr(st, :new_opaque_closure)
                found = true
                break
            end
        end
    end
    @lock _RUNTIME_SITES_LOCK _RUNTIME_SITES[ci] = found
    return found
end

"""
`return_type` (and so `promote_op`, broadcasting's and `map`'s element types) asks what *plain
Julia's* inference gives, so under the policy it is folded from plain Julia's inference, never
from the policy's own (which types a run-time site `Any`: `map(x -> 1, Integer[])` would be a
`Vector{Any}`, acceptance G1.8). At a concrete signature whose native answer rests on concrete
facts only (`_concrete_deps`), the fold records the dispatch fact at the signature and an edge to
the native CodeInstance it read (`_NativeRT`): the trait code is invalidated exactly when plain
Julia's answer can change. Otherwise the call is left to run time, where it is plain Julia's
inference in the current world: folding an answer that rests on abstract dispatch would let any
load that adds a method there invalidate the trait code (G2).
"""
struct _NativeRT <: CC.CallInfo
    sig::Any
    ci::Core.CodeInstance
end
CC.add_edges_impl(edges::Vector{Any}, info::_NativeRT) = (push!(edges, info.sig); push!(edges, info.ci); nothing)

"""
Whether native code's answer rests on facts at concrete signatures only, in it and in the native
code it depends on (through at most `limit` CodeInstances). Abstract dispatch shows in an edge list
as a method-table edge, a match group (`Int`, then the call's type), a bare MethodInstance (a cycle
partner), a CodeInstance or MethodInstance at a non-concrete signature, or an invoke signature that
is neither concrete nor its method's own. Then folding the answer into the policy's code keeps G2
(a load invalidates it only through a concrete fact); otherwise `return_type` runs at run time.
"""
function _concrete_deps(ci::Core.CodeInstance; limit::Int = 2000)
    seen = Base.IdSet{Core.CodeInstance}()
    todo = Core.CodeInstance[ci]
    while !isempty(todo)
        c = pop!(todo)
        c in seen && continue
        push!(seen, c)
        length(seen) > limit && return false
        es = c.edges
        i = 1
        while i <= length(es)
            e = es[i]
            if e isa Int || e === Core.MethodTable || e isa Core.MethodTable || e isa Core.MethodInstance
                return false
            elseif e isa Core.Binding
                i += 1
            elseif e isa Core.CodeInstance
                _fact_sig(Core.Compiler.get_ci_mi(e).specTypes) || return false
                push!(todo, e)
                i += 1
            elseif e isa Type && i < length(es)
                callee = es[i + 1]
                callee isa Core.CodeInstance || return false
                m = Core.Compiler.get_ci_mi(callee).def
                (_fact_sig(e) || (m isa Method && e == m.sig)) || return false
                push!(todo, callee)
                i += 2
            else
                return false
            end
        end
    end
    return true
end

function CC.return_type_tfunc(interp::FactsInterp, argtypes::Vector{Any}, si::CC.StmtInfo, sv::CC.AbsIntState)
    _FACTS_POLICY[] || return @invoke CC.return_type_tfunc(interp::CC.AbstractInterpreter, argtypes::Vector{Any}, si::CC.StmtInfo, sv::CC.AbsIntState)
    UNKNOWN = CC.CallMeta(Type, Any, CC.Effects(CC.EFFECTS_THROWS; nortcall = false), CC.NoCallInfo())
    2 <= length(argtypes) <= 3 || return CC.Future(UNKNOWN)
    tt = CC.widenslotwrapper(argtypes[end])
    T = tt isa CC.Const ? tt.val : (CC.isType(tt) && !CC.has_free_typevars(tt)) ? tt.parameters[1] : nothing
    (T isa DataType && T <: Tuple) || return CC.Future(UNKNOWN)
    sig = length(argtypes) == 3 ? Tuple{CC.widenconst(CC.widenslotwrapper(argtypes[2])), T.parameters...} : T
    _fact_sig(sig) || return CC.Future(UNKNOWN)
    # 1. the policy's own answer, with its facts as edges, when it is a concrete type or Union{}:
    #    it differs from plain Julia's only through values inference decides (A3), e.g. Union{}
    #    where an abstract site's methods all throw, or a nested `return_type` in the callee
    own = @invoke CC.return_type_tfunc(interp::CC.AbstractInterpreter, argtypes::Vector{Any}, si::CC.StmtInfo, sv::CC.AbsIntState)
    return CC.Future{CC.CallMeta}(own, interp, sv) do call, interp, sv
        rt = call.rt
        if rt isa CC.Const && rt.val isa Type && (rt.val === Union{} || isconcretetype(rt.val))
            return call
        end
        # 2. plain Julia's answer, folded when it rests on concrete facts; 3. otherwise at run time
        r = _native_return_type(interp, sig, sv)
        return r === nothing ? UNKNOWN : r
    end
end

"Plain Julia's `return_type` at `sig` from native inference at the match's own signature (not the compilation signature, which `@nospecialize`, `Function`, `Type` and long Vararg arguments widen), when it rests on concrete facts."
function _native_return_type(interp::FactsInterp, @nospecialize(sig), sv::CC.AbsIntState)
    world = CC.get_inference_world(interp)
    lo, hi = Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt))
    ms = Base._methods_by_ftype(sig, nothing, 1, world, false, lo, hi, Ptr{Int32}(C_NULL))
    (ms isa Vector && length(ms) == 1) || return nothing
    match = ms[1]::Core.MethodMatch
    match.fully_covers || return nothing
    mi = CC.specialize_method(match)
    nci = CC.typeinf_ext_toplevel(CC.NativeInterpreter(world), mi, CC.SOURCE_MODE_NOT_REQUIRED)
    nci isa Core.CodeInstance || return nothing
    _concrete_deps(nci) || return nothing
    CC.update_valid_age!(sv, CC.WorldRange(max(lo[], nci.min_world), min(hi[], nci.max_world)))
    # a constant result folds as plain compiled code folds it (`typeof` of the constant)
    rt = isdefined(nci, :rettype_const) ? Core.Typeof(nci.rettype_const) : nci.rettype
    return CC.CallMeta(CC.Const(rt), Union{}, CC.Effects(CC.EFFECTS_TOTAL; nortcall = false),
                       CC.MethodResultPure(_NativeRT(sig, nci)))
end

"""
The world the compiler runs in for the policy: fixed when TraitWorld is initialized, as Julia fixes
its own compiler's world (`jl_typeinf_world`). The world inferred *for* is the interpreter's own
(`FactsInterp(world)`); this is only the world the compiler's code executes in, so methods loaded
later (CSV, Makie, …) cannot invalidate the compiler's native code specialized for `FactsInterp`
(without it a session recompiled about 670 such instances after big loads: 7 s).
"""
const _COMPILER_WORLD = Ref{UInt}(0)
function _in_compiler_world(f, args...; kws...)
    w = _COMPILER_WORLD[]
    return w == 0 ? Base.invokelatest(f, args...; kws...) : Base.invoke_in_world(w, f, args...; kws...)
end

"A keyword call of the machinery's own function (`Core.kwcall(nt, f, args...)` with `f` TraitWorld's): its methods are TraitWorld's too."
function _machinery_kwcall(argtypes::Vector{Any})
    length(argtypes) >= 3 || return false
    ft = CC.widenconst(argtypes[1])
    ft === typeof(Core.kwcall) || return false
    return _machinery_call(argtypes[3])
end

const _ABSTRACT_SITE = CC.FailedMethodMatch("trait world: argument types not concrete, dispatched at run time")

function CC.find_method_matches(interp::FactsInterp, argtypes::Vector{Any}, @nospecialize(atype);
                                max_union_splitting::Int = CC.InferenceParams(interp).max_union_splitting,
                                max_methods::Int = CC.InferenceParams(interp).max_methods)
    𝕃 = CC.typeinf_lattice(interp)
    if !_FACTS_POLICY[] || (!isempty(argtypes) && (_machinery_call(argtypes[1]) || _machinery_kwcall(argtypes)))
        return @invoke CC.find_method_matches(interp::CC.AbstractInterpreter, argtypes::Vector{Any}, atype::Any;
                                              max_union_splitting, max_methods)
    end
    if CC.is_union_split_eligible(𝕃, argtypes, max_union_splitting)
        for arg_n in CC.switchtupleunion(𝕃, argtypes)
            sig_n = CC.argtypes_to_type(arg_n)
            sig_n === Union{} && continue
            _fact_sig(sig_n) || return _ABSTRACT_SITE
        end
        return CC.find_union_split_method_matches(interp, argtypes, max_methods)
    end
    _fact_sig(atype) || return _ABSTRACT_SITE
    return CC.find_simple_method_matches(interp, atype, max_methods)
end

"""
Bare `:invoke`s of a `MethodInstance` in the policy's code: the optimizer emits them for a callee
whose result was not cached when the caller was optimized (a partner in a recursion cycle, a callee
inferred without caching). At run time such an invoke runs the *native* code of that instance,
which loads invalidate and which depends on the method table beyond concrete facts. So each one is
made an `:invoke` of the policy's CodeInstance of the same instance when it exists, or else a call
of `_invoke_under_policy`, which finds or compiles it at run time. A call that only throws
(`Union{}`) keeps plain Julia's code: it is a cold path, and its native code comes with the system
image. Edges are unchanged, so invalidation is as before (piece 9 makes bare edges owner-aware).
"""
function CC.transform_result_for_cache(interp::FactsInterp, result::CC.InferenceResult, edges::Core.SimpleVector)
    src = @invoke CC.transform_result_for_cache(interp::CC.AbstractInterpreter, result::CC.InferenceResult, edges::Core.SimpleVector)
    _FACTS_POLICY[] && src isa Core.CodeInfo && _owner_invokes!(src, CC.get_inference_world(interp))
    return src
end
function _owner_invokes!(src::Core.CodeInfo, world::UInt)
    code = src.code
    types = src.ssavaluetypes
    for i in eachindex(code)
        st = code[i]
        (st isa Expr && st.head === :invoke) || continue
        mi = st.args[1]
        (mi isa Core.MethodInstance && mi.def isa Method) || continue
        types isa Vector{Any} && types[i] === Union{} && continue
        ci = _owner_ci(mi, world)
        if ci isa Core.CodeInstance
            st.args[1] = ci
        else
            code[i] = Expr(:call, GlobalRef(TraitWorld, :_invoke_under_policy), QuoteNode(mi), st.args[2:end]...)
            push!(get!(() -> Core.MethodInstance[], task_local_storage(), :tw_policy_pending)::Vector{Core.MethodInstance}, mi)
        end
    end
    _RUNTIME_POLICY[] && _policy_sites!(src, world)
    return src
end

"""
Whether run-time sites in the policy's code run the policy's code (`_call_under_policy`), or plain
Julia's native code (`JULIA_TW_RUNTIME_SITES=native`, the design until session 27). Read when
TraitWorld is loaded; it decides the IR stored in CodeInstances, so images built with one setting
keep it.
"""
const _RUNTIME_POLICY = Ref(true)

"The value a statement's callee `g` stands for in `world`, if it is a constant (bindings are read in the world inferred for, not the compiler's)."
function _callee_value(@nospecialize(g), world::UInt)
    g isa GlobalRef && return Base.invoke_in_world(world, _const_binding, g.mod, g.name)
    g isa QuoteNode && return g.value
    g isa Union{Core.SSAValue, Core.Argument, Expr} && return nothing
    return g
end
_const_binding(m::Module, n::Symbol) = isdefined(m, n) && isconst(m, n) ? getglobal(m, n) : nothing
"Whether a call of `g` stays as it is: builtins, and TraitWorld's and the compiler's own functions."
function _keep_call(@nospecialize(gv))
    gv isa Core.Builtin && return true
    gv isa Function || return false
    m = parentmodule(typeof(gv))
    r = Base.moduleroot(m)
    return r === TraitWorld || m === Base.Compiler || parentmodule(m) === Base.Compiler || r === Core.Compiler
end

"""
Run-time sites made calls of `_call_under_policy`, which dispatches at run time as plain Julia does
and runs the policy's code of the method found: a `:call` of a function that is no builtin, and the
function of a splatted call (`Core._apply_iterate`). TraitWorld's and the compiler's own calls stay.
"""
function _policy_sites!(src::Core.CodeInfo, world::UInt)
    code = src.code
    for i in eachindex(code)
        st = code[i]
        st isa Expr || continue
        if st.head === :call
            g = st.args[1]
            gv = _callee_value(g, world)
            if gv === Core._apply_iterate && length(st.args) >= 3
                # a splatted call of a known function: its function becomes the first argument (a
                # constant tuple, so the IR stays flat); one of unknown function stays as it is
                h = _callee_value(st.args[3], world)
                (h === nothing || _keep_call(h)) && continue
                code[i] = Expr(:call, st.args[1], st.args[2], GlobalRef(TraitWorld, :_call_under_policy),
                               QuoteNode((h,)), st.args[4:end]...)
                continue
            end
            (gv === nothing || !_keep_call(gv)) || continue
            # a site of fixed arity keeps its own cache (`_CallSite`); longer calls take the trampoline
            code[i] = length(st.args) <= _SITE_MAXARGS + 1 ?
                Expr(:call, GlobalRef(TraitWorld, :_call_site), QuoteNode(_CallSite()), st.args...) :
                Expr(:call, GlobalRef(TraitWorld, :_call_under_policy), st.args...)
        elseif st.head === :(=) && length(st.args) == 2 && Meta.isexpr(st.args[2], :call)
            # (optimized IR has no assignments; kept for safety)
            continue
        end
    end
    return src
end

"""
A run-time site in the policy's code: dispatch at run time, in the caller's world, as plain Julia
does; then run the policy's code of the method found, compiled under the policy and kept in images,
rather than plain Julia's native code, which other packages' loads invalidate. No fact is recorded
at the site, so what it calls is decided at each call, as in plain Julia. No method, or an
ambiguity, takes plain Julia's call, which raises the same error.
"""
function _call_under_policy(@nospecialize(f), @nospecialize(args...))
    ci = _policy_ci(Base.tls_world_age(), f, args)
    return ci === nothing ? f(args...) : Core.invoke(f, ci, args...)
end
"""
The policy's CodeInstance that a call of `f` with `args` runs in `world`, compiled if needed; or
`nothing` when plain Julia's call runs: a builtin, no method or an ambiguity (the call raises the same
error), the machinery's own methods, or code the policy cannot compile.
"""
function _policy_ci(world::UInt, @nospecialize(f), @nospecialize(args::Tuple))
    f isa Core.Builtin && return nothing                 # a builtin passed as a value
    tt = Tuple{Core.Typeof(f), Any[Core.Typeof(a) for a in args]...}
    mi = ccall(:jl_method_lookup_by_tt, Any, (Any, Csize_t, Any), tt, world, nothing)
    (mi isa Core.MethodInstance && mi.def isa Method) || return nothing
    _keep_method(mi.def) && return nothing
    ci = _owner_ci(mi, world)
    if !(ci isa Core.CodeInstance)
        (@lock _NO_POLICY_LOCK haskey(_NO_POLICY, mi)) && return nothing
        _FACTS_DEBUG[] && Core.println("TraitWorld: compiling under the policy at a run-time site: ", mi)
        ci = try
            _typeinf_policy(world, mi, CC.SOURCE_MODE_ABI)
        catch
            nothing
        end
        ci isa Core.CodeInstance || @lock _NO_POLICY_LOCK (_NO_POLICY[mi] = true)
    end
    ci isa Core.CodeInstance || return nothing           # inference gave up: plain Julia's code
    ci.invoke == C_NULL && ccall(:jl_compile_codeinst, Cint, (Any,), ci)
    ci.invoke == C_NULL && return nothing                # stock Julia cannot run this owner's code
    return ci
end

"""
A run-time site's cache, as Julia keeps one for its own dynamic dispatch: the last dispatch the
site made. Dispatch is a function of the world and the arguments' `Core.Typeof` (`Type{Int}` for
the value `Int`, which dispatches apart from a value of type `Int`), so a call in the same world
with the same keys runs the same CodeInstance, which stays valid in that world (invalidation only
ends a CodeInstance's validity after the world it was valid in). An entry holds this process's token: a
cache kept in an image never hits with a world number of the process that built it. Without the
cache a hot site cost 6.5 µs per call (a type built and looked up per call), against 26 ns for
plain dynamic dispatch.
"""
mutable struct _CallSite
    @atomic entry::Any
end
_CallSite() = _CallSite(nothing)
struct _CallSiteEntry{N}
    session::UInt
    world::UInt
    key::NTuple{N,Any}           # the callee's and the arguments' dispatch keys
    ci::Union{Nothing,Core.CodeInstance}     # nothing: plain Julia's call
end
"This process's token for site caches (set when TraitWorld is initialized)."
const _SESSION = Ref{UInt}(0)
_session_token() = UInt(time_ns()) ⊻ (UInt(getpid()) << 40) | UInt(1)
_dkey(@nospecialize(x)) = Core.Typeof(x)      # the lookup's own key: `Type{X}` for a type value
const _SITE_MAXARGS = 4
"A site's miss: dispatch as `_call_under_policy` does, and keep the result for the next call."
function _site_miss(s::_CallSite, w::UInt, @nospecialize(f), @nospecialize(args::Tuple))
    ci = _policy_ci(w, f, args)
    key = (_dkey(f), map(_dkey, args)...)
    @atomic :release s.entry = _CallSiteEntry{length(key)}(_SESSION[], w, key, ci)
    return ci === nothing ? f(args...) : Core.invoke(f, ci, args...)
end
for n in 0:_SITE_MAXARGS
    as = [Symbol(:a, k) for k in 1:n]
    hit = foldl((x, k) -> :($x && e.key[$(k + 1)] === _dkey($(as[k]))), 1:n; init = :(e.key[1] === _dkey(f)))
    @eval function _call_site(s::_CallSite, @nospecialize(f), $([:(@nospecialize($a)) for a in as]...))
        e = @atomic :acquire s.entry
        w = Base.tls_world_age()
        if e isa _CallSiteEntry{$(n + 1)} && e.world == w && e.session == _SESSION[] && $hit
            ci = e.ci
            return ci === nothing ? f($(as...)) : Core.invoke(f, ci, $(as...))
        end
        return _site_miss(s, w, f, ($(as...),))
    end
end
"Method instances the policy could not compile at a run-time site: plain Julia's code, without trying again."
const _NO_POLICY = IdDict{Core.MethodInstance,Bool}()
const _NO_POLICY_LOCK = ReentrantLock()
"Methods whose code runs as plain Julia's even from the policy's run-time sites: TraitWorld's, the compiler's, generated functions."
function _keep_method(m::Method)
    r = Base.moduleroot(m.module)
    r === TraitWorld && return true
    (m.module === Base.Compiler || parentmodule(m.module) === Base.Compiler) && return true
    isdefined(m, :generator) && return true
    return false
end
"""
Inference under the policy from the top: Julia's `typeinf_ext_toplevel` with `FactsInterp`, in the
compiler's world. When the outermost one returns, the callees that its code reaches through
`_invoke_under_policy` are compiled under the policy too, so that they are found at run time and
kept in the image being built (otherwise a session compiles them on first use, which after big loads
also compiles the policy's compiler code again, seconds, open-issues §1.3).
"""
function _typeinf_policy(world::UInt, mi::Core.MethodInstance, source_mode::UInt8)
    tls = task_local_storage()
    depth = get(tls, :tw_policy_depth, 0)::Int
    tls[:tw_policy_depth] = depth + 1
    ci = try
        _in_compiler_world(CC.typeinf_ext_toplevel, FactsInterp(world), mi, source_mode)
    finally
        tls[:tw_policy_depth] = depth
    end
    depth == 0 && _compile_pending!(world)
    return ci
end
# bounds, as the generator's depth: a recursion with growing types would otherwise go on compiling
# ever deeper signatures; what is left over is compiled at run time, on first use, like plain Julia
const _PENDING_MAX = 256
const _PENDING_DEPTH = 8
_type_depth(@nospecialize(T)) = T isa DataType ? 1 + maximum(_type_depth, T.parameters; init = 0) :
    T isa UnionAll ? _type_depth(Base.unwrap_unionall(T)) : T isa Union ? max(_type_depth(T.a), _type_depth(T.b)) : 0
function _compile_pending!(world::UInt)
    pend = get(task_local_storage(), :tw_policy_pending, nothing)
    pend === nothing && return nothing
    done = 0
    while !isempty(pend)
        mi = pop!(pend::Vector{Core.MethodInstance})
        if done >= _PENDING_MAX
            empty!(pend)
            break
        end
        _owner_ci(mi, world) === nothing || continue
        _type_depth(mi.specTypes) > _PENDING_DEPTH + 2 && continue
        done += 1
        try
            _typeinf_policy(world, mi, CC.SOURCE_MODE_ABI)
        catch
            # left to run time (`_invoke_under_policy`)
        end
    end
    return nothing
end

"""
The policy's CodeInstance of `mi` valid in `world` that can be invoked, or `nothing`: a walk of the instance's cache,
which runs no compiler code (an image keeps CodeInstances without IR, which `jl_rettype_inferred`
does not return; entering the compiler instead costs seconds when loads have invalidated its native
code for `FactsInterp`, open-issues §1.3).
"""
function _owner_ci(mi::Core.MethodInstance, world::UInt)
    isdefined(mi, :cache) || return nothing
    ci = mi.cache
    while true
        # with native code (an image on stock Julia keeps none for the policy's code: piece 5)
        ci.owner isa FactsOwner && ci.min_world <= world <= ci.max_world && ci.invoke != C_NULL && return ci
        isdefined(ci, :next) || break
        ci = ci.next
    end
    # else code the runtime can compile, as `facts_codeinstance` finds it
    c = ccall(:jl_rettype_inferred, Any, (Any, Any, UInt, UInt), FactsOwner(), mi, world, world)
    return c isa Core.CodeInstance ? c : nothing
end
"The call of method instance `mi` in the policy's code, compiled under the policy in the caller's world if needed."
function _invoke_under_policy(mi::Core.MethodInstance, @nospecialize(f), @nospecialize(args...))
    w = Base.tls_world_age()
    ci = _owner_ci(mi, w)
    if !(ci isa Core.CodeInstance)
        _FACTS_DEBUG[] && (t0 = time(); Core.println("TraitWorld: compiling under the policy at run time: ", mi))
        ci = _typeinf_policy(w, mi, CC.SOURCE_MODE_ABI)
        _FACTS_DEBUG[] && Core.println("  ", round(time() - t0; digits = 3), " s")
    end
    # the policy could not compile the instance (a generated function's, as `_carries_static`
    # reached by a bare call): plain Julia's code of the same method, as at a run-time site
    ci isa Core.CodeInstance || return Core.invoke(f, Tuple{mi.specTypes.parameters[2:end]...}, args...)
    ci.invoke == C_NULL && ccall(:jl_compile_codeinst, Cint, (Any,), ci)
    if ci.invoke == C_NULL
        # the runtime cannot compile this owner's code here (stock Julia, without the patched
        # build's support for foreign code instances): plain Julia's code of the same method, as before
        return Core.invoke(f, Tuple{mi.specTypes.parameters[2:end]...}, args...)
    end
    return Core.invoke(f, ci, args...)
end

# the runtime compiles a CodeInstance of this owner through these (e.g. an `:invoke` target)
import Core.OptimizedGenerics.CompilerPlugins: typeinf, typeinf_edge
@noinline typeinf(::FactsOwner, mi::Core.MethodInstance, source_mode::UInt8) =
    _typeinf_policy(Base.tls_world_age(), mi, source_mode)
@noinline typeinf_edge(::FactsOwner, mi::Core.MethodInstance, parent_frame::CC.InferenceState, world::UInt, source_mode::UInt8) =
    CC.typeinf_edge(FactsInterp(world), mi.def, mi.specTypes, Core.svec(), parent_frame, false, false)

"""
    facts_codeinstance(sig, world = current) -> CodeInstance

The CodeInstance compiled under the trait world's policy for the call signature `sig`
(`Tuple{typeof(f), argument types...}`), valid in `world`; `nothing` if no method matches.
"""
function facts_codeinstance(@nospecialize(sig), world::UInt = Base.tls_world_age())
    mi = ccall(:jl_method_lookup_by_tt, Any, (Any, Csize_t, Any), sig, world, nothing)
    mi isa Core.MethodInstance || return nothing
    # a hit in the policy's cache (from an image, or earlier in the session) runs no compiler code:
    # the compiler's own native code specialized for `FactsInterp` is in TraitWorld's image, but a
    # package loaded before TraitWorld can make it fail verification at load (about 1.5 s to
    # compile it again), and a first call of code the images hold needs no inference at all
    c = ccall(:jl_rettype_inferred, Any, (Any, Any, UInt, UInt), FactsOwner(), mi, world, world)
    c isa Core.CodeInstance && return c
    return _typeinf_policy(world, mi, CC.SOURCE_MODE_ABI)::Core.CodeInstance
end

"Whether entries call workers through the trait world's policy (`JULIA_TW_FACTS=0` turns it off)."
const FACTS = Ref(false)
const _FACTS_POLICY = Ref(true)          # false: the own cache under Julia's own policy (for diagnosis)
const _FACTS_DEBUG = Ref(false)

"""
The generator of `_facts_call`, given the world it generates for: it compiles the worker under the
policy in that world and emits `invoke(f, ci, args...)` of the resulting CodeInstance `ci`, a
constant. Inference types the call by `ci`'s result type and records the edge `(method sig, ci)`
(`InvokeCICallInfo`): the entry is invalidated when the worker's code under the policy is (a fact
broken) or the method is replaced, never by the native code of the same method instance.
That edge says nothing about dispatch at the call's own signature: the generated code adds the
edge `(sig, ci)`, a dispatch fact at the concrete signature (as native code records for a call
whose method instance is wider than the call), and the lookup's world bounds. A method added
later that is more specific at `sig` invalidates the entry (acceptance G1.6).
The call is marked `@noinline` unless the runtime has piece 10 (`_INLINER_KEEPS_CI`): Julia's inliner resolves `:invoke ci` by the method instance in
the caller's own cache, so a native caller would inline the worker's native code, and the edge
to that code would be dropped as a duplicate of `ci`'s (a stale-code hole, review of 2026-10-17).
A worker that calls its own function's entry again (recursion through an entry, also with
growing types) would make the generator infer the worker again while it is being inferred: on
re-entry, or beyond `_FACTS_GEN_DEPTH` nested generations, the generator throws, inference of that
call gives up without caching, and the caller calls `_facts_call` at run time. Not a `CachedGenerator`: its result is generated again whenever the entry is inferred again.
"""
struct _FactsCallGen end
"""
Whether Julia's inliner inlines exactly the CodeInstance an `invoke` names when it belongs to another
owner (julia-support.md piece 10: a resolver for a given CodeInstance). Then the entry's call of the
worker need not be `@noinline`: a native caller inlines the policy's code, with its edge.
"""
const _INLINER_KEEPS_CI = Ref(false)
_inliner_keeps_ci() = hasmethod(CC.resolve_todo, Tuple{Core.CodeInstance, CC.CallInfo, UInt32, CC.InliningState})
_INLINER_KEEPS_CI[] = _inliner_keeps_ci()        # also while an image is built (no `__init__` then)
struct _FactsReentry <: Exception
    sig::Any
end
"Entries nested deeper than this while their workers are compiled are called at run time."
const _FACTS_GEN_DEPTH = 8
function (::_FactsCallGen)(world::UInt, source::Method, self, f, args)
    sig = Tuple{f, args...}
    as = Any[:(getfield(args, $i)) for i in 1:length(args)]
    active = get!(() -> Any[], task_local_storage(), :tw_facts_generating)::Vector{Any}
    if any(s -> s === sig, active) || length(active) >= _FACTS_GEN_DEPTH
        # recursion through an entry (the worker's code is being made), or with growing types: no
        # code is generated, so inference gives up on this call without caching anything and the
        # caller calls `_facts_call` at run time, when the worker's code exists
        throw(_FactsReentry(sig))
    else
        lo_r, hi_r = Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt))
        ms = Base._methods_by_ftype(sig, nothing, -1, world, false, lo_r, hi_r, Ptr{Int32}(C_NULL))
        push!(active, sig)
        ci = try
            facts_codeinstance(sig, world)
        finally
            pop!(active)
        end
        _FACTS_DEBUG[] && Core.println("facts entry: ", sig, " in world ", world)
        if ci === nothing
            # no method: the plain call, which raises the plain `MethodError` (its inference
            # records the method table edge that a later method breaks)
            call = :(f($(as...)))
            lo, hi = UInt(1), typemax(UInt)
            edges = nothing
        else
            call = :(Core.invoke(f, $ci, $(as...)))
            # effects asserted somewhere below (`@assume_effects`, `Base.@pure`) can make the
            # policy's code claim foldable effects over a run-time site: the native caller would
            # then evaluate the call at compile time and fold a value whose facts it never records
            # (acceptance G1.10); the barrier keeps the type and drops the constant
            if CC.is_foldable(CC.decode_effects(ci.ipo_purity_bits), true) && _has_runtime_sites(ci)
                call = :(Base.compilerbarrier(:const, $call))
            end
            lo, hi = lo_r[], hi_r[]
            edges = Core.svec(sig, ci)
        end
    end
    body = _INLINER_KEEPS_CI[] ?
        Expr(:block, Expr(:meta, :inline), Expr(:local, Expr(:(=), :val, call)), Expr(:return, :val)) :
        Expr(:block, Expr(:meta, :inline),
             Expr(:noinline, true), Expr(:local, Expr(:(=), :val, call)), Expr(:noinline, false),
             Expr(:return, :val))
    lam = Expr(:lambda, Any[Symbol("#self#"), :f, :args], Expr(:var"scope-block", body))
    src = Base.generated_body_to_codeinfo(lam, @__MODULE__, true)
    if edges !== nothing
        src.edges = src.edges === nothing ? edges : Core.svec(src.edges..., edges...)
        src.min_world = lo
        src.max_world = hi
    end
    return src
end

@eval function _facts_call(f, args...)
    $(Expr(:meta, :generated, _FactsCallGen()))
    $(Expr(:meta, :generated_only))
end
"""
In a closed build (`--trim`), replace `_facts_call` by the plain call (`verify_main` does it when it
closes the world, after every package is loaded). Package images built in a session hold entries
generated for the policy (`--trim` does not key images); replacing the method invalidates every
entry compiled against it, so the build infers them again, for the closed world, where they call
workers plainly. Nothing loads in a binary afterwards: the invalidation is free.
"""
function _close_policy!()
    _closed_build() || return nothing
    Core.eval(@__MODULE__, :(_facts_call(f, args...) = f(args...)))
    return nothing
end

"""
    _facts_call(f, args...)

The call of a worker under the policy, made by `checked_call`: a direct call of its CodeInstance
compiled under the policy (see `_FactsCallGen`), typed by that code's result type. Inlined into
the entry: a frame of its own, which copies a view built on the entry's stack into an argument
tuple, made typed calls twice as slow (69 against 37 ns).
"""
_facts_call

"""
    _latest_under_policy(f, args...)

A slow path of the machinery (finding a conformance's builder, the checks at a signature's first
call) run in the latest world and compiled under the policy, like a worker: its code depends on
the method table only through facts at concrete signatures, so loads that invalidate the native
code of TraitWorld's reflective, abstractly typed implementation do not reach it, and a first call
after them need not infer it again. Its abstract sites call plain Julia's code at run time.
"""
_latest_under_policy(f, args...) =
    _policy_path() ? Base.invokelatest(_facts_call, f, args...) : Base.invokelatest(f, args...)

"""
The world the machinery decides conformances in: the caller's (`tls_world_age()` where an entry's
slow path starts), as plain Julia dispatches in the caller's world. A task pinned to an older world
then sees the conformances of its world, not of the latest. Outside a decision, the latest world.
"""
const _DECISION_WORLD = Base.ScopedValues.ScopedValue{UInt}(UInt(0))
_decision_world() = (w = _DECISION_WORLD[]; w == 0 ? Base.get_world_counter() : w)
_in_decision_world(f, args...) =
    (w = _DECISION_WORLD[]; w == 0 ? Base.invokelatest(f, args...) : Base.invoke_in_world(w, f, args...))
"`_latest_under_policy` in world `w`, deciding in `w`."
_in_world_under_policy(w::UInt, f, args...) = Base.ScopedValues.with(_DECISION_WORLD => w) do
    _policy_path() ? Base.invoke_in_world(w, _facts_call, f, args...) : Base.invoke_in_world(w, f, args...)
end

