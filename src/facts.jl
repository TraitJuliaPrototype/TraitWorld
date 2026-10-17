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
_fact_sig(@nospecialize(T)) = T isa DataType && (Base.isdispatchtuple(T) ||
    (T <: Tuple && !isempty(T.parameters) && _is_closure_type(T.parameters[1]) && _kinds_ok(T.parameters)))
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
        isdefined(m, b) && getglobal(m, b) === F.instance && return false       # a named function
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

"""
Concrete and semi-concrete evaluation under the policy. Both need foldable effects, which a run-time
site rules out, unless effects are asserted (`@assume_effects :foldable`, `Base.@pure`): then a
fold would run plain Julia's code, or resolve the site at constant arguments, and record only the
edge to the policy's CodeInstance, which holds no fact for the run-time site; a later definition
there would leave the folded value stale (G1). So no evaluation at compile time when the callee's
code under the policy (or code it invokes) has a run-time call.
"""
function CC.concrete_eval_eligible(interp::FactsInterp, @nospecialize(f), result::CC.MethodCallResult,
                                   arginfo::CC.ArgInfo, sv::CC.AbsIntState)
    r = @invoke CC.concrete_eval_eligible(interp::CC.AbstractInterpreter, f, result::CC.MethodCallResult,
                                          arginfo::CC.ArgInfo, sv::CC.AbsIntState)
    _FACTS_POLICY[] || return r
    (r === :concrete_eval || r === :semi_concrete_eval) || return r
    edge = result.edge
    edge isa Core.CodeInstance && _has_runtime_sites(edge) && return :none
    return r
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
                g isa GlobalRef && (g = isdefined(g.mod, g.name) ? getglobal(g.mod, g.name) : nothing)
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

# the runtime compiles a CodeInstance of this owner through these (e.g. an `:invoke` target)
import Core.OptimizedGenerics.CompilerPlugins: typeinf, typeinf_edge
@noinline typeinf(::FactsOwner, mi::Core.MethodInstance, source_mode::UInt8) =
    _in_compiler_world(CC.typeinf_ext_toplevel, FactsInterp(Base.tls_world_age()), mi, source_mode)
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
    return _in_compiler_world(CC.typeinf_ext_toplevel, FactsInterp(world), mi, CC.SOURCE_MODE_ABI)::Core.CodeInstance
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

