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

"Whether `T` (a call's argument types) is concrete: a fact can be recorded at it."
_fact_sig(@nospecialize(T)) = T isa DataType && Base.isdispatchtuple(T)

"""
Whether the call's function is the machinery's own (defined in TraitWorld): its methods are
TraitWorld's alone, a fixed set, so a call with abstract argument types (a view's object held as
`Any`, read at an offset) is inferred as usual. Its edges can be broken only by a definition of
TraitWorld's own functions, which only TraitWorld (or a pirate of it) makes.
"""
function _machinery_call(@nospecialize(ft))
    ft = CC.widenconst(ft)
    ft isa DataType || return false
    m = ft.name.module
    return Base.moduleroot(m) === TraitWorld
end

"""
`return_type` (and so `promote_op`, broadcasting's and `map`'s element types) asks what *plain
Julia's* inference gives, so under the policy it is folded from plain Julia's inference, never
from the policy's own (which types a run-time site `Any`: `map(x -> 1, Integer[])` would be a
`Vector{Any}`, acceptance G1.8). At a concrete signature the fold records the dispatch fact at
the signature and an edge to the native CodeInstance it read (`_NativeRT`): the trait code is
invalidated exactly when plain Julia's answer can change. At an abstract signature the call is
left to run time, where it is plain Julia's inference in the current world.
"""
struct _NativeRT <: CC.CallInfo
    sig::Any
    ci::Core.CodeInstance
end
CC.add_edges_impl(edges::Vector{Any}, info::_NativeRT) = (push!(edges, info.sig); push!(edges, info.ci); nothing)
CC.nsplit_impl(::_NativeRT) = 0

function CC.return_type_tfunc(interp::FactsInterp, argtypes::Vector{Any}, si::CC.StmtInfo, sv::CC.AbsIntState)
    _FACTS_POLICY[] || return @invoke CC.return_type_tfunc(interp::CC.AbstractInterpreter, argtypes::Vector{Any}, si::CC.StmtInfo, sv::CC.AbsIntState)
    UNKNOWN = CC.Future(CC.CallMeta(Type, Any, CC.Effects(CC.EFFECTS_THROWS; nortcall = false), CC.NoCallInfo()))
    2 <= length(argtypes) <= 3 || return UNKNOWN
    tt = CC.widenslotwrapper(argtypes[end])
    T = tt isa CC.Const ? tt.val : (CC.isType(tt) && !CC.has_free_typevars(tt)) ? tt.parameters[1] : nothing
    (T isa DataType && T <: Tuple) || return UNKNOWN
    sig = length(argtypes) == 3 ? Tuple{CC.widenconst(CC.widenslotwrapper(argtypes[2])), T.parameters...} : T
    _fact_sig(sig) || return UNKNOWN
    world = CC.get_inference_world(interp)
    mi = ccall(:jl_method_lookup_by_tt, Any, (Any, Csize_t, Any), sig, world, nothing)
    mi isa Core.MethodInstance || return UNKNOWN
    nci = CC.typeinf_ext_toplevel(CC.NativeInterpreter(world), mi, CC.SOURCE_MODE_NOT_REQUIRED)
    nci isa Core.CodeInstance || return UNKNOWN
    CC.update_valid_age!(sv, CC.WorldRange(nci.min_world, nci.max_world))
    return CC.Future(CC.CallMeta(CC.Const(nci.rettype), Union{}, CC.Effects(CC.EFFECTS_TOTAL; nortcall = false), _NativeRT(sig, nci)))
end

const _ABSTRACT_SITE = CC.FailedMethodMatch("trait world: argument types not concrete, dispatched at run time")

function CC.find_method_matches(interp::FactsInterp, argtypes::Vector{Any}, @nospecialize(atype);
                                max_union_splitting::Int = CC.InferenceParams(interp).max_union_splitting,
                                max_methods::Int = CC.InferenceParams(interp).max_methods)
    𝕃 = CC.typeinf_lattice(interp)
    if !_FACTS_POLICY[] || (!isempty(argtypes) && _machinery_call(argtypes[1]))
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
    Base.invokelatest(CC.typeinf_ext_toplevel, FactsInterp(Base.tls_world_age()), mi, source_mode)
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
    return Base.invokelatest(CC.typeinf_ext_toplevel, FactsInterp(world), mi, CC.SOURCE_MODE_ABI)::Core.CodeInstance
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
The call is marked `@noinline`: Julia's inliner resolves `:invoke ci` by the method instance in
the caller's own cache, so a native caller would inline the worker's native code, and the edge
to that code would be dropped as a duplicate of `ci`'s (a stale-code hole, review of 2026-10-17).
A worker that calls its own function's entry again (recursion through an entry) would make the
generator infer the worker again while it is being inferred: on re-entry the call is left to run
time. Not a `CachedGenerator`: its result is generated again whenever the entry is inferred again.
"""
struct _FactsCallGen end
function (::_FactsCallGen)(world::UInt, source::Method, self, f, args)
    sig = Tuple{f, args...}
    as = Any[:(getfield(args, $i)) for i in 1:length(args)]
    active = get!(() -> Any[], task_local_storage(), :tw_facts_generating)::Vector{Any}
    if any(s -> s === sig, active)
        # recursion through an entry: the worker's code is being made; call it at run time
        call = :(Base.inferencebarrier(_facts_call)(f, $(as...)))
        lo, hi = UInt(1), typemax(UInt)
        edges = nothing
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
            lo, hi = lo_r[], hi_r[]
            edges = Core.svec(sig, ci)
        end
    end
    body = Expr(:block, Expr(:meta, :inline),
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
