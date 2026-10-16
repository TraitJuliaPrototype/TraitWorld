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
constant. Inference types the call by `ci`'s result type and records one edge, to `ci` alone
(`InvokeCICallInfo`): the entry is invalidated exactly when the worker's code under the policy is
(a fact broken, the method replaced), never by the native code of the same method instance. The
call is marked `@noinline`: Julia's inliner resolves `:invoke ci` by the method instance in the
caller's own cache, so a native caller would inline the worker's native code (sound, since its
edge is then to that code, but with abstract edges again).
Not a `CachedGenerator`: its result is generated again whenever the entry is inferred again.
"""
struct _FactsCallGen end
function (::_FactsCallGen)(world::UInt, source::Method, self, f, args)
    sig = Tuple{f, args...}
    as = Any[:(getfield(args, $i)) for i in 1:length(args)]
    ci = facts_codeinstance(sig, world)
    _FACTS_DEBUG[] && println(stderr, "facts entry: ", sig, " in world ", world)
    # no method: the plain call, which raises the plain `MethodError`
    call = ci === nothing ? :(f($(as...))) : :(Core.invoke(f, $ci, $(as...)))
    body = Expr(:block, Expr(:meta, :noinline),
                Expr(:noinline, true), Expr(:local, Expr(:(=), :val, call)), Expr(:noinline, false),
                Expr(:return, :val))
    lam = Expr(:lambda, Any[Symbol("#self#"), :f, :args], Expr(:var"scope-block", body))
    return Base.generated_body_to_codeinfo(lam, @__MODULE__, true)
end

@eval function _facts_call(f, args...)
    $(Expr(:meta, :generated, _FactsCallGen()))
    $(Expr(:meta, :generated_only))
end
"""
    _facts_call(f, args...)

The call of a worker under the policy, made by `checked_call`: a direct call of its CodeInstance
compiled under the policy (see `_FactsCallGen`), typed by that code's result type. Not inlined,
so that `verify_main` sees one call whose targets are the worker's.
"""
_facts_call
