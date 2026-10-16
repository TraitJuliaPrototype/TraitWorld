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
    facts_codeinstance(sig) -> CodeInstance

The CodeInstance compiled under the trait world's policy for the call signature `sig`
(`Tuple{typeof(f), argument types...}`), valid in the current world.
"""
function facts_codeinstance(@nospecialize(sig))
    world = Base.tls_world_age()
    mi = ccall(:jl_method_lookup_by_tt, Any, (Any, Csize_t, Any), sig, world, nothing)
    mi isa Core.MethodInstance || throw(MethodError(sig.parameters[1], Tuple{sig.parameters[2:end]...}, world))
    return Base.invokelatest(CC.typeinf_ext_toplevel, FactsInterp(world), mi, CC.SOURCE_MODE_ABI)::Core.CodeInstance
end

"Whether entries call workers through the trait world's policy (`JULIA_TW_FACTS=0` turns it off)."
const FACTS = Ref(false)
const _FACTS_OC = Ref(true)
const _FACTS_POLICY = Ref(true)          # false: the own cache under Julia's own policy (for diagnosis)
const _FACTS_DEBUG = Ref(false)

"""
A worker's code under the policy, for one call signature: its CodeInstance (whose validity decides
whether the entry is current, and whose machine code a package image may hold), and, once the
signature is hot, an opaque closure compiled in this session from the same optimized IR, which an
entry calls through its specialized calling convention. Before that, the entry calls the
CodeInstance's own machine code through its boxed calling convention (`_facts_invoke`). The
entry lives in the generated code of `_facts_call`, so a package image may hold it: an entry from
another session (`session`) is made again, its closure never used.
"""
mutable struct FactsEntry
    const ci::Core.CodeInstance
    oc::Any
    session::UInt
    calls::Int
end
const _SESSION = Ref{UInt}(0)
"Calls of a signature after which its entry compiles an opaque closure."
const FACTS_HOT = Ref(1000)

"The entry in `cache` if its CodeInstance is valid in the current world, else a new one stored there."
@inline function _facts_entry(cache::Base.RefValue{Any}, @nospecialize(sig))
    e = cache[]
    if e isa FactsEntry && e.session == _SESSION[]      # an entry from an image is looked up again (and its code compiled if the image has none)
        ci = e.ci
        w = Base.tls_world_age()
        (ci.min_world <= w <= ci.max_world) && return e
    end
    return Base.inferencebarrier(_facts_entry_slow)(cache, sig)::FactsEntry
end
@noinline function _facts_entry_slow(cache::Base.RefValue{Any}, @nospecialize(sig))
    ci = facts_codeinstance(sig)
    _FACTS_DEBUG[] && println(stderr, "facts entry: ", sig)
    e = FactsEntry(ci, nothing, _SESSION[], 0)
    cache[] = e
    return e
end
"After `FACTS_HOT[]` calls: the opaque closure for the entry (or none, then never again)."
@noinline function _facts_hot!(e::FactsEntry, @nospecialize(sig), @nospecialize(RT))
    e.oc = _FACTS_OC[] ? (try
        _facts_oc(sig, RT, e.ci.min_world)
    catch
        nothing
    end) : nothing
    _FACTS_DEBUG[] && println(stderr, "facts closure: ", sig, " => ", e.oc === nothing ? "none" : "closure")
    return nothing
end
"Call a CodeInstance's machine code through its boxed calling convention, without `invoke`'s checks (its signature is the call's)."
@inline function _facts_invoke(f, ci::Core.CodeInstance, args...)
    p = ci.invoke
    p == C_NULL && return invoke(f, ci, args...)
    as = Any[args...]
    return GC.@preserve as ccall(p, Any, (Any, Ptr{Any}, UInt32, Any), f, pointer(as), length(as) % UInt32, ci)
end

function _uses_self(ir)
    for st in ir.stmts.stmt
        st isa Expr || continue
        for a in st.args
            a isa Core.Argument && a.n == 1 && return true
        end
    end
    return false
end

function _facts_oc(@nospecialize(sig), @nospecialize(RT), world::UInt)
    world = Base.tls_world_age()
    mi = ccall(:jl_method_lookup_by_tt, Any, (Any, Csize_t, Any), sig, world, nothing)::Core.MethodInstance
    m = mi.def::Method
    res = Base.code_ircode_by_type(sig; world, interp = FactsInterp(world))
    length(res) == 1 || return nothing
    ir, rt = res[1]
    ir isa CC.IRCode || return nothing
    rt <: RT || return nothing
    _uses_self(ir) && return nothing
    ir = CC.copy(ir)
    ir.argtypes[1] = Tuple{}
    nargtypes = length(ir.argtypes)
    src = ccall(:jl_new_code_info_uninit, Ref{Core.CodeInfo}, ())
    src.slotnames = fill(:none, nargtypes)
    src.slotflags = fill(zero(UInt8), nargtypes)
    src.slottypes = copy(ir.argtypes)
    src.min_world = ir.valid_worlds.min_world
    src.max_world = ir.valid_worlds.max_world
    src.isva = m.isva
    src.nargs = UInt(nargtypes)
    src = CC.ir_to_codeinf!(src, ir)
    src.rettype = RT
    A = Tuple{sig.parameters[2:end]...}
    return Base.Experimental.generate_opaque_closure(A, Union{}, RT, src, nargtypes - 1, m.isva)
end

"""
    _facts_call(f, args...)

The call of a worker under the policy, made by `checked_call`: through the opaque closure of its
`FactsEntry` (one per call signature), or `invoke` of its CodeInstance; the result typed as plain
Julia infers it. Not inlined, so that `verify_main` sees one call whose targets are the worker's.
"""
@generated function _facts_call(f, args...)
    cache = Ref{Any}(nothing)
    sig = Tuple{f,args...}
    A = Tuple{args...}
    as = [:(args[$i]) for i in 1:length(args)]
    return quote
        $(Expr(:meta, :noinline))
        RT = $(Core.Compiler.return_type)(f, $A)
        e = _facts_entry($cache, $sig)
        oc = e.oc
        oc isa Core.OpaqueClosure{$A,RT} && return oc($(as...))::RT
        n = e.calls += 1
        n == FACTS_HOT[] && Base.inferencebarrier(_facts_hot!)(e, $sig, RT)
        return _facts_invoke(f, e.ci, $(as...))::RT
    end
end
