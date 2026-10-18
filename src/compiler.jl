# ---------------------------------------------------------------------------
# The facts mode is Julia's (julia-1.13, Compiler/src/facts.jl; writeup/design.md §6): a trait
# module is compiled by facts under the cache owner `:facts` (`@compiler_options facts=true`,
# which `@trait_module` declares), entries are boundaries compiled in their caller's mode
# (`Expr(:meta, :facts, 0)`), and code compiled by facts dispatches at run time to code compiled
# by facts. What TraitWorld keeps here: the definition checks' interpreter, the world decisions are
# made in, and the facts rule's signature test (the compiler's, one source of truth).
# ---------------------------------------------------------------------------

const CC = Base.Compiler

isdefined(CC, :FACTS_OWNER) ||
    error("TraitWorld needs Julia's facts mode: the patched build in julia-1.13 (stock Julia is not supported)")

"The cache owner of code compiled by facts (Julia's)."
const FACTS_OWNER = CC.FACTS_OWNER

"Whether a signature is a fact: only stakeholders or pirates can change dispatch at it (the compiler's test)."
_fact_sig(@nospecialize(s)) = CC.is_fact_sig(s)
"The concrete signatures a fact signature stands for (its splits), or the signature itself."
function _fact_splits(@nospecialize(s))
    ss = CC.concrete_splits(s)
    return ss === nothing ? Any[s] : ss
end

"The cache owner of the definition checks' inference: none of their results reaches the code that runs."
struct _CheckOwner end
"""
The interpreter of the definition checks (return types, kept trait objects): plain inference
rules, in its own cache, so that checking a worker before any value exists compiles nothing the
program runs.
"""
struct _CheckInterp <: CC.AbstractInterpreter
    world::UInt
    inf_params::CC.InferenceParams
    opt_params::CC.OptimizationParams
    inf_cache::Vector{CC.InferenceResult}
    codegen::IdDict{Core.CodeInstance,Core.CodeInfo}
end
_check_interp(world::UInt = Base.get_world_counter()) =
    _CheckInterp(world, CC.InferenceParams(), CC.OptimizationParams(), CC.InferenceResult[], IdDict{Core.CodeInstance,Core.CodeInfo}())
CC.InferenceParams(i::_CheckInterp) = i.inf_params
CC.OptimizationParams(i::_CheckInterp) = i.opt_params
CC.get_inference_world(i::_CheckInterp) = i.world
CC.get_inference_cache(i::_CheckInterp) = i.inf_cache
CC.cache_owner(::_CheckInterp) = _CheckOwner()
CC.codegen_cache(i::_CheckInterp) = i.codegen
"Keywords for reflection by the definition checks: their own interpreter."
_check_kw(world::UInt = Base.get_world_counter()) = (; world, interp = _check_interp(world))

"A `CodeInstance`'s inferred result type (as the compiler decodes it: a lattice element may be stored)."
function _ci_return_type(ci::Core.CodeInstance)
    r = CC.cached_return_type(ci)
    return r isa CC.Const ? Core.Typeof(r.val) : CC.widenconst(r)
end

"Print the machinery's slow paths as they run (`JULIA_TW_DEBUG=1`)."
const _FACTS_DEBUG = Ref(false)

"""
    _latest(f, args...)

A slow path of the machinery (finding a conformance's builder, the checks at a signature's first
call), run in the latest world: TraitWorld's own code is plain Julia.
"""
_latest(f, args...) = Base.invokelatest(f, args...)

"""
The world the machinery decides conformances in: the caller's (`tls_world_age()` where an entry's
slow path starts), as plain Julia dispatches in the caller's world. A task pinned to an older world
then sees the conformances of its world, not of the latest. Outside a decision, the latest world.
"""
const _DECISION_WORLD = Base.ScopedValues.ScopedValue{UInt}(UInt(0))
_decision_world() = (w = _DECISION_WORLD[]; w == 0 ? Base.get_world_counter() : w)
_in_decision_world(f, args...) =
    (w = _DECISION_WORLD[]; w == 0 ? Base.invokelatest(f, args...) : Base.invoke_in_world(w, f, args...))
"`_latest` in world `w`, deciding in `w`."
_in_world(w::UInt, f, args...) = Base.ScopedValues.with(_DECISION_WORLD => w) do
    Base.invoke_in_world(w, f, args...)
end
