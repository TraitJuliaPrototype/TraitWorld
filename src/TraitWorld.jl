"""
    TraitWorld

A proof of concept of the design note "Traits for better Julia": trait
modules, traits over a representation parameter, implementations and
projections. What library code may do with a trait object (rule 2) and
ownership of the methods a trait module defines (rule 3) are checked when
code is defined. Code written without traits is wrapped by facts: trait-world
code may call any Julia code, and its workers are compiled under the trait
world's compiler policy (`facts.jl`), so that only concrete facts decide their
compiled code and Julia's own invalidation keeps it valid.
"""
module TraitWorld

using PrecompileTools: PrecompileTools
using Serialization: Serialization

export Trait, Callable, CallMode, DynamicCall, CompiledCall, compiled_call, dynamic_call, TObj, Dynamic, DynamicFn, dynamic_fn,
       @trait, @implement, @trait_module, @workload,
       TraitBoundError, TraitUseError, ImplementError, OwnershipError, verify_main, isclosed,
       viewcache_flush,
       @warn_on_abstract, @error_on_abstract, AbstractTypeError, check_concrete, check_definitions, conforms, withfields

function __init__()
    empty!(_NOT_EXTENSIONS)
    FACTS[] = get(ENV, "JULIA_TW_FACTS", "1") != "0"
    _vc_init!()
    _hooks_init!()
    _strict_init!()
    _FACTS_POLICY[] = get(ENV, "JULIA_TW_FACTS_POLICY", "1") != "0"
    _FACTS_DEBUG[] = get(ENV, "JULIA_TW_FACTS_DEBUG", "0") == "1"
    _COMPILER_WORLD[] = Base.get_world_counter()
    _INLINER_KEEPS_CI[] = _inliner_keeps_ci() && get(ENV, "JULIA_TW_NOINLINE", "0") != "1"
    push!(Base.package_callbacks, _on_package_load)
    _register_type_printers()
end

"""
After a package load: the generation moves (a load can bring projections and
implementations without running `@implement` here), the overrides the image hook
left inactive are reported, and once per top-level `using` the view caches of
what is loaded now are read.
"""
function _on_package_load(id::Base.PkgId)
    _bump!()
    m = get(Base.loaded_modules, id, nothing)
    m isa Module || return nothing
    _strict_known_delegates!()
    _report_refused_at_load()                                                # what the image hook left inactive (patched Julia)
    Base.toplevel_load[] && Base.inferencebarrier(_vc_load!)()               # the view caches of what is loaded now
    return nothing
end

include("ownership.jl")
include("facts.jl")
include("core.jl")
include("trait.jl")
include("implement.jl")
include("entry.jl")
include("trait_module.jl")
include("checks.jl")
include("verify.jl")
include("concrete.jl")
include("viewcache.jl")
include("defcheck.jl")
include("hooks.jl")
include("strict.jl")

# ---------------------------------------------------------------------------
# Precompile the machinery itself: macro expansion, registration, checks,
# entries and erasure, so that implementing a trait in a fresh session costs
# the user's own code and little else. Private trait module and types.
# ---------------------------------------------------------------------------

@trait_module module _PC
using ..TraitWorld
@trait PCT{R} begin
    pn(r::R)::Int
    pv(r::R, i::Int)::Float64
    pd(r::R)::Float64 = pv(r, 1)
end
@implement PCT{Vector{Float64}} begin
    pn(r) = length(r)
    pv(r, i) = r[i]
end
pcsum(t::PCT) = (s = 0.0; for i in 1:pn(t); s += pv(t, i); end; s + pd(t))
pcmap(f::Callable{Tuple{Float64},Float64}, t::PCT) = f(pv(t, 1))
pcboth(a::PCT, b::PCT) = pcsum(a) - pcsum(b)
end

struct _PCProj; v::Vector{Float64}; end
@implement _PC.PCT _PCProj project(t) = t.v
struct _PCDyn; v::Vector{Float64}; end
@implement _PC.PCT _PCDyn dynamic begin
    project(t) = t.v
    pn(r) = length(r)
    pv(r, i) = r[end - i + 1]
end
struct _PCOwn; n::Int; end
@implement _PC.PCT{_PCOwn} begin
    pn(r) = r.n
    pv(r, i) = Float64(i)
end
struct _PCOne; data::Vector{Float64}; end
@implement _PC.PCT _PCOne

PrecompileTools.@compile_workload begin
    v = [1.0, 2.0]
    _PC.pcsum(v); _PC.pcsum(_PCProj(v)); _PC.pcsum(_PCDyn(v)); _PC.pcsum(_PCOwn(2)); _PC.pcsum(_PCOne(v))
    macroexpand(TraitWorld, :(@implement _PC.PCT _PCOne))
    _PC.pcboth(v, _PCProj(v))
    _PC.pcmap(abs, v); _PC.pcmap(x -> 2x, _PCProj(v))
    macroexpand(_PC, :(@implement PCT{Vector{Int}} begin pn(r) = 1; pv(r, i) = 1.0 end))
    macroexpand(TraitWorld, :(@implement _PC.PCT _PCProj by v))
    macroexpand(_PC, :(@trait Q{R} begin q(r::R)::Int; q2(r::R, i::Int)::Float64 = 1.0 end))
    macroexpand(_PC, :(f(t::PCT, i::Int) = pv(t, i)))
    conformance_problems(_PC.PCT, Vector{Float64}, (:pn, :pv))
    worker_problems(Tuple{typeof(_PC.pcsum),typeof(TObj((View{_PC.PCT}(Impl{(:pd,)}(), v),)))})
    # rule 3 per signature (Union members expanded)
    for m in methods(_PC.pv)
        owned_method(m)
    end
    _sig_alternatives(Tuple{typeof(sum),Union{Int,Float64},Union{Int,Float32},Union{Int8,Int16}})
    _sig_alternatives(Tuple{typeof(sum),Union{Int,Float64},Union{Int,Float32}})
    owned_method(first(methods(TraitWorld.owner)))
end
precompile(_on_package_load, (Base.PkgId,))
precompile(_vc_load!, ())
precompile(viewcache_flush, ())

"""
    @workload begin … end

A precompile workload for a trait module (`PrecompileTools.@compile_workload`,
reached through TraitWorld so that the trait module imports only the trait world).
"""
macro workload(ex)
    # the module's entry positions are fixed first, so the workload compiles the entries as they stay
    fin = isdefined(__module__, :__tw_positions__) ? :($TraitWorld._finish_needed(@__MODULE__)) : nothing
    return esc(Expr(:block, fin, Expr(:macrocall, GlobalRef(PrecompileTools, Symbol("@compile_workload")), __source__, ex)))
end
"Fix `needed` for a trait module's entry positions now (before a workload), as `_finish_module` will."
function _finish_needed(mod::Module)
    for (f, pos, nargs) in mod.__tw_positions__
        _fix_needed!(mod, f, pos, nargs)
    end
    for f in unique(Any[x[1] for x in mod.__tw_positions__])
        _fix_keeps!(mod, f)
    end
    mod.__tw_finished__[] = true
    return nothing
end


# the compiler's specializations for the policy's interpreter (facts.jl), compiled into this image:
# without them a session's first trait call compiles the compiler for `FactsInterp` (about 11 s)
_facts_warm(x::Vector{Float64}) = sum(x) / length(x)
if ccall(:jl_generating_output, Cint, ()) == 1
    _facts_call(_facts_warm, [1.0, 2.0])
    # the machinery's slow paths under the policy (`_latest_under_policy`), compiled into this
    # image: their arguments are `@nospecialize`d, so one CodeInstance serves every signature
    for sig in (Tuple{typeof(_check_once), Base.RefValue{Bool}, DataType},
                Tuple{typeof(_builder_for), Vector{Any}, DataType},
                Tuple{typeof(worker_problems), DataType},
                Tuple{typeof(_check_concrete), DataType},
                Tuple{typeof(_finish_module), Module})
        facts_codeinstance(sig)
    end
end

end
