"""
    TraitWorld

A proof of concept of the design note "Traits for better Julia": trait
modules, traits over a representation parameter, implementations and
projections, layering (rule 1) and ownership (rule 5) checked when code is
defined.
"""
module TraitWorld

using PrecompileTools: PrecompileTools

export Trait, Callable, TObj, @trait, @implement, @trait_module, @workload,
       TraitBoundError, TraitUseError, ImplementError, LayeringError, OwnershipError, PiracyError

include("ownership.jl")
include("core.jl")
include("audit.jl")
include("trait.jl")
include("implement.jl")
include("entry.jl")
include("trait_module.jl")
include("checks.jl")

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

PrecompileTools.@compile_workload begin
    v = [1.0, 2.0]
    _PC.pcsum(v); _PC.pcsum(_PCProj(v)); _PC.pcsum(_PCDyn(v)); _PC.pcsum(_PCOwn(2))
    _PC.pcboth(v, _PCProj(v))
    _PC.pcmap(abs, v); _PC.pcmap(x -> 2x, _PCProj(v))
    macroexpand(_PC, :(@implement PCT{Vector{Int}} begin pn(r) = 1; pv(r, i) = 1.0 end))
    macroexpand(_PC, :(@implement PCT Int project(t) = [1.0]))
    macroexpand(_PC, :(@trait Q{R} begin q(r::R)::Int; q2(r::R, i::Int)::Float64 = 1.0 end))
    macroexpand(_PC, :(f(t::PCT, i::Int) = pv(t, i)))
    conformance_problems(_PC.PCT, Vector{Float64}, (:pn, :pv))
    worker_problems(Tuple{typeof(_PC.pcsum),typeof(TObj((View{_PC.PCT}(Impl{(:pd,)}(), v),)))})
end

"""
    @workload begin … end

A precompile workload for a trait module (`PrecompileTools.@compile_workload`,
reached through TraitWorld so that the trait module imports only the trait world).
"""
macro workload(ex)
    return esc(Expr(:macrocall, GlobalRef(PrecompileTools, Symbol("@compile_workload")), __source__, ex))
end

end
