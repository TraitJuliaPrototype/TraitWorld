"""
    TraitWorld

The trait language of the design (`writeup/design.md` in the design repository) as a package
on Julia with the facts mode (the patched build, julia-1.13): traits, implementations, keys, trait
modules, `Dynamic`, `Callable`, results like the input, definition checking, concrete mode,
`verify_main` and strict mode. Julia's compiler compiles a trait module by facts (`compiler.jl`):
its code depends on the method table only through facts at concrete signatures.
"""
module TraitWorld

using PrecompileTools: PrecompileTools
using Serialization: Serialization

export Trait, Callable, TObj, Dynamic, Compiled, compiled_for, with_dynamic,
       @trait, @implement, @trait_module, @workload,
       TraitBoundError, TraitUseError, ImplementError, OwnershipError, verify_main, isclosed,
       @warn_on_abstract, @error_on_abstract, AbstractTypeError, check_concrete, check_definitions, conforms, withfields,
       fully_typed, isfullytyped, FullyTypedReport, NotFullyTypedError

function __init__()
    empty!(_NOT_EXTENSIONS)
    _SESSION[] = (time_ns() ⊻ UInt(getpid()) << 32) | 1   # tables of untyped calls saved in images are ignored (untyped.jl)
    _hooks_init!()
    _strict_init!()
    _DEFCHECK_AT_END[] = get(ENV, "JULIA_TW_DEFCHECK", "1") != "0"
    _FACTS_DEBUG[] = get(ENV, "JULIA_TW_DEBUG", "0") == "1"
    push!(Base.package_callbacks, _on_package_load_callback)
    _register_type_printers()
    _install_frame_filter!()
    _install_error_hints!()
end

"The package callback."
function _on_package_load_callback(id::Base.PkgId)
    Base.invokelatest(_on_package_load, id)
    return nothing
end

"""
After a package load: the generation moves (a load can bring implementations
without running `@implement` here), and the overrides the image hook left
inactive are reported.
"""
function _on_package_load(id::Base.PkgId)
    _bump!()
    m = get(Base.loaded_modules, id, nothing)
    m isa Module || return nothing
    _note_checked_ahead!(m)
    _strict_known_delegates!()
    _report_refused_at_load()                                                # what the image hook left inactive
    return nothing
end

include("ownership.jl")
include("compiler.jl")
include("core.jl")
include("trait.jl")
include("implement.jl")
include("entry.jl")
include("attributes.jl")
include("trait_module.jl")
include("checks.jl")
include("untyped.jl")
include("ahead.jl")
include("verify.jl")
include("concrete.jl")
include("certificate.jl")
include("defcheck.jl")
include("hooks.jl")
# piece 5 for TraitWorld's own image: its workload compiles, by facts, the Base code its machinery's
# run-time sites reach (no backedge leads there): kept, else every session compiles it again (about
# 200 ms at the first `@implement`). `__init__` switches this on for the packages built after it.
if ccall(:jl_generating_output, Cint, ()) == 1 && get(ENV, "JULIA_TW_KEEP_COMPILED", "1") != "0" &&
        (try; cglobal(:jl_set_image_keep_compiled) != C_NULL; catch; false; end)
    ccall(:jl_set_image_keep_compiled, Cvoid, (Cint,), 1)
end
include("strict.jl")
include("frames.jl")
# the trait world's standard library: traits for Base's concepts (traits reference §18)
include("BaseTraits.jl")
using .BaseTraits
export BaseTraits, HasLength, Iterable, Indexable, MutableIndexable, Resizable, Keyed, DynamicItems, DynamicValues, retain!

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
@implement _PC.PCT _PCOne by data
struct _PCTwo; data::Vector{Float64}; end         # not implemented: the workload expands declarations for it

# a trait of declared fields only, and an implementation by forwarding: the paths of `@implement`
# that `_PC` does not reach (generic keys, ownership, field slots), so their code is in this image
@trait_module module _PCF
using ..TraitWorld
@trait PFT begin
    @const data::Vector{Float64}
end
pfsum(t::PFT) = sum(t.data)
end
struct _PCFA; label::String; data::Vector{Float64}; end
@implement _PCF.PFT _PCFA
mutable struct _PCFB; n::Int; data::Vector{Float64}; end
@implement _PCF.PFT _PCFB

PrecompileTools.@compile_workload begin
    v = [1.0, 2.0]
    _PCF.pfsum(_PCFA("a", v)); _PCF.pfsum(_PCFB(1, v))
    for x in Any[_PCFA("a", v), _PCFB(1, v)]; _PCF.pfsum(x); end
    _PC.pcsum(v); _PC.pcsum(_PCProj(v)); _PC.pcsum(_PCDyn(v)); _PC.pcsum(_PCOwn(2)); _PC.pcsum(_PCOne(v))
    # untyped calls: the table of declared implementations (untyped.jl), its slow path included
    for x in Any[v, _PCProj(v), _PCOwn(2), _PCOne(v)]; _PC.pcsum(x); end
    macroexpand(TraitWorld, :(@implement _PC.PCT _PCTwo by data))
    _PC.pcboth(v, _PCProj(v))
    _PC.pcmap(abs, v); _PC.pcmap(x -> 2x, _PCProj(v))
    macroexpand(_PC, :(@implement PCT{Vector{Int}} begin pn(r) = 1; pv(r, i) = 1.0 end))
    macroexpand(TraitWorld, :(@implement _PC.PCT _PCTwo project(t) = t.data))
    macroexpand(_PC, :(@trait Q{R} begin q(r::R)::Int; q2(r::R, i::Int)::Float64 = 1.0 end))
    macroexpand(_PC, :(f(t::PCT, i::Int) = pv(t, i)))
    conformance_problems(_PC.PCT, Vector{Float64}, (:pn, :pv))
    worker_problems(Tuple{typeof(_PC.pcsum),typeof(TObj((_selfview(_PC.PCT, Impl{(:pd,)}(), v),)))})
    # rule 3 per signature (Union members expanded)
    for m in methods(_PC.pv)
        owned_method(m)
    end
    _sig_alternatives(Tuple{typeof(sum),Union{Int,Float64},Union{Int,Float32},Union{Int8,Int16}})
    _sig_alternatives(Tuple{typeof(sum),Union{Int,Float64},Union{Int,Float32}})
    owned_method(first(methods(TraitWorld.owner)))
end
precompile(_on_package_load, (Base.PkgId,))
precompile(_narrow_slow, (Any, TObj))
precompile(_conf_family_slow, (Base.RefValue{IdDict{Any,Any}}, Any, Any))
precompile(_param_agrees, (Any, Symbol, Any, Any))   # a stated parameter's check, run by the declaration's top-level code

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


if ccall(:jl_generating_output, Cint, ()) == 1
    precompile(_on_image_methods_hook, (Vector{Any}, String))
    precompile(_on_method_definition_hook, (Method, Bool))
    precompile(_on_package_load_callback, (Base.PkgId,))
end

end
