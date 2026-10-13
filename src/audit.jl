# ---------------------------------------------------------------------------
# The error split on stock Julia, ported from TraitRegions (Stage 1). Every
# worker signature passes a guard (in `checked_call`) that audits its
# compiled code's concrete edges for piratical targets: methods whose package
# owns neither the function nor the types, in every signature they apply to.
# Three session-level modes:
#
#   :warn       (default on stock Julia) name each pirate once, then run on
#               top of it exactly as plain Julia does;
#   :error      the design's semantics: the call raises `PiracyError`;
#   :recompile  the opt-out: plain Julia, no audit.
#
# The audit runs at the first call of each signature and again after any
# world change, so whether it fires does not depend on workloads or load order.
# PoC limits (as in TraitRegions): stock Julia compiles against the whole
# method table, so the audit stands in for rule 6; a pirate reached only
# through a dynamic call is applied, as in plain Julia.
# ---------------------------------------------------------------------------

const MODE = Ref(:warn)
const SESSION = Ref{UInt}(0)

"""
    TraitWorld.mode!(:warn | :error | :recompile)

The session's reaction to piracy against trait-bound code. Also settable at
startup with the environment variable `JULIA_TRAITWORLD`.
"""
function mode!(m::Symbol)
    m in (:warn, :error, :recompile) || throw(ArgumentError("mode must be :warn, :error or :recompile, got :$m"))
    MODE[] = m
    SESSION[] += 1
    return m
end

struct PiracyFinding
    method::Method      # the piratical method trait-bound code would call
    sig::Any            # the concrete call it intercepts
    caller::Any         # the MethodInstance whose compiled code holds the call
end

"""
    PiracyError

Raised (in `:error` mode) when trait-bound code would run on top of a method
defined by a package that owns neither the function nor its argument types.
`catch` blocks inside trait modules rethrow it.
"""
struct PiracyError <: Exception
    sig::Any
    findings::Vector{PiracyFinding}
end
PiracyError(msg::String) = PiracyError(msg, PiracyFinding[])
function Base.showerror(io::IO, e::PiracyError)
    print(io, "PiracyError: trait-bound code ", e.sig, " depends on ",
          length(e.findings) == 1 ? "a method" : "methods",
          " defined by a package that owns neither the function nor its argument types:")
    for f in e.findings
        print(io, "\n  ", f.method, "  [defined by ", owner(f.method.module), "]",
              "\n    intercepts ", f.sig, "\n    called from ", f.caller)
    end
    print(io, "\nRemove the pirate, or opt out with TraitWorld.mode!(:recompile).")
end

"Per-signature guard state, embedded in `checked_call`'s compiled code."
mutable struct GuardState
    session::UInt
    world::UInt
    warned::Base.IdSet{Method}
end
GuardState() = GuardState(typemax(UInt), UInt(0), Base.IdSet{Method}())

@inline function _guard(st::GuardState, @nospecialize(sig))
    MODE[] === :recompile && return nothing
    st.session == SESSION[] && st.world == Base.get_world_counter() && return nothing
    return Base.inferencebarrier(_guard_slow)(st, sig)
end

@noinline function _guard_slow(st::GuardState, @nospecialize(sig))
    findings = @lock _LOCK audit(sig)
    if !isempty(findings)
        MODE[] === :error && throw(PiracyError(sig, findings))      # stays poisoned: not stamped
        for f in findings
            f.method in st.warned && continue
            push!(st.warned, f.method)
            @warn sprint(showerror, PiracyError(sig, [f])) * "\n(warn mode: running on top of the pirate, as plain Julia does)"
        end
    end
    st.session = SESSION[]
    st.world = Base.get_world_counter()
    return nothing
end

# --- the audit ----------------------------------------------------------------

const _CLEAN = Base.IdSet{Core.CodeInstance}()
const _PIRATICAL = IdDict{Method,Bool}()

"Piratical under rule 5 (per signature, so a `Union` is no way around it), unless an implementer relation is declared."
_piratical(m::Method) = get!(() -> !owned_method(m) && !_implements_exempt(m), _PIRATICAL, m)
function _implements_exempt(m::Method)
    definer = owner(m.module)
    definer isa Module || return false
    impl = Base.inferencebarrier(implements)(definer)::Vector{Symbol}
    return any(o -> o isa Module && nameof(o) in impl, sig_owners(m.sig))
end

_isvalid(ci::Core.CodeInstance, world::UInt) = ci.min_world <= world <= ci.max_world

function _latest_ci(mi::Core.MethodInstance)
    isdefined(mi, :cache) || return nothing
    ci = mi.cache
    while true
        ci.owner === nothing && return ci
        isdefined(ci, :next) || return nothing
        ci = ci.next
    end
end
function _valid_ci(mi::Core.MethodInstance, world::UInt)
    isdefined(mi, :cache) || return nothing
    ci = mi.cache
    while true
        ci.owner === nothing && _isvalid(ci, world) && return ci
        isdefined(ci, :next) || return nothing
        ci = ci.next
    end
end
_callee_method(@nospecialize(c)) =
    c isa Core.CodeInstance ? c.def.def :
    c isa Core.MethodInstance ? c.def :
    c isa Method ? c : nothing
function _current_target(@nospecialize(sig), world::UInt)
    m = Base._which(sig; world, raise = false)
    return m === nothing ? nothing : m.method
end

"""
    audit(sig) -> Vector{PiracyFinding}

Walk the concrete edges of the compiled code for the call signature `sig`
(a worker's) and report every concrete call whose target is piratical.
Invalidated code is re-resolved in the current world, so a pirate that just
invalidated the worker is found without recompiling it.
"""
function audit(@nospecialize(sig); compile::Bool = true)
    world = Base.get_world_counter()
    mi = try
        Base.specialize_method(Base._which(sig; world))
    catch
        nothing
    end
    mi isa Core.MethodInstance || return PiracyFinding[]
    ci = _latest_ci(mi)
    if MODE[] === :error && ci !== nothing && !_isvalid(ci, world)
        findings = _walk(ci, world)
        isempty(findings) || return findings
    end
    ci = _valid_ci(mi, world)
    if ci === nothing
        compile || return PiracyFinding[]
        ccall(:jl_compile_hint, Int32, (Any,), sig)
        ci = _valid_ci(mi, world)
        ci === nothing && return PiracyFinding[]
    end
    return _walk(ci, world)
end

function _walk(ci0::Core.CodeInstance, world::UInt)
    findings = PiracyFinding[]
    seen = Base.IdSet{Core.CodeInstance}()
    stack = Core.CodeInstance[ci0]
    while !isempty(stack)
        ci = pop!(stack)
        ci in seen && continue
        push!(seen, ci)
        valid = _isvalid(ci, world)
        valid && ci in _CLEAN && continue
        caller = ci.def
        e = ci.edges
        i = 1
        while i <= length(e)
            it = e[i]
            if it isa Int
                n = abs(it)
                sig = e[i+1]
                for j in 1:n
                    _edge!(findings, stack, sig, e[i+1+j], caller, valid, world)
                end
                i += 2 + n
            elseif it isa Type
                nxt = e[i+1]
                if nxt isa Core.MethodTable
                    _mt_edge!(findings, it, caller, world)
                else
                    _edge!(findings, stack, it, nxt, caller, valid, world)
                end
                i += 2
            elseif it isa Core.CodeInstance || it isa Core.MethodInstance
                mi = it isa Core.CodeInstance ? it.def : it
                _edge!(findings, stack, mi.specTypes, it, caller, valid, world)
                i += 1
            else
                i += 1
            end
        end
    end
    if isempty(findings)
        for ci in seen
            _isvalid(ci, world) && push!(_CLEAN, ci)
        end
    end
    return findings
end

function _edge!(findings, stack, @nospecialize(sig), @nospecialize(callee), @nospecialize(caller), valid::Bool, world::UInt)
    if sig isa Type && Base.isdispatchtuple(sig)
        m = valid ? _callee_method(callee) : _current_target(sig, world)
        if m isa Method && _piratical(m)
            push!(findings, PiracyFinding(m, sig, caller))
        end
    end
    if callee isa Core.CodeInstance
        push!(stack, callee)
    elseif callee isa Core.MethodInstance
        c = _latest_ci(callee)
        c === nothing || push!(stack, c)
    end
    return nothing
end

function _mt_edge!(findings, @nospecialize(sig), @nospecialize(caller), world::UInt)
    sig isa Type && Base.isdispatchtuple(sig) || return nothing
    m = _current_target(sig, world)
    if m isa Method && _piratical(m)
        push!(findings, PiracyFinding(m, sig, caller))
    end
    return nothing
end
