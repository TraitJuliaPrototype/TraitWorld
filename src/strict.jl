# ---------------------------------------------------------------------------
# Strict mode (writeup/explorations/strict-mode.md): defining a winning pirate is an error.
# A method definition is refused when it is a pirate (rule 3: its package does not own the
# function or a type in every signature it applies to; an extension counts as its parent), it
# would win at a concrete signature where valid trait-world code holds a fact (Julia would
# invalidate that code because of it), and its package is not a declared delegate of an owner of
# that signature. Trait-world
# code is then never invalidated by a pirate; stakeholders' definitions are followed as before.
# Nothing changes at run time: the check runs only when a method is defined.
#
# Needs the definition hooks of the patched runtime (piece 1). The check before a definition
# reads Julia's backedges (a stand-in for piece 14, a read-only "would invalidate" query); after
# the definition, Julia's invalidation log is read as a safety net: a trait-world CodeInstance
# invalidated by a non-stakeholder means the check missed a case, and the method is deleted again.
# ---------------------------------------------------------------------------

"Whether strict mode is on (`JULIA_TW_STRICT=1`, or `strict!()`)."
const STRICT = Ref(false)
"Turn strict mode on or off for this session."
strict!(on::Bool = true) = (STRICT[] = on; nothing)

"Delegates: an implementation package that counts as a stakeholder wherever the package it implements is (`delegate!(StaticArraysCore => StaticArrays)`)."
const DELEGATES = IdDict{Any,Vector{Any}}()        # implemented package's owner => delegates' owners
delegate!(p::Pair{Module,Module}) = (push!(get!(() -> Any[], DELEGATES, owner(p.first)), owner(p.second)); nothing)
"Split-core pairs known to TraitWorld, by package name (core => implementation)."
const KNOWN_DELEGATES = [("StaticArraysCore", "StaticArrays"), ("StatsAPI", "StatsBase"), ("MakieCore", "Makie"),
                         ("ChainRulesCore", "ChainRules"), ("SciMLBase", "OrdinaryDiffEq"), ("ArrayInterfaceCore", "ArrayInterface")]

"""
    PirateError

Strict mode: a definition was refused because it would change trait-world code (`sig`, compiled in
`caller`) and its package owns neither the function nor a type in the signature.
"""
struct PirateError <: Exception
    method::Method
    definer::Any
    sig::Any
    caller::Any
    later::Bool                  # found only after the definition (the method was deleted again)
end
function Base.showerror(io::IO, e::PirateError)
    print(io, "PirateError: strict mode refuses ", e.method, ", defined by ", e.definer,
          ": it would change what trait-world code computes at ", e.sig, " (", e.caller, "), and ",
          e.definer, " owns neither the function nor a type in that signature. ",
          "Turn strict mode off (`TraitWorld.strict!(false)`) to follow it as plain Julia does",
          ", or declare the package a delegate of the owner it implements (`TraitWorld.delegate!(Core => Impl)`).")
    e.later && print(io, " (found after the definition by the safety net; the method was deleted again)")
end

"Code the mode protects: compiled under the facts policy, or a trait module's (an entry)."
function _trait_world_code(ci::Core.CodeInstance)
    ci.owner isa FactsOwner && return true
    ci.owner === nothing || return false
    mi = Core.Compiler.get_ci_mi(ci)
    return mi.def isa Method && is_trait_world(mi.def.module)
end

"Whether `definer` is a stakeholder of the concrete signature `s` (or a delegate of one)."
function _stakeholder(@nospecialize(definer), @nospecialize(s))
    os = sig_owners(s)
    definer in os && return true
    for o in os
        ds = get(DELEGATES, o, nothing)
        ds !== nothing && definer in ds && return true
    end
    return false
end

"Whether the new method `m` would be selected at the concrete signature `s`: it applies, and no current method beats it (it fills a gap, is more specific, replaces, or makes the call ambiguous)."
function _would_win(m::Method, @nospecialize(s), world::UInt)
    s <: m.sig || return false
    ms = Base._methods_by_ftype(s, nothing, 1, world, false, Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
    (ms isa Vector && length(ms) == 1) || return true             # no method, or ambiguous already: m changes it
    cur = (ms[1]::Core.MethodMatch).method
    cur === m && return false
    return ccall(:jl_type_morespecific, Cint, (Any, Any), cur.sig, m.sig) == 0
end

"The first fact of valid trait-world code that `m`, defined by a non-stakeholder, would break: `(sig, caller)`, or `nothing`."
function _strict_violation(m::Method)
    definer = owner(m.module)
    definer === :Julia && return nothing               # Julia is one owner, and owns its own functions
    _strict_owned(m) && return nothing
    # an owned method (rule 3: its package owns the function or a type in every signature it
    # applies to, an abstract type included) is no pirate, wherever it wins: by Lemma O only
    # pirates need the walk, and they are few (a package image's methods are nearly all owned)
    owned_method(m) && return nothing
    world = Base.get_world_counter()
    check(s, caller) = caller isa Core.CodeInstance && caller.max_world == typemax(UInt) && _trait_world_code(caller) &&
                       _fact_sig(s) && _would_win(m, s, world) && !_stakeholder(definer, s)
    # 1. calls that dispatch to an existing method's specializations, where m would win
    ms = Base._methods_by_ftype(m.sig, nothing, -1, world, false, Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
    if ms isa Vector
        for mm in ms
            old = (mm::Core.MethodMatch).method
            old === m && continue
            ccall(:jl_type_morespecific, Cint, (Any, Any), old.sig, m.sig) != 0 && continue   # old always beats m
            for mi in Base.specializations(old)
                mi isa Core.MethodInstance || continue
                isdefined(mi, :backedges) || continue
                be = mi.backedges
                i = 1
                while i <= length(be)
                    x = be[i]
                    if x isa Type
                        i + 1 <= length(be) || break
                        s, caller = x, be[i+1]; i += 2
                    else
                        s, caller = mi.specTypes, x; i += 1
                    end
                    check(s, caller) && return (s, caller)
                end
            end
        end
    else
        return nothing        # too many matches to list: the safety net decides
    end
    # 2. calls that found no method (a gap the new method would fill)
    body = Base.unwrap_unionall(m.sig)
    if body isa DataType && !isempty(body.parameters)
        ft = body.parameters[1]
        tn = ft isa DataType ? ft.name : nothing
        be = getfield(Core.methodtable, :backedges)
        for i in 1:2:length(be)-1
            isassigned(be, i) || continue
            be[i] === tn || continue
            isassigned(be, i + 1) || continue
            v = be[i+1]
            v isa Vector{Any} || continue
            for j in 1:2:length(v)-1
                check(v[j], v[j+1]) && return (v[j], v[j+1])
            end
        end
    end
    return nothing
end

# --- the safety net: Julia's own invalidation log around a definition ---------------------

const _STRICT_LOG = Ref{Any}(nothing)
const _STRICT_MISSES = Any[]                         # (method, sig, caller) found only by the safety net
_strict_log_start!() = (_STRICT_LOG[] = ccall(:jl_debug_method_invalidation, Any, (Cint,), 1); nothing)
function _strict_log_stop!()
    log = _STRICT_LOG[]
    _STRICT_LOG[] = nothing
    ccall(:jl_debug_method_invalidation, Any, (Cint,), 0)
    return log
end
"""
After `m` is visible: Julia's log of what it invalidated. If trait-world code was invalidated and
`m`'s package holds no stake in a signature whose dispatch it changed, the check before the
definition missed a case: delete `m` again and raise (counted in `_STRICT_MISSES`).
"""
function _strict_after!(m::Method)
    log = _strict_log_stop!()
    log isa Vector || return nothing
    definer = owner(m.module)
    (definer === :Julia || owned_method(m)) && return nothing
    w = Base.get_world_counter()
    nonstake = nothing
    hit = nothing
    for (k, x) in enumerate(log)
        direct = (x isa Core.MethodInstance && k < length(log) && log[k+1] == "jl_method_table_insert") || x isa Type
        if direct && nonstake === nothing
            S = x isa Core.MethodInstance ? x.specTypes : x
            _stakeholder(definer, S) || (nonstake = S)
        end
        if hit === nothing && x isa Core.MethodInstance && isdefined(x, :cache)
            ci = x.cache
            while true
                if _trait_world_code(ci) && ci.max_world < w && ci.max_world + 2 >= w
                    hit = ci; break
                end
                isdefined(ci, :next) || break
                ci = ci.next
            end
        end
    end
    if nonstake !== nothing && hit !== nothing
        push!(_STRICT_MISSES, (m, nonstake, hit))
        Base.delete_method(m)
        throw(PirateError(m, definer, nonstake, hit, true))
    end
    return nothing
end

"Strict mode's part of the definition hook (before: may throw; after: the safety net)."
function _strict_on_definition(m::Method, after::Bool)
    STRICT[] || return nothing
    if !after
        v = _strict_violation(m)
        v === nothing || throw(PirateError(m, owner(m.module), v[1], v[2], false))
        _strict_log_start!()
    else
        _strict_after!(m)
    end
    return nothing
end

"Counts and times of the check at image loads: methods seen, pirates walked, seconds owning, seconds walking."
const _STRICT_STATS = zeros(4)
"Strict mode's part of the image hook: the image's methods that would break trait-world facts."
function _strict_image_refusals(ms::Vector{Any})
    STRICT[] || return Any[]
    out = Any[]
    _OWNER_MEMO[] = IdDict{Module,Any}()          # owners cannot change while one image's methods are scanned
    try
    for m in ms
        m isa Method || continue
        _STRICT_STATS[1] += 1
        t0 = time_ns()
        own = _strict_owned(m)
        t1 = time_ns()
        _STRICT_STATS[3] += (t1 - t0) / 1e9
        own && continue
        _STRICT_STATS[2] += 1
        v = _strict_violation(m)
        _STRICT_STATS[4] += (time_ns() - t1) / 1e9
        v === nothing || push!(out, PirateError(m, owner(m.module), v[1], v[2], false))
    end
    finally
        _OWNER_MEMO[] = nothing
    end
    return out
end
"Owned (no pirate): Julia's own, a method of the definer's own function (the common case), or owned by rule 3."
function _strict_owned(m::Method)
    d = owner(m.module)
    d === :Julia && return true
    body = Base.unwrap_unionall(m.sig)
    if body isa DataType && !isempty(body.parameters)
        ft = body.parameters[1]
        ft isa DataType && owner(ft.name.module) === d && return true
    end
    return owned_method(m)
end

function _strict_init!()
    STRICT[] = get(ENV, "JULIA_TW_STRICT", "0") == "1"
    empty!(DELEGATES)
    return nothing
end
"Register the known split-core delegates whose packages are loaded (after each top-level load)."
function _strict_known_delegates!()
    for (c, i) in KNOWN_DELEGATES
        cm = _loaded_root(c); im = _loaded_root(i)
        (cm === nothing || im === nothing) && continue
        ds = get!(() -> Any[], DELEGATES, owner(cm))
        o = owner(im)
        o in ds || push!(ds, o)
    end
    return nothing
end
