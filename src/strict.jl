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
"A type or signature for a message: printed by bound and key, cut at `n` characters."
function _short(@nospecialize(x), n::Int = 80)
    t = sprint(show, x; context = :compact => true)
    return length(t) <= n ? t : first(t, n - 1) * "…"
end
"The trait-world code a protected CodeInstance serves: the first caller, walking up its backedges, that is a method of a trait module."
function _trait_root(@nospecialize(ci))
    ci isa Core.CodeInstance || return nothing
    seen = Base.IdSet{Any}()
    todo = Any[ci.def isa Core.MethodInstance ? ci.def : ci.def.def]
    while !isempty(todo) && length(seen) < 500
        mi = pop!(todo)
        mi isa Core.MethodInstance || continue
        mi in seen && continue
        push!(seen, mi)
        m = mi.def
        m isa Method && _facts_method(m) && return mi      # trait-module code (compiled by facts), not Base under it
        isdefined(mi, :backedges) || continue
        for x in mi.backedges
            x isa Core.CodeInstance && push!(todo, x.def isa Core.MethodInstance ? x.def : x.def.def)
            x isa Core.MethodInstance && push!(todo, x)
        end
    end
    return nothing
end
"Whether `m`'s function belongs to the core of a known split-core pair (where a delegate is the answer)."
function _split_core_function(m::Method)
    ft = Base.unwrap_unionall(m.sig).parameters[1]
    mod = ft isa DataType ? Base.moduleroot(ft.name.module) : nothing
    mod === nothing && return false
    return any(c -> c == string(nameof(mod)), first.(KNOWN_DELEGATES))
end
function Base.showerror(io::IO, e::PirateError)
    m = e.method
    root = _trait_root(e.caller)
    print(io, "PirateError: strict mode refuses `", m.name, "(", join((_short(t, 40) for t in Base.unwrap_unionall(m.sig).parameters[2:end]), ", "),
          ")`, defined by ", e.definer, ".\n  It would change what trait-world code computes",
          root === nothing ? "" : " in `$(root.def isa Method ? "$(root.def.module).$(root.def.name)" : root)`",
          ", at the call `", _short(e.sig), "`.\n  ", e.definer, " owns neither the function nor a type in that signature (a pirate).\n  ",
          _split_core_function(m) ? "If the package implements the core that owns the function, declare it a delegate (`TraitWorld.delegate!(Core => Impl)`); otherwise t" : "T",
          "urn strict mode off (`TraitWorld.strict!(false)`) to follow the method as plain Julia does, or define it where a type it is for is owned.")
    e.later && print(io, "\n  (found after the definition by the safety net; the method was deleted again)")
end

"Code the mode protects: compiled by facts (Julia's owner `:facts`), or a trait module's."
function _trait_world_code(ci::Core.CodeInstance)
    ci.owner === FACTS_OWNER && return true
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

"Whether `m` would win at one of the concrete signatures the fact at `s` stands for (`_fact_splits`)."
function _would_win_split(m::Method, @nospecialize(s), world::UInt)
    ss = _fact_splits(s)
    ss === nothing && return _would_win(m, s, world)          # a closure's call at kinds
    return any(sp -> _would_win(m, sp, world), ss)
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
    return _winning_fact(m, s -> !_stakeholder(definer, s))
end

"""
A package extension's method that would win at a fact of valid trait-world code whose signature
holds no type of the extension's triggers: `(sig, caller)`, or `nothing`. The extension acts for
its parent there, a stakeholder's change: followed, with a warning (`_extension_warn`).
"""
function _extension_win(m::Method)
    r = Base.moduleroot(m.module)
    _extension_parent(r) === nothing && return nothing
    trig = _extension_triggers(r)
    trig === nothing && return nothing
    no_trigger(s) = !any(o -> o isa Module && String(nameof(o)) in trig, sig_owners(s))
    return _winning_fact(m, no_trigger)
end
function _extension_warn(m::Method, v)
    @warn "The package extension $(Base.moduleroot(m.module)) defines $(m.sig), which wins at $(v[1]), " *
          "a fact of trait code ($(_short(v[2]))) with none of the extension's triggers in it: " *
          "followed as its parent's change; that trait code compiles again" maxlog = 20
    return nothing
end

"The first fact `(sig, caller)` of valid trait-world code at which `m` would win and `accept(sig)` holds, or `nothing`."
function _winning_fact(m::Method, accept)
    world = Base.get_world_counter()
    seen = Base.IdSet{Any}()
    # a fact of trait-world code at which m wins; or a call of other code at which m wins, whose invalidation
    # reaches trait-world code through the callers' backedges, as Julia's invalidation follows them
    function check(s, caller)
        caller isa Core.CodeInstance && caller.max_world == typemax(UInt) || return nothing
        if _trait_world_code(caller)
            return _fact_sig(s) && _would_win_split(m, s, world) && accept(s) ? caller : nothing
        end
        caller in seen && return nothing
        si = typeintersect(s, m.sig)                     # a call of plain code may be at an abstract signature
        (si !== Union{} && _would_win(m, si, world) && accept(si)) || return nothing
        return _trait_dependent(caller, seen)
    end
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
                    t = check(s, caller)
                    t === nothing || return (s, t)
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
                t = check(v[j], v[j+1])
                t === nothing || return (v[j], t)
            end
        end
    end
    return nothing
end

"""
The first valid trait-world CodeInstance that depends on `ci` through callers' backedges (what
invalidating `ci` would invalidate too), or `nothing`. `seen` holds the code already walked.
"""
function _trait_dependent(ci::Core.CodeInstance, seen::Base.IdSet{Any})
    stack = Any[ci]
    while !isempty(stack)
        c = pop!(stack)::Core.CodeInstance
        c in seen && continue
        push!(seen, c)
        c.max_world == typemax(UInt) || continue
        _trait_world_code(c) && return c
        mi = Core.Compiler.get_ci_mi(c)
        isdefined(mi, :backedges) || continue
        be = mi.backedges
        i = 1
        while i <= length(be)
            x = be[i]
            if x isa Type                                  # (invoke signature, caller)
                i + 1 <= length(be) || break
                y = be[i+1]; i += 2
            else
                y = x; i += 1
            end
            y isa Core.CodeInstance && !(y in seen) && push!(stack, y)
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
        w = _extension_win(m)
        w === nothing || _extension_warn(m, w)
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
    _image_known_delegates!(ms)        # before the check: the image's own package may be a known delegate
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
        if own
            w = _extension_win(m)          # an extension's method is owned (it counts as its parent)
            w === nothing || _extension_warn(m, w)
            continue
        end
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
"""
Register the known split-core delegates among the packages of an image's methods, while it activates:
the package is not among the loaded modules yet, so `_strict_known_delegates!` (after the load)
would come too late for its own methods.
"""
function _image_known_delegates!(ms::Vector{Any})
    seen = Base.IdSet{Module}()
    for m in ms
        m isa Method || continue
        r = Base.moduleroot(m.module)
        r in seen && continue
        push!(seen, r)
        nm = string(nameof(r))
        for (c, i) in KNOWN_DELEGATES
            i == nm || continue
            cm = _loaded_root(c)
            cm === nothing && continue
            ds = get!(() -> Any[], DELEGATES, owner(cm))
            o = owner(r)
            o in ds || push!(ds, o)
        end
    end
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
