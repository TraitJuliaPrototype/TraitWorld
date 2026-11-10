# Strict mode (traits §12.3; lowering §13; compiler §10.2; facts §11). Code compiled by facts is
# invalidated only by a change of code it depends on, a stakeholder's: a pirate that would win at a
# call that code compiled by facts makes is refused (`PirateError`) and does not exist, for any code.

const STRICT = Ref(false)

"""
    TraitWorld.strict!(on = true)

Turn strict mode on or off for this session (traits §12.3); `JULIA_TW_STRICT=1` turns it on at start.
"""
function strict!(on::Bool = true)
    STRICT[] = on
    on ? _validation_log_on!() : _validation_log_off!()
    ccall(:jl_set_strict_memberships, Cint, (Cint,), on)  # an ambiguity at a membership refused (§12.3)
    return nothing
end

"""
    PirateError

Strict mode refused a method: it would win at a call that code compiled by facts makes (`sig`, in
`caller`), and its package owns neither the function nor a type in that signature (traits §11.3).
"""
struct PirateError <: Exception
    method::Method
    definer::Any
    sig::Any
    caller::Any
    later::Bool          # found only after the definition: the method was deleted again
end

function _short(@nospecialize(x), n::Int = 80)
    t = sprint(show, x; context = :compact => true)
    return length(t) <= n ? t : first(t, n - 1) * "…"
end

function _code_name(@nospecialize(ci))
    ci isa Core.CodeInstance || return "code compiled by facts"
    mi = CC.get_ci_mi(ci)
    return mi.def isa Method ? "$(mi.def.module).$(mi.def.name)" : string(mi)
end

function Base.showerror(io::IO, e::PirateError)
    m = e.method
    print(io, "PirateError: strict mode refuses `", m.name, "(",
          join((_short(t, 40) for t in (Base.unwrap_unionall(m.sig)::DataType).parameters[2:end]), ", "),
          ")`, defined by ", _owner_name(e.definer), ".\n  It would win at the call `", _short(e.sig),
          "`, which code compiled by facts makes (in `", _code_name(e.caller), "`).\n  ",
          _owner_name(e.definer), " owns neither the function nor a type in that signature (a pirate). ",
          "Define it where a type it is for is owned, name the definer a joint owner (`@joint_owners`), ",
          "or turn strict mode off (`TraitWorld.strict!(false)`) to follow it as plain Julia does.")
    e.later && print(io, "\n  (found after the definition; the method was deleted again)")
end

# code compiled by facts: Julia's own owner, the facts policy bit in its flags (compiler §2.3)
_facts_code(ci::Core.CodeInstance) = ci.owner === nothing && (ci.flags & 0x20) != 0

"Whether `definer` is a stakeholder of the signature `s`: it owns, or is a joint owner of, a part of it."
_stakeholder(@nospecialize(definer), @nospecialize(s)) = any(o -> owns(definer, o), sig_owners(s))

"Whether the new method `m` would be selected at `s`: it applies, and no current method beats it."
function _would_win(m::Method, @nospecialize(s), world::UInt)
    s <: m.sig || return false
    ms = Base._methods_by_ftype(s, nothing, 1, world, false, Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
    (ms isa Vector && length(ms) == 1) || return true      # no method, or ambiguous already: m changes it
    cur = (ms[1]::Core.MethodMatch).method
    cur === m && return false
    return ccall(:jl_type_morespecific, Cint, (Any, Any), cur.sig, m.sig) == 0
end

_owned_or_julia(m::Method) = (d = owner(m.module); d === :Julia || owned_method(m))

"The first fact `(sig, caller)` of code compiled by facts at which `m` would win and `accept(sig)` holds, or `nothing`."
function _winning_fact(m::Method, accept)
    world = Base.get_world_counter()
    seen = Base.IdSet{Any}()
    function check(@nospecialize(s), @nospecialize(caller))
        caller isa Core.CodeInstance && caller.max_world == typemax(UInt) || return nothing
        if _facts_code(caller)
            return CC.is_fact_sig(s) && _would_win(m, s, world) && accept(s) ? caller : nothing
        end
        caller in seen && return nothing
        si = typeintersect(s, m.sig)                         # plain code may call at an abstract signature
        (si !== Union{} && _would_win(m, si, world) && accept(si)) || return nothing
        return _facts_dependent(caller, seen)
    end
    # 1. calls that dispatch to an existing method's specializations, where m would win
    ms = Base._methods_by_ftype(m.sig, nothing, -1, world, false, Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
    ms isa Vector || return nothing                          # too many to list: the check after decides
    for mm in ms
        old = (mm::Core.MethodMatch).method
        old === m && continue
        ccall(:jl_type_morespecific, Cint, (Any, Any), old.sig, m.sig) != 0 && continue
        for mi in Base.specializations(old)
            mi isa Core.MethodInstance && isdefined(mi, :backedges) || continue
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
    # 2. calls that found no method: a gap the new method fills
    body = Base.unwrap_unionall(m.sig)
    if body isa DataType && !isempty(body.parameters)
        ft = body.parameters[1]
        tn = ft isa DataType ? ft.name : nothing
        be = getfield(Core.methodtable, :backedges)
        for i in 1:2:(length(be)::Int)-1
            isassigned(be, i) && be[i] === tn && isassigned(be, i + 1) || continue
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

"The first valid CodeInstance compiled by facts that rests on `ci` through its callers' backedges, or `nothing`."
function _facts_dependent(ci::Core.CodeInstance, seen::Base.IdSet{Any})
    stack = Any[ci]
    while !isempty(stack)
        c = pop!(stack)::Core.CodeInstance
        c in seen && continue
        push!(seen, c)
        c.max_world == typemax(UInt) || continue
        _facts_code(c) && return c
        mi = CC.get_ci_mi(c)
        isdefined(mi, :backedges) || continue
        be = mi.backedges
        i = 1
        while i <= length(be)
            x = be[i]
            if x isa Type
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

"The fact `(sig, caller)` a pirate `m` would win at, by a definer that holds no stake there, or `nothing`."
function _strict_violation(m::Method)
    _owned_or_julia(m) && return nothing
    definer = owner(m.module)
    return _winning_fact(m, s -> !_stakeholder(definer, s))
end

# --- after the definition: Julia's own invalidation log, the check the walk could miss ----------

const _STRICT_LOG = Ref{Any}(nothing)
const _STRICT_MISSES = Any[]                 # (method, sig, code) found only after the definition
_strict_log_start!() = (_STRICT_LOG[] = ccall(:jl_debug_method_invalidation, Any, (Cint,), 1); nothing)
function _strict_log_stop!()
    log = _STRICT_LOG[]
    _STRICT_LOG[] = nothing
    ccall(:jl_debug_method_invalidation, Any, (Cint,), 0)
    return log
end

function _strict_after!(m::Method)
    log = _strict_log_stop!()
    log isa Vector || return nothing
    _owned_or_julia(m) && return nothing
    definer = owner(m.module)
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
                if _facts_code(ci) && ci.max_world < w && ci.max_world + 2 >= w
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

"Strict mode's part of the definition hook: before the method is visible, the walk; after, the log."
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

"Strict mode's part of the image hook: the image's methods that would win at a fact, left inactive."
function _strict_image_refusals(ms::Vector{Any})
    STRICT[] || return Any[]
    out = Any[]
    for m in ms
        m isa Method || continue
        _owned_or_julia(m) && continue
        v = _strict_violation(m)
        v === nothing && continue
        @error sprint(showerror, PirateError(m, owner(m.module), v[1], v[2], false)) * "\n  (the image's method is left inactive)"
        push!(out, m)
    end
    return out
end

# --- after an image's load: the edges that failed validation (compiler §10.2) -------------------

const _VAL_LOG = Ref{Any}(nothing)
_validation_log_ref() = CC.ReinferUtils._jl_debug_method_invalidation
function _validation_log_on!()
    r = _validation_log_ref()
    cur = r[]
    (cur !== nothing && cur === _VAL_LOG[]) && return nothing
    cur === nothing || return nothing                     # another tool's record: left alone
    log = Any[]
    _VAL_LOG[] = log
    r[] = log
    return nothing
end
function _validation_log_off!()
    r = _validation_log_ref()
    r[] === _VAL_LOG[] && _VAL_LOG[] !== nothing && (r[] = nothing)
    _VAL_LOG[] = nothing
    return nothing
end

"A pirate loaded before a package image, which breaks a fact of the image's code compiled by facts."
struct PirateAtLoadError <: Exception
    method::Method
    definer::Any
    sig::Any
    code::Core.CodeInstance
end
function Base.showerror(io::IO, e::PirateAtLoadError)
    print(io, "PirateError: `", e.method.name, "(",
          join((_short(t, 40) for t in (Base.unwrap_unionall(e.method.sig)::DataType).parameters[2:end]), ", "),
          ")`, defined by ", _owner_name(e.definer), " before a package image was loaded, wins at its fact `",
          _short(e.sig), "` in `", _code_name(e.code), "`.\n  It came first, so strict mode cannot refuse it: ",
          "the image's code is compiled again with it. Load the package before the pirate.")
end

function _load_pirates(log::Vector{Any})
    out = PirateAtLoadError[]
    world = Base.get_world_counter()
    seen = Set{Any}()
    for k in 2:length(log)
        tag = log[k]
        (tag isa String && tag == "insert_backedges_callee" && k + 1 <= length(log)) || continue
        edge, ci = log[k-1], log[k+1]
        ci isa Core.CodeInstance && _facts_code(ci) || continue
        s = edge isa Core.MethodInstance ? edge.specTypes : edge isa Type ? edge : continue
        ms = Base._methods_by_ftype(s, nothing, 1, world, false, Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
        (ms isa Vector && length(ms) == 1) || continue
        m = (ms[1]::Core.MethodMatch).method
        (m, s) in seen && continue
        push!(seen, (m, s))
        _owned_or_julia(m) && continue
        d = owner(m.module)
        _stakeholder(d, s) && continue
        push!(out, PirateAtLoadError(m, d, s, ci))
    end
    return out
end

const _LOAD_PIRATES = PirateAtLoadError[]

"The ambiguities that images' memberships met at their activation under strict mode, as reported (traits §12.3)."
const _LOAD_AMBIGUITIES = String[]

# The runtime collects them at activation in place of its warning; the report is strict mode's.
function _report_load_ambiguities!()
    msgs = ccall(:jl_take_activation_ambiguities, Any, ())
    msgs isa Vector{Any} || return nothing
    n = length(_LOAD_AMBIGUITIES)
    for m in msgs
        m isa String && push!(_LOAD_AMBIGUITIES, m)
    end
    length(_LOAD_AMBIGUITIES) > n || return nothing
    @error "strict mode: a package image's membership makes methods ambiguous with code loaded earlier:\n  " *
           join(_LOAD_AMBIGUITIES[n+1:end], "\n  ")
    return nothing
end

"After a package load, in strict mode: the report of the edges that failed validation, with the winning method."
function _strict_at_load!(_pkg = nothing)
    STRICT[] || return nothing
    ccall(:jl_generating_output, Cint, ()) == 0 || return nothing
    _report_load_ambiguities!()
    log = _VAL_LOG[]
    if log isa Vector{Any} && _validation_log_ref()[] === log
        isempty(log) && return nothing
        entries = copy(log)
        empty!(log)
        es = _load_pirates(entries)
        isempty(es) || @error "strict mode: pirates loaded before a package image change its code compiled by facts:\n  " *
                              join(sprint.(showerror, es), "\n  ")
        append!(_LOAD_PIRATES, es)
    else
        _validation_log_on!()
    end
    return nothing
end

# --- deletions (compiler §10.2) ---------------------------------------------------------------

"Strict mode's deletion hook: deleting a pirate that code compiled by facts dispatches to is refused; an owned method's deletion is its owner's change."
function _deletion_hook(m::Method)
    STRICT[] || return nothing
    _owned_or_julia(m) && return nothing                 # an owner's change
    world = Base.get_world_counter()
    for mi in Base.specializations(m)
        mi isa Core.MethodInstance && isdefined(mi, :backedges) || continue
        seen = Base.IdSet{Any}()
        for x in mi.backedges
            x isa Core.CodeInstance || continue
            c = _facts_code(x) ? x : _facts_dependent(x, seen)
            c === nothing && continue
            throw(PirateError(m, owner(m.module), mi.specTypes, c, false))
        end
    end
    return nothing
end

function _strict_init!()
    STRICT[] = get(ENV, "JULIA_TW_STRICT", "0") == "1"
    STRICT[] && _validation_log_on!()
    STRICT[] && ccall(:jl_set_strict_memberships, Cint, (Cint,), 1)
    push!(Base.package_callbacks, _strict_at_load!)
    return nothing
end
