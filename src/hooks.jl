# ---------------------------------------------------------------------------
# The method-definition hooks of the patched Julia (writeup/explorations/julia-support.md,
# piece 1). Where the runtime offers them, the trait world's rules about definitions are
# enforced when a method is defined, before it becomes visible, instead of at checkpoints:
#   - an override after a conformance (note "Declaring a trait") is refused at its definition;
#   - a pirate of a sealed package (rule 3) is refused at its definition in refuse mode, and a
#     package image's pirates are left inactive at its load, whatever the load order;
#   - a method added to a trait module after it is complete refreshes the module's keep flags.
# On stock Julia the hooks do not exist; the checkpoints (`check_overrides`, the scan after each
# `using`) remain, and are kept as well where the hooks exist.
# ---------------------------------------------------------------------------

"Whether the running Julia has the method-definition hooks (`jl_set_method_definition_hook`)."
const _HAS_DEF_HOOK = Ref(false)
"Methods an image hook left inactive in this session, reported after the load."
const _REFUSED_AT_LOAD = Pirate[]
const _REFUSED_OVERRIDES = Method[]

function _hooks_init!()
    _HAS_DEF_HOOK[] = false
    ok = try
        cglobal(:jl_set_method_definition_hook) != C_NULL
    catch
        false
    end
    ok || return nothing
    get(ENV, "JULIA_TW_HOOKS", "1") == "0" && return nothing
    ccall(:jl_set_method_definition_hook, Cvoid, (Any,), _on_method_definition)
    ccall(:jl_set_image_methods_hook, Cvoid, (Any,), _on_image_methods)
    _HAS_DEF_HOOK[] = true
    return nothing
end

# --- the index of operations served by defaults -----------------------------------------

const _OVR_INDEX = Ref{Any}(nothing)          # IdDict: operation function => [(Y, op, R, X, T)]
const _OVR_GEN = Ref{UInt}(0)

"The conformances' default-served operations by operation function, rebuilt when the generation moves."
function _override_index()
    idx = _OVR_INDEX[]
    idx !== nothing && _OVR_GEN[] == GENERATION[] && return idx::IdDict{Any,Vector{Any}}
    d = IdDict{Any,Vector{Any}}()
    for m in methods(_declared_defaults)
        sig = Base.unwrap_unionall(m.sig)
        ps = sig.parameters
        length(ps) == 3 || continue
        (ps[2] isa DataType && ps[3] isa DataType) || continue
        X, T = ps[2].parameters[1], ps[3].parameters[1]
        for (Y, R, D) in Base.invokelatest(_declared_defaults, X, T)
            for op in D
                f = _opfn(Y, op)
                push!(get!(d, f, Any[]), (Y, op, R, X, T))
            end
        end
    end
    _OVR_INDEX[] = d
    _OVR_GEN[] = GENERATION[]
    return d
end

"An override that method `m` would make after a conformance whose default serves the operation, or `nothing`."
function _override_violation(m::Method)
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType && !isempty(sig.parameters) || return nothing
    FT = sig.parameters[1]
    (FT isa DataType && Base.issingletontype(FT)) || return nothing
    recs = get(_override_index(), FT.instance, nothing)
    recs === nothing && return nothing
    for (Y, op, R, X, T) in recs
        for N in _arities(Y, op)
            A = _declared_args(Y, op, R, N)
            Tuple{FT,R,A.parameters...} <: m.sig || continue
            return "`$op` of $Y gets a method for $R ($m), but the conformance of $T to $X serves it by the trait's default. " *
                   "An override belongs to the conformance: define it before `@implement`, or in its block"
        end
    end
    return nothing
end

# --- the hooks --------------------------------------------------------------------------

"Called by the runtime for every method definition: before it is visible (`after = false`, may throw), and after."
function _on_method_definition(m::Method, after::Bool)
    err = nothing
    try
        if !after
            msg = _override_violation(m)
            if msg !== nothing
                err = ImplementError(msg)
            elseif !isempty(SEALED) && SEAL_MODE[] === :refuse
                p = _pirate_of_sealed(m)
                p === nothing || (err = PiracyError(_pirate_report([p], :refuse_def)))
            end
        else
            # a method added to a complete trait module: its functions' keep flags may change
            mod = _finished_trait_module(m)
            mod === nothing || _refresh_keeps!(mod)
        end
    catch e
        # a failure of the machinery must not break definitions: report it once, define the method
        _HOOK_FAILED[] || (_HOOK_FAILED[] = true; @warn "TraitWorld's definition hook failed; definitions proceed unchecked" exception = (e, catch_backtrace()))
    end
    err === nothing || throw(err)                    # refused: the method never becomes visible
    return nothing
end
const _HOOK_FAILED = Ref(false)

"The complete trait module a method belongs to (by where it is defined or by its function's owner), or `nothing`."
function _finished_trait_module(m::Method)
    for x in (m.module, _function_module(m))
        x === nothing && continue
        y = x
        while true
            if isdefined(y, :__tw_finished__)
                return y.__tw_finished__[] ? y : nothing
            end
            p = parentmodule(y)
            p === y && break
            y = p
        end
    end
    return nothing
end
function _function_module(m::Method)
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType && !isempty(sig.parameters) || return nothing
    FT = sig.parameters[1]
    FT isa DataType && return FT.name.module
    return nothing
end

"Recompute the keep flags of a trait module's bounded functions after a later definition."
function _refresh_keeps!(mod::Module)
    isdefined(mod, :__tw_positions__) || return nothing
    seen = Base.IdSet{Any}()
    for (f, _, _) in mod.__tw_positions__
        f in seen && continue
        push!(seen, f)
        _fix_keeps!(mod, f)
    end
    return nothing
end

"Called by the runtime with a package image's new methods before they are activated: those to leave inactive."
function _on_image_methods(ms::Vector{Any}, pkg::String)
    refused = Any[]
    isempty(SEALED) && return nothing
    for m in ms
        m isa Method || continue
        if SEAL_MODE[] === :refuse
            p = _pirate_of_sealed(m)
            if p !== nothing
                push!(refused, m)
                push!(_REFUSED_AT_LOAD, p)
                continue
            end
        end
        if _override_violation(m) !== nothing
            push!(refused, m)
            push!(_REFUSED_OVERRIDES, m)
        end
    end
    return isempty(refused) ? nothing : refused
end

"After a load: report what the image hook left inactive."
function _report_refused_at_load()
    if !isempty(_REFUSED_AT_LOAD)
        found = copy(_REFUSED_AT_LOAD); empty!(_REFUSED_AT_LOAD)
        @error sprint(showerror, PiracyError(_pirate_report(found, :refuse_load)))
    end
    if !isempty(_REFUSED_OVERRIDES)
        ms = copy(_REFUSED_OVERRIDES); empty!(_REFUSED_OVERRIDES)
        @error "ImplementError: overrides after a conformance were left inactive at load:\n  " * join(string.(ms), "\n  ")
    end
    return nothing
end

# --- the invalidation policy (julia-support.md piece 2) -----------------------------------

"A package's root module, as the runtime's filter counts it: a module under `Main` counts as its own package."
function _pkg_root(m::Module)
    while true
        p = parentmodule(m)
        (p === m || p === Main) && return m
        m = p
    end
end
"Whether package `r` owns `t` (a type in a method's signature; `Type{T}` is a constructor of `T`; a `Union` proves nothing)."
function _root_owns(@nospecialize(t), r::Module, depth::Int = 0)
    depth > 2 && return false
    t = Base.unwrap_unionall(t)
    t isa TypeVar && (t = t.ub)
    t isa DataType || return false
    t.name === Type.body.name && length(t.parameters) == 1 && return _root_owns(t.parameters[1], r, depth + 1)
    return _pkg_root(t.name.module) === r
end

"""
    _invalidation_policy(m::Method) -> Union{Module, Nothing}

The trait world's invalidation policy, registered with the patched runtime (rule 4). A definition
in the trait world or in Julia is in every view, and a pirate (whose definer owns nothing in its
signature) changes code compiled against what it pirates: both invalidate as usual (`nothing`).
Otherwise the definer adds a method for its own types or function; it can change protected code
only if that code was compiled for one of the definer's types, which the runtime checks per
CodeInstance against the package returned here.
"""
function _invalidation_policy(m::Method)
    mod = m.module
    is_trait_world(mod) && return nothing
    r = _pkg_root(mod)
    owner(r) === :Julia && return nothing
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return nothing
    for p in sig.parameters
        Base.isvarargtype(p) && continue
        _root_owns(p, r) && return r
    end
    return nothing
end
