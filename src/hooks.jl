# ---------------------------------------------------------------------------
# The method-definition hooks of the patched Julia (writeup/explorations/julia-support.md,
# piece 1). Where the runtime offers them, the trait world's rules about definitions are
# enforced when a method is defined, before it becomes visible, instead of at checkpoints:
#   - an override after a conformance (note "Declaring a trait") is refused at its definition,
#     and a package image's overrides are left inactive at its load;
#   - a method added to a trait module after it is complete refreshes the module's keep flags.
# On stock Julia the hooks do not exist; the checkpoint (`check_overrides`) remains, and is kept
# as well where the hooks exist. Piece 5 (`jl_set_image_keep_compiled`) is switched on here too.
# ---------------------------------------------------------------------------

"Whether the running Julia has the method-definition hooks (`jl_set_method_definition_hook`)."
const _HAS_DEF_HOOK = Ref(false)
"Overrides an image hook left inactive in this session, reported after the load."
const _REFUSED_OVERRIDES = Method[]
"Strict mode: an image's winning pirates left inactive at its load, reported after it."
const _REFUSED_PIRATES = Any[]

function _hooks_init!()
    # piece 5: an image of a package using TraitWorld keeps the machine code its workload made for
    # upstream code (workers at upstream keys, code under the trait world's own cache owner)
    if ccall(:jl_generating_output, Cint, ()) == 1 && get(ENV, "JULIA_TW_KEEP_COMPILED", "1") != "0" &&
            (try; cglobal(:jl_set_image_keep_compiled) != C_NULL; catch; false; end)
        ccall(:jl_set_image_keep_compiled, Cvoid, (Cint,), 1)
    end
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

const _OVR_INDEX = IdDict{Any,Vector{Any}}()      # operation function => [(Y, op, R, X, T)]
const _OVR_BUILT = Ref(false)

"Add the records of one `_declared_defaults(X, T)` method to the index."
function _index_declared!(m::Method)
    sig = Base.unwrap_unionall(m.sig)
    ps = sig.parameters
    length(ps) == 3 || return nothing
    (ps[2] isa DataType && ps[3] isa DataType && ps[2] <: Type && ps[3] <: Type) || return nothing
    X, T = ps[2].parameters[1], ps[3].parameters[1]
    for (Y, R, D) in Base.invokelatest(_declared_defaults, X, T)
        for op in D
            f = _opfn(Y, op)
            push!(get!(_OVR_INDEX, f, Any[]), (Y, op, R, X, T))
        end
    end
    return nothing
end
"""
The conformances' default-served operations by operation function: built once from the methods of
`_declared_defaults`, then kept current by the hooks, which see every new such method.
"""
function _override_index()
    if !_OVR_BUILT[]
        empty!(_OVR_INDEX)
        for m in methods(_declared_defaults)
            _index_declared!(m)
        end
        _OVR_BUILT[] = true
    end
    return _OVR_INDEX
end
_is_declared_defaults(m::Method) = (sig = Base.unwrap_unionall(m.sig); sig isa DataType && !isempty(sig.parameters) && sig.parameters[1] === typeof(_declared_defaults))

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
            msg === nothing || (err = ImplementError(msg))
            err === nothing && (err = _strict_check(m, false))
        else
            err = _strict_check(m, true)
            _OVR_BUILT[] && _is_declared_defaults(m) && _index_declared!(m)
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
"Strict mode's check, as an error to throw or `nothing` (a failure of the check itself is the hook's failure)."
function _strict_check(m::Method, after::Bool)
    try
        _strict_on_definition(m, after)
    catch e
        e isa PirateError && return e
        rethrow()
    end
    return nothing
end

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
    try
        for m in ms
            m isa Method || continue
            _is_declared_defaults(m) && (_OVR_BUILT[] = false)   # not active yet: the index is rebuilt at its next use
        end
        # overrides are checked against the conformances already active; an image's own are its package's business
        idx = _override_index()
        for m in ms
            m isa Method || continue
            if !isempty(idx) && _override_violation(m) !== nothing
                push!(refused, m)
                push!(_REFUSED_OVERRIDES, m)
            end
        end
        for e in _strict_image_refusals(ms)
            push!(refused, e.method)
            push!(_REFUSED_PIRATES, e)
        end
    catch e
        _HOOK_FAILED[] || (_HOOK_FAILED[] = true; @warn "TraitWorld's image hook failed; the load proceeds unchecked" exception = (e, catch_backtrace()))
    end
    return isempty(refused) ? nothing : refused
end

"After a load: report the overrides the image hook left inactive."
function _report_refused_at_load()
    if !isempty(_REFUSED_OVERRIDES)
        ms = copy(_REFUSED_OVERRIDES); empty!(_REFUSED_OVERRIDES)
        @error "ImplementError: overrides after a conformance were left inactive at load:\n  " * join(string.(ms), "\n  ")
    end
    if !isempty(_REFUSED_PIRATES)
        es = copy(_REFUSED_PIRATES); empty!(_REFUSED_PIRATES)
        @error "strict mode left a package's winning pirates inactive at its load:\n  " * join(sprint.(showerror, es), "\n  ")
    end
    return nothing
end
