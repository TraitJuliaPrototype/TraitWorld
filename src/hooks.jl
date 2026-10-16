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
    # the inference hook (piece 4): newly compiled trait-world code is audited where it is compiled,
    # so a guard need not re-audit after every world change
    if isdefined(Base.Compiler, :_tw_infer_hook)
        Base.Compiler._tw_infer_hook[] = _on_inferred
        _GUARD_BY_STAMP[] = true
    end
    return nothing
end

"Called by the compiler after trait-world code is inferred: audit its edges; a pirate reached makes the guards audit again."
function _on_inferred(ci::Core.CodeInstance)
    MODE[] === :recompile && return nothing
    findings = @lock _LOCK _walk(ci, Base.get_world_counter())
    isempty(findings) || _bump_guard!()
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
            if msg !== nothing
                err = ImplementError(msg)
            elseif !isempty(SEALED)
                p = _pirate_of_sealed(m)
                if p !== nothing
                    SEAL_MODE[] === :refuse ? (err = PiracyError(_pirate_report([p], :refuse_def))) : _bump_guard!()
                end
            end
        else
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
    _OWNER_MEMO[] = IdDict{Module,Any}()
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
                continue
            end
            isempty(SEALED) && continue
            p = _pirate_of_sealed(m)
            p === nothing && continue
            if SEAL_MODE[] === :refuse
                push!(refused, m)
                push!(_REFUSED_AT_LOAD, p)
            else
                push!(_WARNED_AT_LOAD, p)            # reported after the load (warn mode)
            end
        end
        isempty(_WARNED_AT_LOAD) || _bump_guard!()
    catch e
        _HOOK_FAILED[] || (_HOOK_FAILED[] = true; @warn "TraitWorld's image hook failed; the load proceeds unchecked" exception = (e, catch_backtrace()))
    finally
        _OWNER_MEMO[] = nothing
    end
    return isempty(refused) ? nothing : refused
end
const _WARNED_AT_LOAD = Pirate[]

"After a load: report what the image hook left inactive, and (warn mode) the pirates it saw."
function _report_refused_at_load()
    if !isempty(_WARNED_AT_LOAD)
        found = copy(_WARNED_AT_LOAD); empty!(_WARNED_AT_LOAD)
        new = filter(p -> !(p.definer in _REPORTED), found)
        for p in new
            push!(_REPORTED, p.definer)
        end
        isempty(new) || @warn sprint(showerror, PiracyError(_pirate_report(new, :warn)))
    end
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

"""
The packages (outside Base, Core and the trait world) that every value matching `t` mentions in its
type: `t` itself (or a `Vararg`'s element, a type variable's bound) is a package's type, or a type
parameter requires one (`Ref{T} where T<:InlineString`, `Diagonal{T, Ones{T}}`); for a `Union`, the
packages both sides require. `Type{T}` counts as `T`: a type, like any value, reaches protected code
only where the code was compiled for it (the premise of rule 4's policy, as for the definer's own
types after review F1).
"""
function _required_roots(@nospecialize(t), depth::Int = 0)
    out = Module[]
    depth > 4 && return out
    t isa UnionAll && return _required_roots(Base.unwrap_unionall(t), depth)
    t isa TypeVar && return _required_roots(t.ub, depth + 1)
    t isa Core.TypeofVararg && return isdefined(t, :T) ? _required_roots(t.T, depth + 1) : out
    t isa Union && return intersect(_required_roots(t.a, depth + 1), _required_roots(t.b, depth + 1))
    t isa DataType || return out
    r = _type_root(t.name.module)
    r === nothing || push!(out, r)
    for p in t.parameters
        union!(out, _required_roots(p, depth + 1))
    end
    return out
end

const _TYPE_ROOTS = IdDict{Module,Any}()           # module => its package root, or `nothing`
"The package whose types a module's are, for the policy: `nothing` for Base's and Core's types (everyone's) and the trait world's; a standard library's types are its own (`LibGit2`, `SparseArrays`)."
function _type_root(mod::Module)
    r = get(_TYPE_ROOTS, mod, missing)
    r === missing || return r
    r = _julia_core(mod) || _trait_world_package(mod) ? nothing : _pkg_root(mod)
    _TYPE_ROOTS[mod] = r
    return r
end

"""
    _invalidation_policy(m::Method) -> Union{Module, Nothing}

The trait world's invalidation policy, registered with the patched runtime (rule 4). A new method
can change compiled code only for the values it applies to. If its signature requires a type of
some package outside Base, Core and the trait world (an argument of that package's type, or of a Julia
type parametrized by it), it can change protected code only if that code was compiled for one of
the package's types: the runtime checks this per CodeInstance against the package returned here.
This holds whoever defines the method (the package itself, another package extending it, a standard
library for its own types). A definition in Base or in the trait world, and a method for Base's
types only (a pirate of Base), can change anything: they invalidate as usual (`nothing`).
"""
_julia_core(mod::Module) = (p = _pkg_root(mod); p === Base || p === Core || p === Base.Compiler)
"In the trait world and not one of Julia's standard libraries (whose types and methods are their own here)."
_trait_world_package(mod::Module) = owner(_pkg_root(mod)) !== :Julia && is_trait_world(mod)
function _invalidation_policy(m::Method)
    (_julia_core(m.module) || _trait_world_package(m.module)) && return nothing
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return nothing
    for (i, p) in enumerate(sig.parameters)
        i == 1 && continue                           # the function: its owner's methods reach every caller
        rs = _required_roots(p)
        isempty(rs) && continue
        i = findfirst(r -> owner(r) !== :Julia, rs)     # every value mentions all of them: prefer a package's
        return rs[i === nothing ? 1 : i]
    end
    return nothing
end
