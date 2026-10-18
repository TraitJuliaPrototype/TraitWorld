# ---------------------------------------------------------------------------
# Definition checking (session 22): library code checked once, against its
# bounds alone. A trait object has no methods but its traits' operations, and
# every operation declares its result type, so a worker's code is the same for
# every representation except the operations' implementations, which are
# checked at their conformance. Inferring a worker once at an archetype, a
# stand-in representation whose operations return values of their declared
# types and nothing more, therefore checks it for every representation: the
# archetypes of C++0x concepts, the definition checking of Rust and Swift.
# A worker whose signature has a `Callable` with an open result type, or a
# bound with open parameters, is still checked per signature, at its first call.
# ---------------------------------------------------------------------------

"""
A stand-in representation of trait `X`: library code checked against `X` alone.
`P` holds the parameters a bound fixes (`ArrayLike{Float64}` fixes `T`), `ParamOpen` for the others.
"""
struct Archetype{X,P} end
"An open parameter `p` of trait `X` at an archetype: a type with no methods."
struct ParamArchetype{X,p} end
struct ParamOpen end
"Parameter `p` (the `i`th) of trait `Y` at archetype `A`: fixed by the bound, else an opaque stand-in."
function _archparam(::Type{Archetype{X,P}}, @nospecialize(Y), p::Symbol, i::Int) where {X,P}
    if Y === X && i <= length(P.parameters)
        v = P.parameters[i]
        v === ParamOpen || return v
    end
    return ParamArchetype{Y,p}
end

"The witness of an archetype's view: an operation answers with a value of its declared type, nothing more."
struct ArchWit end

# never run, only inferred: `opcall` asserts the declared result type of whatever comes back
@inline _dispatch(::Type{X}, ::Val{op}, f::F, w::ArchWit, r, t, args...) where {X,op,F} = Base.inferencebarrier(nothing)
# a field at an archetype: a value of its declared type, nothing more
@inline _fget(::Type{X}, ::Val{f}, w::ArchWit, v, ::Type{R}) where {X,f,R} = Base.inferencebarrier(nothing)::field_type(X, Val(f), R)

"The traits a view of `X` brings: `X` and its supertraits, or the traits a bundle names."
function _arch_traits(@nospecialize(X), out = Any[])
    b = bundle(X)
    if b !== nothing
        for Y in b
            _arch_traits(Y, out)
        end
        return out
    end
    X = _family(X)
    _hasid(out, X) || push!(out, X)
    for S in supertraits(X)
        _arch_traits(S, out)
    end
    return out
end

"""
    archetype_tobj(lb)

The trait object a worker sees at a position bounded by the trait patterns in
`lb` (`ArrayLike{Float64, N, R}`, open parameters as type variables): each
bound at its own archetype, which keeps the parameters the bound fixes; its
supertraits' views share it.
"""
function archetype_tobj(@nospecialize(lb))
    views = Any[]
    for Yp in Base.uniontypes(lb)
        X = _family(Yp)
        u = Base.unwrap_unionall(Yp)
        fixed = u isa DataType && length(u.parameters) > 1 ?
                Any[p isa TypeVar ? ParamOpen : p for p in u.parameters[1:end-1]] : Any[]
        A = Archetype{X,Tuple{fixed...}}
        for Y in _arch_traits(X)
            push!(views, View{_instance(Y, A),ArchWit,A,length(trait_fields(Y)),Nothing})
        end
    end
    return TObj{_encode_traits(Any[v.parameters[1] for v in views]),Tuple{views...}}
end

"The archetype signature of a worker method, or `nothing` if it has no bounded position or is not checked this way."
function archetype_sig(m::Method)
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return nothing
    ps = sig.parameters
    (isempty(ps) || ps[1] === typeof(Core.kwcall)) && return nothing        # keyword workers: per signature
    out = Any[ps[1]]
    bounded = false
    for k in 2:length(ps)
        p = ps[k]
        Base.isvarargtype(p) && return nothing                              # vararg workers: per signature
        lb = _tobj_lb(p)
        if lb === nothing || lb === Union{}
            q = p isa TypeVar ? p.ub : p
            _hascallable(q) && return nothing                                # a function from above: per signature
            push!(out, q)
        else
            _open_params(lb) && return nothing       # an open parameter: checked per signature (note "Definition checking")
            push!(out, archetype_tobj(lb))
            bounded = true
        end
    end
    return bounded ? Tuple{out...} : nothing
end
"Whether a bound leaves a trait parameter (other than the representation) open."
function _open_params(@nospecialize(lb))
    for Yp in Base.uniontypes(lb)
        u = Base.unwrap_unionall(Yp)
        u isa DataType && length(u.parameters) > 1 && any(p -> p isa TypeVar, u.parameters[1:end-1]) && return true
    end
    return false
end

function _hascallable(@nospecialize(T))
    T isa Union && return any(_hascallable, Base.uniontypes(T))
    T = Base.unwrap_unionall(T)
    return T isa DataType && (T <: CObj || T <: CMulti || T <: Erased || T <: CallAs)
end

"Methods checked at their definition: their workers need no check per signature."
const _DEF_CHECKED = Base.IdSet{Method}()
"Whether a worker's first call skips its check when its method was checked at definition (measurement switch)."
const DEFCHECK_SKIP = Ref(true)

"""
    definition_problems(f) -> Vector{String}

Check every trait-bounded method of `f` once, at archetypes: what it does
with its trait objects, independent of any representation. Methods checked
clean are recorded, so their workers' first calls skip the check per signature.
"""
function definition_problems(@nospecialize(f))
    out = String[]
    for m in methods(f)
        # a method the check cannot build archetypes for (keyword workers, families it does not
        # cover) is left to its worker's first call, as the deferred cases are
        asig = try archetype_sig(m) catch; nothing end
        asig === nothing && continue
        ps = try
            _latest(worker_problems, asig)::Vector{String}
        catch
            continue
        end
        if isempty(ps)
            push!(_DEF_CHECKED, m)
        else
            for p in unique(ps)
                push!(out, "$(m.name) ($(basename(string(m.file))):$(m.line)): $p")
            end
        end
    end
    return out
end

"""
    check_definitions(mod) -> Vector{String}

Definition checks for every function of trait module `mod`; throws a
`TraitUseError` listing the problems, or returns the empty list.
"""
function check_definitions(mod::Module)
    out = String[]
    for n in names(mod; all = true)
        isdefined(mod, n) || continue
        f = getfield(mod, n)
        f isa Function || continue
        parentmodule(f) === mod || continue
        append!(out, definition_problems(f))
    end
    isempty(out) || throw(TraitUseError(out))
    return out
end

"Whether the worker for `sig` was checked at its method's definition."
function _def_checked(@nospecialize(sig))
    DEFCHECK_SKIP[] || return false
    isempty(_DEF_CHECKED) && return false
    sig isa DataType || return false
    for p in sig.parameters
        _hascallable(p) && return false
    end
    m = try
        Base._which(sig).method
    catch
        return false
    end
    return m in _DEF_CHECKED
end

# --- keeping: which functions may keep a trait object (note "Keeping a value is a crossing") ---------
#
# A trait object holds an immutable user type's parts; a kept value must keep the whole object. The
# entry passes the whole object (boxed) only to functions whose workers may keep a trait object:
# `keeps(KeepOf{F}())`, decided here once per function, at archetypes, when its trait module is
# complete. The walk follows internal functions and workers called with the trait object.

"A worker's signature at archetypes for the keep analysis: bounded positions at their archetypes, the rest as declared."
function _keep_sig(m::Method)
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return nothing
    ps = sig.parameters
    (isempty(ps) || ps[1] === typeof(Core.kwcall)) && return nothing     # the positional method reaches the body
    out = Any[ps[1]]
    bounded = false
    for k in 2:length(ps)
        p = ps[k]
        if Base.isvarargtype(p)
            q = Base.unwrapva(p)
            lb = _tobj_lb(q isa TypeVar ? q.ub : q)
            lb === nothing || lb === Union{} ? push!(out, Any) : (push!(out, archetype_tobj(lb)); bounded = true)
            continue
        end
        lb = _tobj_lb(p)
        if lb === nothing || lb === Union{}
            q = p isa TypeVar ? p.ub : p
            push!(out, q)
        else
            push!(out, archetype_tobj(lb))
            bounded = true
        end
    end
    return bounded ? Tuple{out...} : nothing
end

"Whether code compiled for `sig` may keep a trait object; `true` when it cannot be decided."
function _keeps_sig(@nospecialize(sig), seen::Base.IdSet{Any})
    sig in seen && return false
    push!(seen, sig)
    world = Base.get_world_counter()
    res = try
        Base.code_typed_by_type(sig; optimize = false, _check_kw(world)...)
    catch
        return true
    end
    isempty(res) && return false
    for (src, _) in res
        mi = src.parent
        sptypes = mi isa Core.MethodInstance ? _CC.sptypes_from_meth_instance(mi) : _CC.EMPTY_SPTYPES
        returned = Base.IdSet{Int}()
        for st in src.code
            st isa Core.ReturnNode && isdefined(st, :val) && st.val isa Core.SSAValue && push!(returned, st.val.id)
        end
        for (i, st) in enumerate(src.code)
            ex = st isa Expr && st.head === :(=) ? st.args[2] : st
            ex isa Expr || continue
            if ex.head === :new
                # a closure that captured a trait object and is returned keeps it
                CT = _CC.argextype(ex.args[1], src, sptypes)
                CT = CT isa _CC.Const ? CT.val : _CC.widenconst(CT)
                CT isa DataType && CT <: Type && (CT = CT.parameters[1])
                if CT isa DataType && CT <: Function && any(k -> _hastobj(fieldtype(CT, k)), 1:fieldcount(CT))
                    i in returned && return true
                end
                continue
            end
            ex.head === :call || continue
            ats = Any[_CC.widenconst(_CC.argextype(a, src, sptypes)) for a in ex.args]
            any(k -> _hastobj(ats[k]), 2:length(ats)) || continue
            fT = _CC.argextype(ex.args[1], src, sptypes)
            f = fT isa _CC.Const ? fT.val : (Base.issingletontype(_CC.widenconst(fT)) ? _CC.widenconst(fT).instance : nothing)
            f === nothing && return true                                     # not known here: assume it keeps
            (f isa Core.Builtin || f isa Core.IntrinsicFunction) && continue
            _keeps_dynamic(f, ats, ex, src, sptypes) && return true
            ms = Base._methods_by_ftype(Tuple{ats...}, -1, world)
            ms isa Vector || return true
            for mm in ms
                m = mm.method
                Base.moduleroot(m.module) === TraitWorld && continue        # the machinery: operations, fields, `like`
                (_isworker(m) || (_is_trait_module_code(m) && !_is_entry(m))) || continue
                _keeps_sig(Tuple{ats...}, seen) && return true
                break                                                        # the call's signature is walked once
            end
        end
    end
    return false
end

"Whether any worker of `f` may keep a trait object (see `keeps`)."
function _analyze_keeps(@nospecialize(f))
    seen = Base.IdSet{Any}()
    try
        for m in methods(f)
            _isworker(m) || continue
            sig = _keep_sig(m)
            sig === nothing && return true
            _keeps_sig(sig, seen) && return true
        end
    catch
        return true                                  # not decided: the entry keeps the whole object
    end
    return false
end

"Define `keeps(KeepOf{typeof(f)}())` in `mod`, once its methods are known; redefined only when the answer changes."
function _fix_keeps!(mod::Module, @nospecialize(f))
    K = _latest(_analyze_keeps, f)::Bool
    P = KeepOf{typeof(f)}
    m = Base._which(Tuple{typeof(keeps),P}; raise = false)
    if m !== nothing && Base.unwrap_unionall(m.method.sig).parameters[2] === P
        Base.invokelatest(keeps, P()) === K && return nothing
        m.method.module === mod || ccall(:jl_generating_output, Cint, ()) == 0 || return nothing
    elseif K
        return nothing                                                       # the fallback says yes already
    end
    Core.eval(mod, :($TraitWorld.keeps(::$P) = $K))
    return nothing
end
