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

"A stand-in representation of trait `X`: library code checked against `X` alone."
struct Archetype{X} end

"The witness of an archetype's view: an operation answers with a value of its declared type, nothing more."
struct ArchWit end

# never run, only inferred: `opcall` asserts the declared result type of whatever comes back
@inline _dispatch(::Type{X}, ::Val{op}, f::F, w::ArchWit, r, t, args...) where {X,op,F} = Base.inferencebarrier(nothing)

"The traits a view of `X` brings: `X` and its supertraits, or the traits a bundle names."
function _arch_traits(@nospecialize(X), out = Any[])
    b = bundle(X)
    if b !== nothing
        for Y in b
            _arch_traits(Y, out)
        end
        return out
    end
    _hasid(out, X) || push!(out, X)
    for S in supertraits(X)
        _arch_traits(S, out)
    end
    return out
end

"""
    archetype_tobj(lb)

The trait object a worker sees at a position bounded by the traits in `lb`,
each bound at its own archetype, its supertraits' views sharing it.
"""
function archetype_tobj(@nospecialize(lb))
    views = Any[]
    for X in Base.uniontypes(lb)
        for Y in _arch_traits(X)
            push!(views, View{Y,ArchWit,Archetype{X}})
        end
    end
    T = Union{Any[v.parameters[1] for v in views]...}
    return TObj{T,Tuple{views...}}
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
            push!(out, archetype_tobj(lb))
            bounded = true
        end
    end
    return bounded ? Tuple{out...} : nothing
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
with its trait objects, the globals and doors it reaches, independent of any
representation. Methods checked clean are recorded, so their workers' first
calls skip the check per signature.
"""
function definition_problems(@nospecialize(f))
    out = String[]
    for m in methods(f)
        asig = archetype_sig(m)
        asig === nothing && continue
        ps = Base.invokelatest(worker_problems, asig)::Vector{String}
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
