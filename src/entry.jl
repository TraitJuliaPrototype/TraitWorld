# ---------------------------------------------------------------------------
# Entries: where ordinary code calls into a trait module (rule 2). An entry
# finds, per trait position, the traits the function's workers need there,
# projects the value once per trait (once for a joint projection), and calls
# the worker. A builder is compiled per user type: the projection per type.
# ---------------------------------------------------------------------------

struct NoTrait end
"Returned by `enter` when a value has none of the traits a position needs: the entry then calls the untyped fallback."
const NOTRAIT = NoTrait()

"Tag for a trait module's untyped fallback of a function that also has trait-bounded methods: `f(x) = …` becomes `f(::Untyped, x) = …`."
struct Untyped end

struct TraitBoundError <: Exception
    msg::String
end
Base.showerror(io::IO, e::TraitBoundError) = print(io, "TraitBoundError: ", e.msg)

"One projection and the views it serves: `p(t)::R`, then one view per trait (with supertraits)."
struct Group{P,R,WS<:Tuple}
    p::P
    ws::WS
end
Group{R}(p::P, ws::WS) where {P,R,WS} = Group{P,R,WS}(p, ws)

"Builds the trait object for one argument of a user type: compiled per type."
struct Builder{G<:Tuple}
    groups::G
end
@inline (b::Builder)(t) = TObj(_build(t, b.groups...))
@inline _build(t) = ()
@inline _build(t, g::Group, rest...) = (_gviews(g, t)..., _build(t, rest...)...)
@inline function _gviews(g::Group{P,R}, t) where {P,R}
    r = g.p(t)::R
    return _subviews(r, g.ws...)
end

"""
TraitWorld's generation: bumped by everything that can change what an entry
builds (`@trait`, `@implement`, a trait-bounded definition, a package load,
`refresh!()`), but not by unrelated method definitions, so code that defines
methods in a loop does not rebuild every entry. Plain methods that a generic
implementation's predicate reads (`eltype` of a user type) must exist before
the first call, or be followed by `TraitWorld.refresh!()`.
"""
const GENERATION = Ref{UInt}(1)
_bump!() = (GENERATION[] += 1; nothing)
"Forget every cached entry builder: after defining methods a generic implementation's predicate reads."
refresh!() = _bump!()

"One lock for the machinery's slow paths: concurrent first calls must not race on its caches."
const _LOCK = ReentrantLock()

"""
The builders of one entry position, by user type. Stamped with the
generation it was filled in; a cache loaded from a package image is stale
(generation 0 there, and its builders may hold erased pointers of another session).
"""
mutable struct EntryCache
    gen::UInt
    builders::IdDict{Any,Any}
end
EntryCache() = EntryCache(UInt(0), IdDict{Any,Any}())

"Set by `verify_main(…; entrypoints = true)` in a trimmed build: entry caches are complete and nothing may be loaded."
const CLOSED_WORLD = Ref(false)

"""
    enter(cache, f, pos, nargs, t)

The trait object for argument `pos` of a call to `f` from ordinary code, or
`NOTRAIT` if `t` has none of the traits `f` needs there.
"""
# Not inlined: verify_main recognizes the call, and the entry stays one small
# piece of code. Its error paths and slow paths are behind inference barriers:
# a static call to a function that formats a message or reflects would give
# every entry an inference edge into Base's string and method-table code,
# which an unrelated package load can invalidate (session 19: loading
# DataFrames invalidated every entry through `_rule3_error`'s message).
@noinline function enter(c::EntryCache, f::F, pos::Int, nargs::Int, @nospecialize(t)) where {F}
    t isa TObj && Base.inferencebarrier(_rule3_error)(f, pos, t)
    if CLOSED_WORLD[]
        b = get(c.builders, typeof(t), nothing)
        b === nothing && Base.inferencebarrier(_closed_miss)(f, t)
        return b === NOTRAIT ? NOTRAIT : b(t)
    end
    if c.gen == GENERATION[]
        b = get(c.builders, typeof(t), nothing)          # copy-on-write: read without the lock
        b === nothing || return b === NOTRAIT ? NOTRAIT : b(t)
    end
    return Base.inferencebarrier(_enter_slow)(c, f, pos, nargs, t)
end

@noinline function _enter_slow(c::EntryCache, @nospecialize(f), pos::Int, nargs::Int, @nospecialize(t))
    b = Base.invokelatest(_builder, f, pos, nargs, typeof(t))
    @lock _LOCK begin
        d = c.gen == GENERATION[] ? copy(c.builders) : IdDict{Any,Any}()
        d[typeof(t)] = b
        c.builders = d                                  # readers see the old table or the new one
        c.gen = GENERATION[]
    end
    return b === NOTRAIT ? NOTRAIT : b(t)
end

@noinline _closed_miss(@nospecialize(f), @nospecialize(t)) =
    error("closed world: `$f` was not verified for an argument of type $(typeof(t))")

@noinline function _rule3_error(@nospecialize(f), pos::Int, @nospecialize(t))
    throw(TraitBoundError("a trait object carrying $(_traitlist(typeof(t))) reached the entry of `$f` at argument $pos, " *
                          "whose methods need other traits there. Inside the trait world a value is passed on only where " *
                          "its own trait is expected (rule 3): declare every bound the callee needs, so the caller projects each."))
end

_traitlist(::Type{TObj{T,V}}) where {T,V} = join(string.(Base.uniontypes(T)), ", ")

"The lower bound of a worker's trait position, `TObj{T} where T >: Union{…}`, or `nothing`."
function _tobj_lb(@nospecialize(p))
    q = Base.unwrap_unionall(p)
    q isa DataType && q.name === Base.typename(TObj) || return nothing
    T = q.parameters[1]
    T isa TypeVar && return T.lb
    return T
end

"""
The traits the workers of `f` with `nargs` arguments need at position `pos`;
`nargs == -1` is a vararg position, served by vararg methods only.
"""
function traits_at(@nospecialize(f), pos::Int, nargs::Int)
    out = Any[]
    for m in methods(f)
        # typed loops, no slicing through Any: the slow path's code must not acquire edges into generic Base code
        sig = Base.unwrap_unionall(m.sig)
        sig isa DataType || continue
        ps = sig.parameters::Core.SimpleVector
        n = length(ps) - 1
        isva = n >= 1 && Base.isvarargtype(ps[end])
        fixed = isva ? n - 1 : n
        if nargs == -1
            isva || continue
        else
            (isva ? nargs >= fixed : nargs == fixed) || continue
        end
        p = pos <= fixed ? ps[pos + 1] : isva ? Base.unwrapva(ps[end]) : continue
        lb = _tobj_lb(p)
        (lb === nothing || lb === Union{}) && continue
        for X in Base.uniontypes(lb)
            _hasid(out, X) || push!(out, X)
        end
    end
    return out
end
"Identity membership by a loop: `any(x -> x === y, v)` on a `Vector{Any}` is generic Base code whose edges unrelated loads invalidate."
_hasid(v::Vector{Any}, @nospecialize(x)) = (for y in v; y === x && return true; end; false)

"The trait objects of a vararg position, one per element, or `NOTRAIT` if an element has none of its traits."
@noinline function enter_each(c::EntryCache, f::F, pos::Int, ts::Tuple) where {F}
    vs = map(t -> enter(c, f, pos, -1, t), ts)
    any(v -> v === NOTRAIT, vs) && return NOTRAIT
    return vs
end

"""
    enter_kw(cache, traits, f, k, nt)

A bounded keyword: if `k` was supplied, its value is projected for `traits`
(a tuple, known from the bound) and replaced in the named tuple of supplied
keywords; a value that conforms to none of them is refused at the entry.
"""
@noinline function enter_kw(c::EntryCache, traits::Tuple, f::F, k::Symbol, nt::NamedTuple) where {F}
    haskey(nt, k) || return nt
    t = getfield(nt, k)
    t isa TObj && return nt
    if CLOSED_WORLD[] || c.gen == GENERATION[]
        b = get(c.builders, typeof(t), nothing)
        if b !== nothing
            b === NOTRAIT && Base.inferencebarrier(_kw_refused)(f, k, t, traits)
            return merge(nt, NamedTuple{(k,)}((b(t),)))
        end
        CLOSED_WORLD[] && Base.inferencebarrier(_closed_miss)(f, t)
    end
    b = Base.inferencebarrier(_enter_kw_slow)(c, traits, typeof(t))
    b === NOTRAIT && Base.inferencebarrier(_kw_refused)(f, k, t, traits)
    return merge(nt, NamedTuple{(k,)}((b(t),)))
end
@noinline function _enter_kw_slow(c::EntryCache, traits::Tuple, @nospecialize(U))
    b = Base.invokelatest(_builder_for, collect(Any, traits), U)
    @lock _LOCK begin
        d = c.gen == GENERATION[] ? copy(c.builders) : IdDict{Any,Any}()
        d[U] = b
        c.builders = d
        c.gen = GENERATION[]
    end
    return b
end
@noinline _kw_refused(@nospecialize(f), k::Symbol, @nospecialize(t), traits::Tuple) =
    throw(TraitBoundError("keyword `$k` of `$f`: a value of type $(typeof(t)) conforms to none of $(join(string.(traits), ", "))"))

"A `Callable` keyword: wrapped like a positional one if supplied."
@noinline function enter_kw_callable(::Type{A}, ::Type{S}, @nospecialize(M), k::Symbol, nt::NamedTuple) where {A,S}
    haskey(nt, k) || return nt
    return merge(nt, NamedTuple{(k,)}((enter_callable(A, S, M, getfield(nt, k)),)))
end

_builder(@nospecialize(f), pos::Int, nargs::Int, @nospecialize(U)) = _builder_for(traits_at(f, pos, nargs), U)

"The builder of a trait object carrying the traits `needed` for a value of type `U`, or `NOTRAIT`."
function _builder_for(needed::Vector{Any}, @nospecialize(U))
    found = Any[]                    # (X, ProjRec)
    for X in needed
        p = proj_lookup(X, U)
        p === nothing || push!(found, (X, p))
    end
    isempty(found) && return NOTRAIT
    # one group per projection function: a joint projection runs once
    groups = Any[]                   # (p::ProjRec, traits)
    for (X, p) in found
        i = 0
        for (k, g) in enumerate(groups)
            q = g[1]::ProjRec
            if q.project === p.project && q.R === p.R
                i = k
                break
            end
        end
        i == 0 ? push!(groups, (p, Any[X])) : push!(groups[i][2]::Vector{Any}, X)
    end
    seen = Any[]
    built = Any[]
    for (p, traits) in groups
        ws = Any[]
        for X in traits, Y in trait_closure(X)
            _hasid(seen, Y) && continue
            push!(seen, Y)
            w = Y === X ? proj_witness(X, U, p) : witness(Y, p.R)
            w === nothing && throw(TraitBoundError("$(U) projects onto $(p.R) for $X, but $(p.R) does not implement $Y"))
            push!(ws, Wit{Y}(w))
        end
        wst = Tuple(ws)
        push!(built, Group{p.R}(p.project, wst))
    end
    return Builder(Tuple(built))
end

"Whether `f` has the tagged untyped fallback for these arguments (a vararg entry accepts the tag too, so `hasmethod` is not enough)."
function _has_tagged_fallback(f::F, args) where {F}
    m = _match(Tuple{F,Untyped,map(typeof, args)...}, Base.get_world_counter())
    m === nothing && return false
    ps = Base.unwrap_unionall(m.method.sig).parameters
    return length(ps) >= 2 && ps[2] === Untyped
end

"""
The untyped fallback of `f`, if the trait module defined one; else any other
ordinary method plain Julia would have called, the most specific one that is
neither an entry nor a worker (`g(x, y)` next to `g(t::ColTable, x::Int)`);
else a `MethodError`. Both the reflection and the call through the method
found are behind barriers: an entry must have no inference edge into them
(session 19: `invoke` with a computed signature reached `promote`, which
ColorVectorSpace extends, so loading Makie invalidated every entry).
"""
function fallback(f::F, args...) where {F}
    CLOSED_WORLD[] && return f(Untyped(), args...)
    Base.inferencebarrier(_has_tagged_fallback)(f, args)::Bool && return f(Untyped(), args...)
    return Base.inferencebarrier(_fallback_plain)(nothing, f, args)
end

"The untyped fallback of a function with keyword arguments."
function kwfallback(nt::NamedTuple, f::F, args...) where {F}
    CLOSED_WORLD[] && return Core.kwcall(nt, f, Untyped(), args...)
    Base.inferencebarrier(_has_tagged_fallback)(f, args)::Bool && return Core.kwcall(nt, f, Untyped(), args...)
    return Base.inferencebarrier(_fallback_plain)(nt, f, args)
end

@noinline function _fallback_plain(@nospecialize(nt), @nospecialize(f), args::Tuple)
    m = _plain_method(f, Tuple{Core.Typeof(f),map(typeof, args)...})
    m === nothing && throw(MethodError(f, args))
    body = Base.unwrap_unionall(m.sig)
    sig = Base.rewrap_unionall(Tuple{body.parameters[2:end]...}, m.sig)
    nt === nothing && return invoke(f, sig, args...)
    return invoke(f, sig, args...; nt...)
end

"An entry: a `@nospecialize` method of a trait module (only entries are generated that way)."
_is_entry(m::Method) = m.nospecialize != 0 && isdefined(m.module, :__tw_entries__)

function _plain_method(@nospecialize(f), @nospecialize(sig))
    # all applicable methods: a method lookup would drop those the entry covers
    cands = Method[m for m in methods(f) if sig <: m.sig && !_isworker(m) && !_is_entry(m)]
    isempty(cands) && return nothing
    best = cands[1]
    for m in cands[2:end]
        Base.morespecific(m.sig, best.sig) && (best = m)
    end
    # ambiguous among themselves: as plain Julia, no answer
    any(m -> m !== best && !Base.morespecific(best.sig, m.sig), cands) && return nothing
    return best
end

# --- Callable ------------------------------------------------------------------

const _FROM_TW = Ref(IdDict{Any,Bool}())          # copy-on-write
"Whether a value's type belongs to the trait world (Julia, TraitWorld, a trait module); cached per type."
function _from_trait_world(@nospecialize(f))
    T = typeof(f)
    v = get(_FROM_TW[], T, nothing)
    v === nothing || return v::Bool
    v = Base.inferencebarrier(_tw_type)(T, Base.IdSet{Any}())::Bool
    @lock _LOCK begin
        d = copy(_FROM_TW[]); d[T] = v; _FROM_TW[] = d
    end
    return v
end
"""
A type of the trait world, all the way down: `Base.Fix1(userf, x)` and
`userf ∘ g` are Base's types around a function from above, so they are not.
An abstract field could hold anything, so it is not either.
"""
function _tw_type(@nospecialize(T), seen)
    T isa DataType || return false
    T in seen && return true
    push!(seen, T)
    is_trait_world(T.name.module) || return false
    for i in 1:fieldcount(T)
        FT = fieldtype(T, i)
        (FT isa DataType && isconcretetype(FT)) || return false
        _tw_type(FT, seen) || return false
    end
    return true
end

"""
    enter_callable(A, S, M, f)

A function handed down from ordinary code, for a `Callable{A, S, M}` argument.
The mode comes from the value's wrapper (`compiled_call(f)`, `dynamic_call(f)`)
if there is one, else from the bound (`M`, or `DynamicCall` when the bound
leaves it open). Functions from the trait world are always passed as
themselves; a function from above is erased to a pointer under `DynamicCall`.
"""
@noinline function enter_callable(::Type{A}, ::Type{S}, @nospecialize(M), @nospecialize(f)) where {A,S}
    f isa CObj{A,S} && return f
    if f isa CallAs
        W = typeof(f)
        FA, FS = W.parameters[2], W.parameters[3]
        (FA === Nothing || (FA === A && FS === S)) || Base.inferencebarrier(_callas_mismatch)(FA, FS, A, S)
        M = W.parameters[1]
        f = f.f
    end
    M === nothing && (M = DynamicCall)
    CLOSED_WORLD[] && return CObj{A,S}(f)          # every function is known: no erasure
    T = typeof(f)
    if Base.issingletontype(T)
        # functions that capture nothing (Base's `abs2`, a closure without state): one wrapper per type
        key = (A, S, M, T)
        c = get(_CALLABLE[], key, nothing)               # copy-on-write: read without the lock
        c === nothing || return c
        c = _wrap_callable(A, S, M, f)
        @lock _LOCK begin
            d = copy(_CALLABLE[]); d[key] = c; _CALLABLE[] = d
        end
        return c
    end
    return _wrap_callable(A, S, M, f)
end
const _CALLABLE = Ref(Dict{Any,Any}())           # copy-on-write
@noinline _callas_mismatch(@nospecialize(FA), @nospecialize(FS), @nospecialize(A), @nospecialize(S)) =
    throw(TraitBoundError("a function wrapped for the signature $FA -> $FS was passed where Callable{$A, $S} is expected"))
function _wrap_callable(::Type{A}, ::Type{S}, @nospecialize(M), @nospecialize(f)) where {A,S}
    (M === CompiledCall || _from_trait_world(f)) && return CObj{A,S}(f)
    return CObj{A,S}(Erased{A,S}(f))
end

"A function argument with several `Callable` bounds: one `CObj` per signature."
function enter_callables(sigs::Tuple, @nospecialize(f))
    f isa CMulti && return f
    f isa CallAs && (M = typeof(f).parameters[1]; f = f.f; sigs = map(s -> (s[1], s[2], M), sigs))
    return CMulti(map(s -> enter_callable(s[1], s[2], s[3], f), sigs))
end
