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
# not inlined: verify_main recognizes the call, and the entry stays one small piece of code
@noinline function enter(c::EntryCache, f::F, pos::Int, nargs::Int, @nospecialize(t)) where {F}
    t isa TObj && _rule3_error(f, pos, t)
    if CLOSED_WORLD[]
        b = get(c.builders, typeof(t), nothing)
        b === nothing && _closed_miss(f, t)
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

"The traits the workers of `f` with `nargs` arguments need at position `pos`."
function traits_at(@nospecialize(f), pos::Int, nargs::Int)
    out = Any[]
    for m in methods(f)
        sig = Base.unwrap_unionall(m.sig)
        length(sig.parameters) == nargs + 1 || continue
        lb = _tobj_lb(sig.parameters[pos+1])
        lb === nothing && continue
        for X in Base.uniontypes(lb)
            any(y -> y === X, out) || push!(out, X)
        end
    end
    return out
end

function _builder(@nospecialize(f), pos::Int, nargs::Int, @nospecialize(U))
    needed = traits_at(f, pos, nargs)
    found = Any[]                    # (X, ProjRec)
    for X in needed
        p = proj_lookup(X, U)
        p === nothing || push!(found, (X, p))
    end
    isempty(found) && return NOTRAIT
    # one group per projection function: a joint projection runs once
    groups = Any[]                   # (p::ProjRec, traits)
    for (X, p) in found
        i = findfirst(g -> g[1].project === p.project && g[1].R === p.R, groups)
        i === nothing ? push!(groups, (p, Any[X])) : push!(groups[i][2], X)
    end
    seen = Any[]
    built = Any[]
    for (p, traits) in groups
        ws = Any[]
        for X in traits, Y in trait_closure(X)
            any(s -> s === Y, seen) && continue
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

"The untyped fallback of `f`, if the trait module defined one; a `MethodError` otherwise."
function fallback(f::F, args...) where {F}
    CLOSED_WORLD[] && return f(Untyped(), args...)
    hasmethod(f, Tuple{Untyped,map(typeof, args)...}) && return f(Untyped(), args...)
    # any other ordinary method plain Julia would have called: the most specific one
    # that is neither an entry nor a worker (`g(x, y)` next to `g(t::ColTable, x::Int)`)
    m = Base.invokelatest(_plain_method, f, Tuple{F,map(typeof, args)...})
    m === nothing && throw(MethodError(f, args))
    body = Base.unwrap_unionall(m.sig)
    return invoke(f, Base.rewrap_unionall(Tuple{body.parameters[2:end]...}, m.sig), args...)
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
    v = _tw_type(T, Base.IdSet{Any}())
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
    enter_callable(A, S, spec, f)

A function handed down from ordinary code, for a `Callable{A, S}` argument.
Functions from the trait world are always passed as themselves (specialized);
a function from above is erased unless the library marked the argument
`@specialize`.
"""
@noinline function enter_callable(::Type{A}, ::Type{S}, spec::Bool, @nospecialize(f)) where {A,S}
    f isa CObj{A,S} && return f
    CLOSED_WORLD[] && return CObj{A,S}(f)          # every function is known: no erasure
    T = typeof(f)
    if Base.issingletontype(T)
        # functions that capture nothing (Base's `abs2`, a closure without state): one wrapper per type
        key = (A, S, spec, T)
        c = get(_CALLABLE[], key, nothing)               # copy-on-write: read without the lock
        c === nothing || return c
        c = _wrap_callable(A, S, spec, f)
        @lock _LOCK begin
            d = copy(_CALLABLE[]); d[key] = c; _CALLABLE[] = d
        end
        return c
    end
    return _wrap_callable(A, S, spec, f)
end
const _CALLABLE = Ref(Dict{Any,Any}())           # copy-on-write
function _wrap_callable(::Type{A}, ::Type{S}, spec::Bool, @nospecialize(f)) where {A,S}
    (spec || _from_trait_world(f)) && return CObj{A,S}(f)
    return CObj{A,S}(Erased{A,S}(f))
end

"A function argument with several `Callable` bounds: one `CObj` per signature."
enter_callables(sigs::Tuple, spec::Bool, @nospecialize(f)) =
    f isa CMulti ? f : CMulti(map(s -> enter_callable(s[1], s[2], spec, f), sigs))
