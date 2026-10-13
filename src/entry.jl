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
The builders of one entry position, by user type. Stamped with the world it
was filled in: any method definition (a new projection, say) empties it, and
so does loading it from a package image, whose builders may hold erased
pointers of another session.
"""
mutable struct EntryCache
    world::UInt
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
    if c.world == Base.get_world_counter()
        b = get(c.builders, typeof(t), nothing)
        b === nothing || return b === NOTRAIT ? NOTRAIT : b(t)
    end
    return Base.inferencebarrier(_enter_slow)(c, f, pos, nargs, t)
end

@noinline function _enter_slow(c::EntryCache, @nospecialize(f), pos::Int, nargs::Int, @nospecialize(t))
    w = Base.get_world_counter()
    if c.world != w
        empty!(c.builders)
        c.world = w
    end
    b = Base.invokelatest(_builder, f, pos, nargs, typeof(t))
    c.builders[typeof(t)] = b
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
    throw(MethodError(f, args))
end

# --- Callable ------------------------------------------------------------------

const _FROM_TW = IdDict{Any,Bool}()
"Whether a value's type belongs to the trait world (Julia, TraitWorld, a trait module); cached per type."
function _from_trait_world(@nospecialize(f))
    T = typeof(f)
    v = get(_FROM_TW, T, nothing)
    v === nothing || return v::Bool
    v = is_trait_world(T.name.module)
    _FROM_TW[T] = v
    return v
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
        c = get(_CALLABLE, key, nothing)
        c === nothing || return c
        c = _wrap_callable(A, S, spec, f)
        _CALLABLE[key] = c
        return c
    end
    return _wrap_callable(A, S, spec, f)
end
const _CALLABLE = Dict{Any,Any}()
function _wrap_callable(::Type{A}, ::Type{S}, spec::Bool, @nospecialize(f)) where {A,S}
    (spec || _from_trait_world(f)) && return CObj{A,S}(f)
    return CObj{A,S}(Erased{A,S}(f))
end

"A function argument with several `Callable` bounds: one `CObj` per signature."
enter_callables(sigs::Tuple, spec::Bool, @nospecialize(f)) =
    f isa CMulti ? f : CMulti(map(s -> enter_callable(s[1], s[2], spec, f), sigs))
