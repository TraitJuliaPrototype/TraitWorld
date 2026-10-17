# ---------------------------------------------------------------------------
# Entries: where ordinary code calls into a trait module (rule 2). The runtime
# is ordinary methods, so Julia's own dispatch does the lookups
# (explorations/keys-plan.md §6):
#
#   - a conformance is a method, `conformance(X, u::U)`, defined by
#     `@implement`: it builds the trait object's views of `X` (and its
#     supertraits) for a `U`, from constants;
#   - an entry is an ordinary `@inline` method, `@nospecialize` on its trait
#     arguments: `enter(EntryPos{F, pos, nargs}, t)` makes the trait object
#     from the traits the function's workers need there (`needed`), and
#     `checked_call` calls the worker for its keys. A typed caller inlines the
#     entry and runs at plain-Julia speed; an untyped caller pays a dispatch;
#   - generic implementations and families have no method per type: their
#     conformance is found by the fallback, `_conformance_slow`, and cached.
#
# `conformance` is declared with `@max_methods 1` and has a fallback, so code
# compiled at `conformance(X, ::Any)` infers nothing from its methods, holds
# no edge to them, and a new conformance invalidates nothing (a new type's
# method would otherwise change what such code inferred, and invalidate it).
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

"""
How a builder makes one trait's view for a user type: the witness, the slot of the
implementing value (the object itself, or its forwarding field), and the slots of the
declared fields. The view's type is `View{X, W, K, N, P}`, the same for every user type of key `K`.
"""
struct VSpec{X,W,K,N,P}
    w::W
    r::Slot
    fs::NTuple{N,Slot}
end

"Builds the trait object of one argument of a user type: the user's object, or its parts held, with a view per trait."
struct Builder{S<:Tuple}
    specs::S
end
@inline (b::Builder)(t) = TObj(_build(t, getfield(b, :specs)...))
@inline _build(t) = ()
@inline _build(t, s::VSpec{X,W,K,N,P}, rest...) where {X,W,K,N,P} =
    (View{X,W,K,N,P}(getfield(s, :w), ismutable(t) ? t : nothing, getfield(s, :r), getfield(s, :fs),
                     _parts(P, t, getfield(s, :r), getfield(s, :fs))), _build(t, rest...)...)

"""
The parts a view holds, typed by the key: the implementing value (`nothing` when there
is none) and the declared fields' values, read from the user's object. For a mutable
object they are what the object holds now; reads go through the object.
"""
@generated function _parts(::Type{P}, t, r::Slot, fs::NTuple{N,Slot}) where {P,N}
    ts = P.parameters
    first = ts[1] === Nothing ? :nothing :
            :((getfield(r, :off) < 0 ? t : getfield(t, getfield(r, :idx)))::$(ts[1]))
    rest = [:(getfield(t, getfield(fs[$i], :idx))::$(ts[i + 1])) for i in 1:N]
    return :(($first, $(rest...)))
end
"The type of a view's parts at key `K`."
_partstype(@nospecialize(K)) = K <: Key ? Tuple{_impl(K), K.parameters[2].parameters[2].parameters...} : Tuple{K}

"""
TraitWorld's generation: bumped by everything that can change what the slow path
builds (`@trait`, `@implement`, a trait-bounded definition, a package load,
`refresh!()`), but not by unrelated method definitions. Plain methods that a generic
implementation's predicate reads (`eltype` of a user type) must exist before the first
call, or be followed by `TraitWorld.refresh!()`.
"""
const GENERATION = Ref{UInt}(1)
_bump!() = (GENERATION[] += 1; nothing)
"Forget every cached conformance of the slow path: after defining methods a generic implementation's predicate reads."
refresh!() = _bump!()

"One lock for the machinery's slow paths: concurrent first calls must not race on its caches."
const _LOCK = ReentrantLock()

"""
The method match of a call signature in `world`, or `nothing`: the runtime's
own lookup, called directly. `Base._which` goes through the compiler's
`findsup_mt`, whose compiled code unrelated loads invalidate (DataFrames'
dependencies do, through `convert(UInt, Integer)`), which put a recompile of
Base on the first call of every session (session 19).
"""
function _match(@nospecialize(sig), world::UInt)
    min_valid = Ref{UInt}(typemin(UInt))
    max_valid = Ref{UInt}(typemax(UInt))
    r = ccall(:jl_gf_invoke_lookup_worlds, Any, (Any, Any, UInt, Ptr{Csize_t}, Ptr{Csize_t}),
              sig, nothing, world, min_valid, max_valid)
    return r === nothing ? nothing : r::Core.MethodMatch
end
"Set by `verify_main(…; entrypoints = true)` in a trimmed build: the slow path's cache is complete and nothing may be loaded."
const CLOSED_WORLD = Ref(false)

# --- conformances as methods -----------------------------------------------------

"A trait as a value to dispatch on: `As{ColTable}()`. Dispatch on a singleton is cached by its type; on a type value (`::Type{ColTable}`) it is several times slower."
struct As{X} end

Base.Experimental.@max_methods 1 function conformance end
"""
    conformance(As{X}(), u)

The trait object of `u` carrying trait `X` (with its supertraits), or `NOTRAIT`. `@implement`
defines a method per conforming type; the fallback finds generic implementations and
families, and caches what it finds.
"""
conformance(::As{X}, @nospecialize(u)) where {X} = Base.inferencebarrier(_conformance_slow)(X, u)

"""
The conformance a declaration makes, as a method body: the views from a builder fixed when
the conformance was declared, or the slow path for a conformance whose witness holds
pointers of a session (a type's own operations called dynamically).
"""
@inline _conf_call(b::Builder, ::Type{X}, u) where {X} = b(u)
@inline _conf_call(::Nothing, ::Type{X}, u) where {X} = Base.inferencebarrier(_conformance_slow)(X, u)

"The builder a conformance of `T` to `X` is fixed to when declared, or `nothing` when it must be built in each session."
function _conformance_builder(@nospecialize(X), @nospecialize(T))
    p = proj_lookup(X, T)
    p === nothing && return nothing
    p.dyn === nothing || return nothing             # erased pointers belong to a session
    b = _builder_for(Any[X], T)
    return b isa Builder ? b : nothing
end

const _SLOW = Ref(IdDict{Any,Any}())                  # Pair(X, U) => Builder or NOTRAIT; copy-on-write
const _SLOW_WORLD = Ref{UInt}(0)                  # the world `_SLOW` was decided in: any definition makes it stale
"The conformance of a type with no method of its own: a generic implementation, a family, a dynamic one."
@noinline function _conformance_slow(@nospecialize(X), @nospecialize(u))
    U = typeof(u)
    key = Pair{Any,Any}(X, U)
    w = Base.tls_world_age()                            # decided in the caller's world, as dispatch is
    if CLOSED_WORLD[] || _SLOW_WORLD[] == w
        b = get(_SLOW[], key, nothing)
        b === nothing || return b === NOTRAIT ? NOTRAIT : (b::Builder)(u)
        CLOSED_WORLD[] && Base.inferencebarrier(_closed_miss)(X, u)
    end
    _FACTS_DEBUG[] && Core.println("TraitWorld: conformance slow path: ", X, " for ", U)
    b = _in_world_under_policy(w, _builder_for, Any[X], U)
    b === NOTRAIT || _vc_note_builder(b, U)
    @lock _LOCK begin
        d = _SLOW_WORLD[] == w ? copy(_SLOW[]) : IdDict{Any,Any}()
        d[key] = b
        _SLOW[] = d                                     # readers see the old table or the new one
        _SLOW_WORLD[] = w
    end
    return b === NOTRAIT ? NOTRAIT : (b::Builder)(u)
end

@noinline _closed_miss(@nospecialize(f), @nospecialize(t)) =
    error("closed world: `$f` was not verified for an argument of type $(typeof(t))")

# --- what an entry position needs --------------------------------------------------

"An entry position: argument `pos` of function type `F` called with `nargs` arguments (`-1`: a vararg position)."
struct EntryPos{F,pos,nargs} end
"The traits a bound or a position needs, as a type: `TraitList{Tuple{ColTable, RowTable}}`."
struct TraitList{L<:Tuple} end

Base.Experimental.@max_methods 1 function needed end
"""
    needed(EntryPos{F, pos, nargs}())

The traits the workers of `F` need at a position, as a `TraitList`. A trait module defines a
method per entry position when it is complete (`_finish_module`), and again when a later
definition adds a bound; until then this fallback computes it.
"""
needed
needed(::EntryPos{F,pos,nargs}) where {F,pos,nargs} = Base.inferencebarrier(_needed_slow)(F, pos, nargs)
_needed_slow(@nospecialize(F), pos::Int, nargs::Int) = TraitList{Tuple{traits_at(F.instance, pos, nargs)...}}()

"""
    enter(EntryPos{F, pos, nargs}(), t)

The trait object for argument `pos` of a call from ordinary code, or `NOTRAIT` if `t` has
none of the traits the position needs. Not inlined, so that `verify_main` sees it, but
specialized: for a known type it folds to the views' construction.
"""
@inline function enter(p::EntryPos{F}, t) where {F}
    t isa Dynamic && return opened(t)                  # a dynamic value is opened: its worker is selected by dispatch
    t isa TObj && return Base.inferencebarrier(_rule3_error)(typeof(p), t)
    v = _assemble(needed(p), t)
    # a function that may keep its trait objects gets the whole user's object, also of an immutable
    # type (boxed); every other function holds its parts (`keeps` folds to a constant)
    keeps(KeepOf{F}()) && !ismutable(t) && v isa TObj && return _with_object(v, t)
    return v
end

"A function type as a value to dispatch on, for `keeps`."
struct KeepOf{F} end
Base.Experimental.@max_methods 1 function keeps end
"""
    keeps(KeepOf{F}()) -> Bool

Whether a worker of function type `F` may keep a trait object beyond the call: make it a
`Dynamic`, store it where a `Dynamic` is declared, or return a closure that captured it (note
"Keeping a value is a crossing"). Then its entry passes the whole user's object, also of an
immutable type, so the kept value keeps it (equality, results like the input, serialization). A
trait module defines a method per function when it is complete; until then, and for functions not
analysed, this fallback says yes.
"""
keeps(::KeepOf) = true

"The trait object `v` of the immutable value `t`, its views reading the whole object (boxed) instead of holding its parts."
@inline _with_object(v::TObj, t) = TObj(map(x -> _view_with(x, t), getfield(v, :views)))
@inline _view_with(v::View{X,W,K,N,P}, t) where {X,W,K,N,P} =
    View{X,W,K,N,P}(getfield(v, :w), t, getfield(v, :r), getfield(v, :fs), getfield(v, :parts))
@inline _view_with(v, t) = v

"The trait object carrying every trait of `L` that `t` conforms to, or `NOTRAIT`."
@generated function _assemble(::TraitList{L}, t) where {L}
    Xs = L.parameters
    isempty(Xs) && return :NOTRAIT
    length(Xs) == 1 && return :(conformance($(As{Xs[1]}()), t))     # one trait: its conformance is the trait object
    calls = [:(conformance($(As{X}()), t)) for X in Xs]
    return :(_merge($(calls...)))
end
"The views of several conformances in one trait object, each trait once; `NOTRAIT` if there are none."
@generated function _merge(cs...)
    seen = Any[]
    parts = Any[]
    for (i, C) in enumerate(cs)
        C <: TObj || continue                                # NOTRAIT, or not known here
        for (j, V) in enumerate(C.parameters[2].parameters)
            F = _family(V.parameters[1])
            any(x -> x === F, seen) && continue
            push!(seen, F)
            push!(parts, :(getfield(cs[$i], :views)[$j]))
        end
    end
    if all(C -> (C isa DataType && C <: TObj) || C === NoTrait, cs)
        isempty(parts) && return :NOTRAIT
        return :(TObj(($(parts...),)))
    end
    return :(_merge_dyn(cs))                                 # a slow-path result: its type is known only now
end
@noinline function _merge_dyn(cs::Tuple)
    vs = Any[]
    seen = Any[]
    for c in cs
        c isa TObj || continue
        for v in getfield(c, :views)
            F = _family(typeof(v).parameters[1])
            _hasid(seen, F) && continue
            push!(seen, F)
            push!(vs, v)
        end
    end
    isempty(vs) && return NOTRAIT
    return TObj(Tuple(vs))
end

@noinline function _rule3_error(@nospecialize(P), @nospecialize(t))
    f, pos = P.parameters[1].instance, P.parameters[2]
    throw(TraitBoundError("a trait object carrying $(_traitlist(typeof(t))) reached the entry of `$f` at argument $pos, " *
                          "whose methods need other traits there. Inside the trait world a value is passed on only where " *
                          "its own trait is expected (rule 2): declare every bound the callee needs, so the caller projects each."))
end

_traitlist(::Type{TObj{T,V}}) where {T,V} = join(unique(string.(_family.(Base.uniontypes(_decode_traits(T))))), ", ")

"The lower bound of a worker's trait position, `TObj{T} where T >: Union{…}`, or `nothing`."
function _tobj_lb(@nospecialize(p))
    q = Base.unwrap_unionall(p)
    q isa DataType && q.name === Base.typename(TObj) || return nothing
    T = q.parameters[1]
    T isa TypeVar && return _decode_traits(T.lb)          # as trait patterns (`ColTable{R} where R`)
    return _decode_traits(T)
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
            F = _family(X)                     # a pattern (`ArrayLike{Float64, N, R}`): its trait family
            _hasid(out, F) || push!(out, F)
        end
    end
    return out
end
"Identity membership by a loop: `any(x -> x === y, v)` on a `Vector{Any}` is generic Base code whose edges unrelated loads invalidate."
_hasid(v::Vector{Any}, @nospecialize(x)) = (for y in v; y === x && return true; end; false)

"The trait objects of a vararg position, one per element, or `NOTRAIT` if an element has none of its traits."
@noinline function enter_each(p::EntryPos, ts::Tuple)
    vs = map(t -> enter(p, t), ts)
    any(v -> v === NOTRAIT, vs) && return NOTRAIT
    return vs
end

"""
    enter_kw(L, f, k, nt)

A bounded keyword: if `k` was supplied, its value is translated for the traits `L` (a
`TraitList`, from the bound) and replaced in the named tuple of supplied keywords; a value
that conforms to none of them is refused at the entry.
"""
@noinline function enter_kw(l::TraitList, f::F, k::Symbol, nt::NamedTuple) where {F}
    haskey(nt, k) || return nt
    t = getfield(nt, k)
    t isa TObj && return nt
    v = t isa Dynamic ? opened(t) : _assemble(l, t)
    v === NOTRAIT && Base.inferencebarrier(_kw_refused)(f, k, t, l)
    keeps(KeepOf{F}()) && !(t isa Dynamic) && !ismutable(t) && v isa TObj && (v = _with_object(v, t))
    return merge(nt, NamedTuple{(k,)}((v,)))
end
@noinline _kw_refused(@nospecialize(f), k::Symbol, @nospecialize(t), @nospecialize(l)) =
    throw(TraitBoundError("keyword `$k` of `$f`: a value of type $(typeof(t)) conforms to none of " *
                          "$(join(string.(typeof(l).parameters[1].parameters), ", "))"))

"A `Callable` keyword: wrapped like a positional one if supplied."
@noinline function enter_kw_callable(::Type{A}, ::Type{S}, @nospecialize(M), k::Symbol, nt::NamedTuple) where {A,S}
    haskey(nt, k) || return nt
    return merge(nt, NamedTuple{(k,)}((enter_callable(A, S, M, getfield(nt, k)),)))
end

"The trait patterns each worker of `f` needs at position `pos` (`StateVector{Float64, R}`), one list per method."
function bound_patterns(@nospecialize(f), pos::Int, nargs::Int)
    out = Vector{Any}[]
    for m in methods(f)
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
        push!(out, Any[Base.uniontypes(lb)...])
    end
    return out
end

"Whether trait instance `Xi` satisfies pattern `Yp`: the same trait, and the parameters the pattern fixes."
function _pmatch(@nospecialize(Xi), @nospecialize(Yp))
    _family(Xi) === _family(Yp) || return false
    u = Base.unwrap_unionall(Yp)
    u isa DataType || return true
    for (i, q) in enumerate(u.parameters)
        q isa TypeVar && continue
        i <= length(Xi.parameters) && Xi.parameters[i] == q || return false
    end
    return true
end

"""
A worker signature no method of `f` accepts: a value conforms, but at parameters no bound
accepts. Raised at the signature's first call (`_check_once`), naming the bounds.
"""
function _no_worker_error(@nospecialize(sig))
    ps = sig.parameters
    f = ps[1].instance
    nargs = length(ps) - 1
    for pos in 1:nargs
        T = ps[pos + 1]
        T isa DataType && T <: TObj || continue
        insts = Any[V.parameters[1] for V in T.parameters[2].parameters]
        pats = bound_patterns(f, pos, nargs)
        isempty(pats) && continue
        any(p -> all(Yp -> any(Xi -> _pmatch(Xi, Yp), insts), p), pats) && continue
        need = join(unique([join(string.(Base.rewrap_unionall.(p, Ref(Any))), " and ") for p in pats]), "; or ")
        throw(TraitBoundError("a value conforming as $(join(string.(insts), ", ")) was passed to `$f` at argument $pos, " *
                              "whose bounds need a value conforming at the parameters they fix: $need"))
    end
    throw(TraitBoundError("no trait-bounded method of `$f` accepts trait objects of $(join(string.(ps[2:end]), ", "))"))
end

"The views of a value of type `U` for the traits `needed`: a `Builder`, or `NOTRAIT`."
function _builder_for(needed::Vector{Any}, @nospecialize(U))
    found = Any[]                    # (X, ProjRec)
    for X in needed
        p = proj_lookup(X, U)
        p === nothing || push!(found, (X, p))
    end
    isempty(found) && return NOTRAIT
    seen = Any[]
    specs = Any[]
    for (X, p) in found, Y in trait_closure(X)
        _hasid(seen, Y) && continue
        push!(seen, Y)
        w = Y === X ? proj_witness(X, U, p) : witness(Y, p.R)
        w === nothing && throw(TraitBoundError("$(U) forwards $X to $(p.R), which does not implement $Y"))
        K, fs = _key_and_slots(Y, p, U, w)
        r = p.field == 0 ? SELF : _slot(U, p.field)
        push!(specs, VSpec{_instance(Y, K),typeof(w),K,length(fs),_partstype(K)}(w, r, fs))
    end
    return Builder(Tuple(specs))
end

"The slot of field `i` of type `U`: its byte offset and index."
_slot(@nospecialize(U), i::Int) = Slot(Int(fieldoffset(U, i)), i)
"The stored field of `U` that declared field `f` maps to: written in the conformance, else the same name."
_mapped(p::ProjRec, f::Symbol) = (m = p.fmap; m === nothing ? f : get(m, f, f))
"""
The key of trait `Y` for user type `U` conforming through `p` with witness `w`, and the
slots of `Y`'s declared fields: the implementing type alone for a trait without fields;
else a `Key` with the declared fields' types in `U`. The implementing type is `Nothing`
when there is none (note "Terms"): every operation served by a default, as in a trait with
fields only.
"""
function _key_and_slots(@nospecialize(Y), p::ProjRec, @nospecialize(U), @nospecialize(w))
    fl = trait_fields(Y)
    isempty(fl) && return p.R, ()
    names = Symbol[f for (f, _) in fl]
    idx = Int[Base.fieldindex(U, _mapped(p, f)) for f in names]
    I = _no_implementing_type(Y, w) ? Nothing : p.R
    F = NamedTuple{Tuple(names),Tuple{Any[fieldtype(U, i) for i in idx]...}}
    return Key{I,F}, Tuple(_slot(U, i) for i in idx)
end
"""
Whether a conformance of trait `Y` with witness `w` has no implementing type: every
operation is served by a default (or there are none), the trait's declarations do not name
`Self`, and every parameter is defined by a field, so nothing depends on the type.
"""
function _no_implementing_type(@nospecialize(Y), @nospecialize(w))
    ops = _ops(Y)
    isempty(ops) && return true
    w isa Impl || return false
    D = typeof(w).parameters[1]
    all(op -> op in D, ops) || return false
    Base.invokelatest(trait_uses_self, Y)::Bool && return false
    fps = Base.invokelatest(trait_field_params, Y)::Tuple
    return all(q -> q in fps, trait_params(Y))
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
    T <: Dynamic && return true                         # made only from trait objects: its type decides it
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

"""
    DynamicFn{A, S}

A function in `DynamicCall` mode as a value of fixed type: a pointer to its code compiled for
`A`, its result asserted to `S`. What a library stores in a field for a function from above
(`Callable` in `DynamicCall` mode is already the dynamic value of a function, note "Dynamic
values"): its type does not depend on the function.
"""
const DynamicFn{A,S} = CObj{A,S,Erased{A,S}}
"""
    dynamic_fn(A, S, f) -> DynamicFn{A, S}

`f` as a dynamic call at the signature `A -> S`, made in ordinary code: the boundary's
translation of a `Callable` bound in `DynamicCall` mode, for a library that stores the
function (a model's right-hand side, a callback).
"""
dynamic_fn(::Type{A}, ::Type{S}, f) where {A,S} = f isa DynamicFn{A,S} ? f : CObj{A,S}(Erased{A,S}(f isa CallAs ? f.f : f))

"""
    Dynamic{X}(x)

A dynamic value of a trait-world value `x` that conforms to `X` but is no trait object: a
library's own type (an integrator handed to callbacks as `Dynamic{IntegratorView}`).
"""
function Dynamic{X}(x) where {X}
    x isa TObj && return Dynamic{X}(x::TObj)
    v = _assemble(TraitList{Tuple{_family(X)}}(), x)
    v === NOTRAIT && throw(TraitBoundError("a $(typeof(x)) does not conform to $X"))
    ismutable(x) || (v = _with_object(v, x))           # kept: the whole value, also of an immutable type
    return Dynamic{X}(v)
end

# --- results like the input (note "Results like the input") -----------------------

"Functions with a method declared `::Like{t}`: their workers return a pending result, which their entry makes into the caller's type."
const _LIKE_FUNCS = Base.IdSet{Any}()
_like!(@nospecialize(f)) = (push!(_LIKE_FUNCS, typeof(f)); nothing)

"No new implementing value: a result like the input with only fields replaced."
struct KeepSelf end

"""
A result like the input (note "Results like the input"): the input's trait object, a new
implementing value or `KeepSelf()`, and new values of declared fields. Nothing operates on
it; only the entry inverts it, rebuilding the user's type.
"""
struct LikeResult{T<:TObj,S,F<:NamedTuple}
    t::T
    x::S
    f::F
end

"""
    like(t, x)

A result like `t` holding the new implementing value `x`: what a function declared
`::Like{t}` returns inside the trait world.
"""
@inline like(t::TObj, x) = LikeResult(t, x, NamedTuple())
@inline like(t::TObj, l::LikeResult) = l
"""
    withfields(t; f = v, …)

A result like `t` with declared fields replaced; also on a result of `like`.
"""
@inline withfields(t::TObj; kw...) = LikeResult(t, KeepSelf(), values(kw))
@inline withfields(l::LikeResult; kw...) = LikeResult(l.t, l.x, merge(l.f, values(kw)))

"How an entry returns: a result like the input becomes a value of the caller's type (entries inline this test, building the tuples only for such a result)."
@inline _out(res, us::Tuple, vs::Tuple) = res isa LikeResult ? Base.inferencebarrier(_like_out)(res, us, vs) : res
function _like_out(res::LikeResult, us::Tuple, vs::Tuple)
    for i in eachindex(vs)
        vs[i] === res.t || continue
        u = us[i]
        v = getfield(res.t, :views)[1]
        X = _family(typeof(v).parameters[1])
        if u isa Dynamic
            # a dynamic value in, a dynamic value of the same trait out
            o = getfield(v, :o)
            o === nothing && getfield(getfield(v, :r), :off) >= 0 && throw(TraitBoundError(
                "a dynamic value of an immutable type keeps the parts $X can see, not the whole object, " *
                "so a result like it cannot be rebuilt; pass the value itself"))
            nu = _invert(X, v, o === nothing ? getfield(getfield(v, :parts), 1) : o, res)
            b = _builder_for(Any[X], typeof(nu))
            b === NOTRAIT && throw(TraitBoundError("$(typeof(nu)) does not conform to $X"))
            return typeof(u)(b(nu))
        end
        return _invert(X, v, u, res)
    end
    throw(TraitBoundError("a result like the input names no trait object the entry passed"))
end

"""
The conformance's inverse: a value of the user's type `typeof(u)` with the new parts of `res`.
A type that implements the operations itself is replaced by the new value (of the same type);
otherwise the user's object is rebuilt by its constructor with the forwarding field and the
declared fields replaced, so its parameters follow the new fields.
"""
function _invert(@nospecialize(X), v::View, u, res::LikeResult)
    x = res.x
    r = getfield(v, :r)
    if !(x isa KeepSelf) && getfield(r, :off) < 0
        typeof(x) <: Base.typename(typeof(u)).wrapper ||
            throw(TraitBoundError("$(typeof(u)) implements $X itself, but the result is a $(typeof(x)): " *
                                  "a result like the input must be a $(Base.typename(typeof(u)).wrapper)"))
        u = x
        x = KeepSelf()
    end
    repl = Dict{Int,Any}()
    x isa KeepSelf || (repl[getfield(r, :idx)] = x)
    fs = getfield(v, :fs)
    for (f, val) in pairs(res.f)
        repl[getfield(fs[_fieldpos(X, Val(f))], :idx)] = val
    end
    isempty(repl) && return u
    return _rebuild(u, repl)
end
"A copy of `u` with fields replaced, built by the type's constructor, which recomputes its parameters (`Series{Float32}` from a `Vector{Float32}`)."
function _rebuild(u, repl::Dict{Int,Any})
    U = typeof(u)
    fs = ntuple(j -> haskey(repl, j) ? repl[j] : getfield(u, j), fieldcount(U))
    try
        return Base.typename(U).wrapper(fs...)
    catch e
        e isa MethodError || rethrow()
        throw(TraitBoundError("$U cannot be rebuilt from its fields by its constructor, so a result like it cannot be built"))
    end
end
"An operation returning `Self`, on a dynamic value: a dynamic value of the new value, which implements the trait itself."
function _dyn_like(d::Dynamic{X}, x) where {X}
    t = opened(d)
    v = getfield(t, :views)[1]
    isempty(getfield(v, :fs)) || throw(TraitBoundError("$X declares fields, so a new value of its implementing type alone does not conform"))
    return Dynamic{X}(TObj(map(w -> View{typeof(w).parameters[1]}(getfield(w, :w), x), getfield(t, :views))))
end

# --- membership (note "Traits as abstract types") ----------------------------------

"""
    conforms(T, X)

Whether values of type `T` conform to the bound `X` (`ColTable`, or a trait at fixed
parameters, `StateVector{Float64}`): what `T <: X` means in the design. The package
cannot make it subtyping, so it is a function.
"""
function conforms(@nospecialize(T::Type), @nospecialize(X::Type))
    F = _family(X)
    if T <: Dynamic && T isa DataType
        Y = _family(T.parameters[1])
        return any(Z -> Z === F, trait_closure(Y))
    end
    p = proj_lookup(F, T)
    p === nothing && return false
    return _pmatch(_instance(F, p.R), X)
end
