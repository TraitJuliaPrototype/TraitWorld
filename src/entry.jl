# ---------------------------------------------------------------------------
# Entries: where ordinary code calls into a trait module (rule 2). The runtime
# is ordinary methods, so Julia's own dispatch does the lookups
# (explorations/keys-plan.md §6):
#
#   - an implementation is a method, `conformance(X, u::U)`, defined by
#     `@implement`: it builds the trait object's views of `X` (and its
#     supertraits) for a `U`, from constants;
#   - an entry is an ordinary `@inline` method, `@nospecialize` on its trait
#     arguments: `enter(EntryPos{F, pos, nargs}, t)` makes the trait object
#     from the traits the function's workers need there (`needed`), and
#     `checked_call` calls the worker for its keys. A typed caller inlines the
#     entry and runs at plain-Julia speed; an untyped caller pays a dispatch;
#   - generic implementations and families have no method per type: their
#     implementation is found by the fallback, `_conformance_slow`, and cached.
#
# `conformance` is declared with `@max_methods 1` and has a fallback, so code
# compiled at `conformance(X, ::Any)` infers nothing from its methods, holds
# no edge to them, and a new implementation invalidates nothing (a new type's
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
receiver (the object itself, or its forwarding field), and the slots of the
declared fields. The view's type is `View{X, W, K, N, P}`, the same for every user type of key `K`.
"""
struct VSpec{X,W,K,N,P,S}    # S: the user's type is the key's receiver type (`r` is `SELF`)
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
@inline _build(t, s::VSpec{X,W,K,N,P,S}, rest...) where {X,W,K,N,P,S} =
    (_buildview(t, s, Val(S && !ismutable(t))), _build(t, rest...)...)
# an immutable value that is its own receiver is held whole; any other is read through
# (mutable) or held as parts (an immutable value forwarding to a field)
@inline _buildview(t, s::VSpec{X,W,K,N,P}, ::Val{true}) where {X,W,K,N,P} =
    Held{X,W,K,N,P}(getfield(s, :w), getfield(s, :fs), _parts(P, t, getfield(s, :r), getfield(s, :fs)))
@inline _buildview(t, s::VSpec{X,W,K,N,P}, ::Val{false}) where {X,W,K,N,P} =
    View{X,W,K,N,P}(getfield(s, :w), ismutable(t) ? t : nothing, getfield(s, :r), getfield(s, :fs),
                    _parts(P, t, getfield(s, :r), getfield(s, :fs)))

"""
The parts a view holds, typed by the key: the receiver (`nothing` when there
is none) and the declared fields' values, read from the user's object. For a mutable
object they are what the object holds now; reads go through the object.
"""
@generated function _parts(::Type{P}, t, r::Slot, fs::NTuple{N,Slot}) where {P,N}
    ts = (P::DataType).parameters        # fully typed, as the generators' code must be (see `_carries_static`)
    first = ts[1] === Nothing ? :nothing :
            :((getfield(r, :off) < 0 ? t : getfield(t, getfield(r, :idx)))::$(ts[1]))
    rest = Any[:(getfield(t, getfield(fs[$i], :idx))::$(ts[i + 1])) for i in 1:(N::Int)]
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
_bump!() = (GENERATION[] += 1; _note_conformances!(); nothing)
"Forget every cached implementation of the slow path: after defining methods a generic implementation's predicate reads."
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

# --- implementations as methods -----------------------------------------------------

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
The implementation a declaration makes, as a method body: the views from a builder fixed when
the implementation was declared, or the slow path for an implementation whose witness holds
pointers of a session (a type's own operations called dynamically).
"""
@inline _conf_call(b::Builder, ::Type{X}, u) where {X} = b(u)
@inline _conf_call(::Nothing, ::Type{X}, u) where {X} = Base.inferencebarrier(_conformance_slow)(X, u)

"The builder an implementation of `X` for `T` is fixed to when declared, or `nothing` when it must be built in each session."
function _conformance_builder(@nospecialize(X), @nospecialize(T))
    p = proj_lookup(X, T)
    p === nothing && return nothing
    p.dyn === nothing || return nothing             # erased pointers belong to a session
    b = _builder_for(Any[X], T)
    return b isa Builder ? b : nothing
end

const _SLOW = Ref(IdDict{Any,Any}())                  # Pair(X, U) => Builder or NOTRAIT; copy-on-write
const _SLOW_WORLD = Ref{UInt}(0)                  # the world `_SLOW` was decided in: any definition makes it stale
"The implementation of a type with no method of its own: a generic implementation, a family, a dynamic one."
@machinery @noinline function _conformance_slow(@nospecialize(X), @nospecialize(u))
    U = typeof(u)
    key = Pair{Any,Any}(X, U)
    w = Base.tls_world_age()                            # decided in the caller's world, as dispatch is
    if CLOSED_WORLD[] || _SLOW_WORLD[] == w
        b = get(_SLOW[], key, nothing)
        b === nothing || return b === NOTRAIT ? NOTRAIT : (b::Builder)(u)
        CLOSED_WORLD[] && Base.inferencebarrier(_closed_miss)(X, u)
    end
    _FACTS_DEBUG[] && Core.println("TraitWorld: implementation slow path: ", X, " for ", U)
    b = _in_world(w, _builder_for, Any[X], U)
    b isa Builder && _in_world(w, _generic_concrete_check, X, U)
    @lock _LOCK begin
        d = _SLOW_WORLD[] == w ? copy(_SLOW[]) : IdDict{Any,Any}()
        d[key] = b
        _SLOW[] = d                                     # readers see the old table or the new one
        _SLOW_WORLD[] = w
    end
    return b === NOTRAIT ? NOTRAIT : (b::Builder)(u)
end

"""
A type conforming through a generic implementation, at its first use: the parts the concreteness
declarations name (traits reference §11.1), as at a declaration. A declared type and a family member
are checked by their own paths.
"""
@machinery function _generic_concrete_check(@nospecialize(X), @nospecialize(U))
    _impl(X, U) isa ImplRec && return nothing
    p = proj_lookup(X, U)
    p === nothing && return nothing
    errs, warns = _concrete_problems(X, U, p)
    isempty(errs) || throw(ImplementError("$U conforms to $X through a generic implementation, but a part is not concrete:\n  " * join(errs, "\n  ")))
    if !isempty(warns) && !(Pair{Any,Any}(X, U) in _FAMILY_WARNED)
        push!(_FAMILY_WARNED, Pair{Any,Any}(X, U))
        @warn "$U conforms to $X with abstract parts: code compiled for it dispatches at run time where it uses them:\n  " * join(warns, "\n  ")
    end
    return nothing
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
@machinery _needed_slow(@nospecialize(F), pos::Int, nargs::Int) = TraitList{Tuple{traits_at(F.instance, pos, nargs)...}}()

"""
    enter(EntryPos{F, pos, nargs}(), t, Val(known))

The trait object for argument `pos` of a call from ordinary code, or `NOTRAIT` if `t` has
none of the traits the position needs: `Compiled` (at its key) or `Dynamic` (at the erased key),
decided once here (traits reference §6; lowering §8.2). `known` is `Compiler.known_type(t)`,
evaluated in the entry's own body. Specialized: for a known type it folds to the views' construction.
"""
@inline function enter(p::EntryPos{F}, t, ::Val{kn}) where {F,kn}
    t isa TObj && return Base.inferencebarrier(_rule3_error)(typeof(p), t)
    # the caller's conversions always win
    t isa CompiledFor && return _enter_compiled(p, getfield(t, :x))
    t isa WithDynamic && return _enter_erased(p, getfield(t, :x))
    # a kept value keeps its attribute: a dynamic one is never opened at a bound, a compiled one is
    # opened by its object's type (the table serves it where the entry has one)
    t isa Dynamic && return _enter_erased(p, _dyn_held(t))
    t isa Compiled && return _enter_compiled(p, _dyn_held(t))
    t isa Kept && return getfield(t, :compiled) ? _enter_compiled(p, _dyn_held(t)) : _enter_erased(p, _dyn_held(t))
    _enters_dynamic(p, t, Val(kn)) && return _enter_erased(p, t)
    return _enter_compiled(p, t)
end
"The trait object at its key of a plain value: a container crossing where the position asks (§13.1); the whole object kept where the worker may keep it."
@inline function _enter_compiled(p::EntryPos{F}, t) where {F}
    t isa TObj && return t                                   # a dynamic value holding a trait object (`_dyn_held`)
    v, o = _enter_keyed(p, t)
    # a function that may keep its trait objects gets the whole user's object, also of an immutable
    # type (boxed); every other function holds its parts (`keeps` folds to a constant)
    keeps(KeepOf{F}()) && !ismutable(o) && v isa TObj && return _with_object(v, o)
    return v
end
"The trait object at the erased key of a plain value: its trait object at its key, erased, holding the user's object (or the crossed container's view)."
@inline function _enter_erased(p::EntryPos{F}, t) where {F}
    t isa TObj && return _erase(_narrow_to(p, t), t)
    v, o = _enter_keyed(p, t)
    v === NOTRAIT && return NOTRAIT
    return _erase(v, o)
end
"What a kept value holds: the user's object, or a trait object where it holds one."
@inline _dyn_held(d::HeldValue) = getfield(d, :t)
"A trait object a dynamic value holds, as it is (its traits are those of the `Dynamic`)."
@inline _narrow_to(p::EntryPos, t::TObj) = t
"""
The trait object at its key of `t`, and the object its views read: `t`, or where `t` is a container
that crosses at the position (traits §8.3), the view it crosses as.
"""
@inline function _enter_keyed(p::EntryPos{F}, t) where {F}
    # a container crosses with its items seen as `Dynamic{Y}` where the bounds ask for that and it
    # does not meet them as it is (traits reference §8.3); once decided for its type, it is not
    # assembled as it is first (a container whose family check failed would take the slow path)
    c = crossing(p)
    if c isa Crossing && _cross_known(c, t) == 0x02
        w = crossed(_citem(c), _cattr(c), t)
        w === nothing || return _assemble(needed(p), w), w
    end
    v = _assemble(needed(p), t)
    if c isa Crossing && _crosses(c, p, v, t)
        w = crossed(_citem(c), _cattr(c), t)
        w === nothing || return _assemble(needed(p), w), w
    end
    return v, t
end

"""
    Crossing{Y, R}

What the bounds at an entry position ask of a container's items: the trait `Y` of the dynamic
items they fix (`Iterable{Shape}`, `Keyed{String, Shape}`: `Shape`), and `R`, per bounded method at
the position, the tuple of the parameter tags (`PTag`) its bound requires. A value meeting one of
them as it is never crosses.
"""
struct Crossing{Y,R,A} end
_citem(::Crossing{Y}) where {Y} = Y
_creqs(::Crossing{Y,R}) where {Y,R} = R
"The attribute the bound gives the items: `:default`, `:compiled` or `:dynamic`."
_cattr(::Crossing{Y,R,A}) where {Y,R,A} = A
Base.Experimental.@max_methods 1 function crossing end
"""
    crossing(EntryPos{F, pos, nargs}())

The `Crossing` of a position, or `nothing` where no bound there fixes a parameter to a dynamic
value, or the bounds fix it to dynamic values of different traits. A method per crossing position
is defined with `needed` (`_fix_crossing!`), when the trait module is complete; until then, and
everywhere else, this fallback: no crossing.
"""
crossing
crossing(::EntryPos) = nothing
"""
    crossed(Y, x)

`x` seen with its items as `Dynamic{Y}`, the value a container crosses as (BaseTraits:
`DynamicItems`, `DynamicValues`), or `nothing` when `x` does not cross.
"""
crossed(::Type, ::Symbol, @nospecialize(x)) = nothing
"The container `t` as it crosses: the trait object of its view, or `nothing` if it has none."
@inline function _cross_into(c::Crossing, p::EntryPos{F}, t) where {F}
    w = crossed(_citem(c), _cattr(c), t)
    w === nothing && return nothing
    vw = _assemble(needed(p), w)
    keeps(KeepOf{F}()) && vw isa TObj && return _with_object(vw, w)
    return vw
end
"The decision kept for crossing `c` and `t`'s type: 0 not known, 1 as it is, 2 crosses."
@inline _cross_known(c::Crossing, t::T) where {T} = _cross_flag(typeof(c), T)[]
"""
Whether a value `t` crosses at a position of crossing `c`: it does not meet the bounds as it is
(its trait object `v`), and its view does. Decided once per crossing and type, and kept in a flag
(0 not known, 1 as it is, 2 crosses): a family member's trait object (every Base container) has a
type known only when it is built, so the test would otherwise run at each call.
"""
@inline function _crosses(c::Crossing, p::EntryPos, v, t::T) where {T}
    flag = _cross_flag(typeof(c), T)
    d = flag[]
    d == 0x00 && (d = _cross_decide(c, p, v, t, flag)::UInt8)   # machinery: a guard for verify_main
    return d == 0x02
end
@generated _cross_flag(::Type{C}, ::Type{T}) where {C,T} = :($(Ref{UInt8}(0x00)))
@machinery @noinline function _cross_decide(c::Crossing, p::EntryPos, v, t::T, flag::Base.RefValue{UInt8}) where {T}
    R = _creqs(c)
    d = 0x01
    if !_satisfies_rt(typeof(v)::Type, R)
        w = crossed(_citem(c), _cattr(c), t)
        w === nothing && return 0x01                      # not kept: `crossed` may say yes once more types conform
        _satisfies_rt(typeof(_assemble(needed(p), w))::Type, R) && (d = 0x02)
    end
    flag[] = d
    return d
end
"""
`_satisfies` for a type known only at run time, written with builtins only, so that it has no
run-time site (`verify_main`): a union's members are reached through its fields.
"""
function _satisfies_rt(TO::Type, R::Type)
    (TO isa DataType && TO <: TObj) || return false
    have = getfield(TO, :parameters)[1]
    for req in getfield(R::DataType, :parameters)
        ok = true
        for tag in getfield(req::DataType, :parameters)
            ok = ok && _union_has(have, tag)
        end
        ok && return true
    end
    return false
end
function _union_has(@nospecialize(u), @nospecialize(x))
    while u isa Union
        (getfield(u, :a) === x || (getfield(u, :a) isa Union && _union_has(getfield(u, :a), x))) && return true
        u = getfield(u, :b)
    end
    return u === x
end
"Whether trait object type `TO` meets one of the tag sets in `R` (a tuple of tuples of `PTag`s)."
@generated function _satisfies(::Type{TO}, ::Type{R}) where {TO,R}
    (TO isa DataType && TO <: TObj) || return false
    have = Base.uniontypes(TO.parameters[1])
    for req in (R::DataType).parameters
        all(t -> any(h -> h === t, have), (req::DataType).parameters) && return true
    end
    return false
end
"The item position inside a fixed parameter value (`Through{Shape, A}`, `Pair{String, Through{Shape, A}}`): `(Shape, A)`, or `nothing`."
function _dyn_inside(@nospecialize(v))
    v isa DataType || return nothing
    v.name === Base.typename(Through) && return (v.parameters[1], v.parameters[2])
    for q in v.parameters
        y = _dyn_inside(q)
        y === nothing || return y
    end
    return nothing
end
"The `Crossing` of position `pos` of `f`'s bounded methods with `nargs` arguments, or `nothing`."
function crossing_at(@nospecialize(f), pos::Int, nargs::Int)
    reqs = Any[]
    ys = Any[]
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
        q = Base.unwrap_unionall(p)
        (q isa DataType && q.name === Base.typename(TObj)) || continue
        T = q.parameters[1]
        lb = T isa TypeVar ? T.lb : T
        tags = Any[x for x in Base.uniontypes(lb) if _isptag(x)]
        push!(reqs, Tuple{tags...})
        for tg in tags
            y = _dyn_inside((tg::DataType).parameters[3])
            y === nothing || _hasid(ys, y) || push!(ys, y)
        end
    end
    length(unique(Any[y[1] for y in ys])) == 1 || return nothing
    return Crossing{ys[1][1],Tuple{reqs...},ys[1][2]}()
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
    length(Xs) == 1 && return :(conformance($(As{Xs[1]}()), t))     # one trait: its implementation gives the trait object
    calls = [:(conformance($(As{X}()), t)) for X in Xs]
    return :(_merge($(calls...)))
end
"The views of several implementations in one trait object, each trait once; `NOTRAIT` if there are none."
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
@noinline function enter_each(p::EntryPos, ts::Tuple, ::Val{kn}) where {kn}
    vs = map(t -> enter(p, t, Val(kn)), ts)
    any(v -> v === NOTRAIT, vs) && return NOTRAIT
    return vs
end

"""
    enter_kw(L, f, k, nt)

A bounded keyword: if `k` was supplied, its value is translated for the traits `L` (a
`TraitList`, from the bound) and replaced in the named tuple of supplied keywords; a value
that conforms to none of them is refused at the entry.
"""
@noinline function enter_kw(l::TraitList, f::F, k::Symbol, nt::NamedTuple, @nospecialize(attr), ::Val{kn}) where {F,kn}
    haskey(nt, k) || return nt
    t = getfield(nt, k)
    t isa TObj && return nt
    # as `enter`: the caller's conversion, a dynamic value carried, the attribute, the traits' default, `known`
    # a held value or a cast carries its attribute; a plain value as at a positional bound
    dyn = t isa WithDynamic || ((t isa Dynamic || t isa Compiled || t isa Kept) && is_dynamic(t)) ||
          (!(t isa CompiledFor || t isa Compiled || t isa Kept) && (attr === :dynamic || (attr !== :compiled &&
                                    ((_any_dynamic_default(l) && !_from_trait_world(t)) || (!kn && _traits_default(l) !== :compiled)))))
    t isa CompiledFor && (t = getfield(t, :x))
    t isa WithDynamic && (t = getfield(t, :x))
    (t isa Dynamic || t isa Compiled || t isa Kept) && (t = _dyn_held(t))
    v = t isa TObj ? t : _assemble(l, t)
    v === NOTRAIT && Base.inferencebarrier(_kw_refused)(f, k, t, l)
    if dyn
        v = _erase(v, t)
    elseif keeps(KeepOf{F}()) && !ismutable(t) && v isa TObj
        v = _with_object(v, t)
    end
    return merge(nt, NamedTuple{(k,)}((v,)))
end
@noinline _kw_refused(@nospecialize(f), k::Symbol, @nospecialize(t), @nospecialize(l)) =
    throw(TraitBoundError("keyword `$k` of `$f`: a value of type $(typeof(t)) conforms to none of " *
                          "$(join(string.(typeof(l).parameters[1].parameters), ", "))"))

"A `Callable` keyword: wrapped like a positional one if supplied."
@noinline function enter_kw_callable(::Type{A}, ::Type{S}, @nospecialize(attr), k::Symbol, nt::NamedTuple, ::Val{kn}) where {A,S,kn}
    haskey(nt, k) || return nt
    return merge(nt, NamedTuple{(k,)}((enter_callable(A, S, attr, getfield(nt, k), Val(kn)),)))
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
@machinery function _builder_for(needed::Vector{Any}, @nospecialize(U))
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
        # held whole when the user's type is its own receiver (not a key without one,
        # whose parts are its declared fields only)
        push!(specs, VSpec{_instance(Y, K),typeof(w),K,length(fs),_partstype(K),p.field == 0 && _impl(K) !== Nothing}(w, r, fs))
    end
    return Builder(Tuple(specs))
end

"The slot of field `i` of type `U`: its byte offset and index."
_slot(@nospecialize(U), i::Int) = Slot(Int(fieldoffset(U, i)), i)
"The stored field of `U` that declared field `f` maps to: written in the implementation, else the same name."
_mapped(p::ProjRec, f::Symbol) = (m = p.fmap; m === nothing ? f : get(m, f, f))
"""
The key of trait `Y` for user type `U` conforming through `p` with witness `w`, and the
slots of `Y`'s declared fields: the receiver type alone for a trait without fields;
else a `Key` with the declared fields' types in `U`. The receiver type is `Nothing`
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
Whether an implementation of trait `Y` with witness `w` has no receiver type: every
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

@machinery @noinline function _fallback_plain(@nospecialize(nt), @nospecialize(f), args::Tuple)
    m = _plain_method(f, Tuple{Core.Typeof(f),map(typeof, args)...})
    m === nothing && throw(MethodError(f, args))
    body = Base.unwrap_unionall(m.sig)
    sig = Base.rewrap_unionall(Tuple{body.parameters[2:end]...}, m.sig)
    nt === nothing && return invoke(f, sig, args...)
    return invoke(f, sig, args...; nt...)
end

"""
An entry: a method of a trait module compiled in its caller's mode (the boundary meta,
`Method.facts == 1`); the only other such methods are the implementations, of `conformance`.
"""
_is_entry(m::Method) = m.facts == 1 && m.name !== :conformance && isdefined(m.module, :__tw_entries__)

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
_from_trait_world(@nospecialize(f)) = _type_from_trait_world(typeof(f))
"Whether type `T` is of the trait world, all the way down (`_tw_type`), kept per type."
function _type_from_trait_world(@nospecialize(T))
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
Machinery: it runs once per function type at a trait module's first call, and its plain code had
edges at abstract signatures (in `owner`, `is_trait_world`) that unrelated loads invalidate.
"""
@machinery function _tw_type(@nospecialize(T), seen)
    T isa DataType || return false
    T <: HeldValue && return true                       # a held value: its type decides it
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
    enter_callable(A, S, attr, f, Val(known))

A function handed down for a `Callable{A, S}` argument, as a `CObj`: `Compiled` (the function itself,
the worker compiled per function type) or `Dynamic` (erased to a pointer, the worker compiled once
per signature). The caller's conversion wins (`compiled_for(f)`, `with_dynamic(f)`); a
`Dynamic{Callable{A, S}}` is carried; else the bound's attribute (`attr`); else `Callable`'s
default, `Dynamic`, for a function whose type is not of the trait world; else whether the caller knew
the function's type (`known`, evaluated in the entry's body). In a closed build nothing is erased.
"""
@noinline function enter_callable(::Type{A}, ::Type{S}, @nospecialize(attr), @nospecialize(f), ::Val{kn}) where {A,S,kn}
    f isa CObj{A,S} && return f
    # a function held or cast keeps its attribute, at this signature too (a `Dynamic` one through its own pointer)
    if _held_callable_dynamic(f) && !(f isa WithDynamic)
        return _erased_at(A, S, _callable_fn(f))
    elseif f isa CObj
        return getfield(f, :f) isa Erased ? _erased_at(A, S, f) : CObj{A,S}(_callable_fn(f))
    end
    if _held_callable_compiled(f)
        f = f isa CompiledFor ? getfield(f, :x) : _callable_fn(f); attr = :compiled
    elseif f isa WithDynamic
        f = getfield(f, :x); attr = :dynamic
    elseif attr === nothing
        attr = _from_trait_world(f) ? (kn ? :compiled : :dynamic) : :dynamic
    end
    CLOSED_WORLD[] && return CObj{A,S}(f)          # every function is known: no erasure
    T = typeof(f)
    if Base.issingletontype(T)
        # functions that capture nothing (Base's `abs2`, a closure without state): one wrapper per type
        key = (A, S, attr, T)
        c = get(_CALLABLE[], key, nothing)               # copy-on-write: read without the lock
        c === nothing || return c
        c = _wrap_callable(A, S, attr, f)
        @lock _LOCK begin
            d = copy(_CALLABLE[]); d[key] = c; _CALLABLE[] = d
        end
        return c
    end
    return _wrap_callable(A, S, attr, f)
end
const _CALLABLE = Ref(Dict{Any,Any}())           # copy-on-write
@noinline _callable_mismatch(@nospecialize(C), @nospecialize(A), @nospecialize(S)) =
    throw(TraitBoundError("a Dynamic{$C} was passed where Callable{$A, $S} is expected"))
_wrap_callable(::Type{A}, ::Type{S}, attr::Symbol, @nospecialize(f)) where {A,S} =
    attr === :compiled ? CObj{A,S}(f) : CObj{A,S}(Erased{A,S}(f))

Base.Experimental.@max_methods 1 function bounded_constructor end
"`bounded_constructor(S)`: whether struct `S` has parameters bounded by a trait, so its constructor without parameters is their bound (methods added by `@trait_module`)."
bounded_constructor(@nospecialize(S)) = false

"""
    _kept_at(B, x, Val(known))

The stored form of `x` at a struct parameter bounded by `B` (traits reference §7.4): its attribute
as a bound gives it (the caller's cast, a value's carried attribute, else the first-seen rule, with
`known` evaluated in the constructor's body), then for a `Compiled` value the user's object itself
(the function, for `Callable`), whose type becomes the parameter, and for a `Dynamic` one `Dynamic{B}`.
A `Compiled{X}` or a `Kept{X}` with `Compiled` is opened here, by its object's type.
"""
function _kept_at(::Type{C}, @nospecialize(x), ::Val{kn}) where {C<:Callable,kn}
    u = Base.unwrap_unionall(C)
    c = enter_callable(u.parameters[1], u.parameters[2], nothing, x, Val(kn))
    f = getfield(c, :f)
    return f isa Erased ? Dynamic{C}(Val(:checked), c) : f
end
function _kept_at(::Type{X}, @nospecialize(x), ::Val{kn}) where {X,kn}
    if x isa TObj
        _is_erased(typeof(getfield(x, :views))) && return Dynamic{X}(x)
        return getfield(Compiled{X}(x), :t)
    elseif x isa Dynamic || x isa WithDynamic
        return Dynamic{X}(x isa WithDynamic ? getfield(x, :x) : x)
    elseif x isa Compiled || x isa CompiledFor
        return getfield(Compiled{X}(x isa CompiledFor ? getfield(x, :x) : x), :t)
    elseif x isa Kept
        return getfield(x, :compiled) ? getfield(Compiled{X}(x), :t) : Dynamic{X}(x)
    end
    d = default_attribute(_family(X))
    dyn = (d === :dynamic && !_from_trait_world(x)) || (!kn && d !== :compiled)
    return dyn ? Dynamic{X}(x) : getfield(Compiled{X}(x), :t)
end

"A function argument with several `Callable` bounds: one `CObj` per signature."
function enter_callables(sigs::Tuple, @nospecialize(f), ::Val{kn}) where {kn}
    f isa CMulti && return f
    return CMulti(map(s -> enter_callable(s[1], s[2], s[3], f, Val(kn)), sigs))
end

# --- `Callable`'s held values (traits reference §5.8; lowering §12) -------------------------------
#
# A `Dynamic{Callable{A, S}}` holds the function erased to a pointer (`CObj{A, S, Erased{A, S}}`); a
# `Compiled{Callable{A, S}}` holds the function itself; a `Kept{Callable{A, S}}` holds either, with
# its attribute. Constructors make or keep, never cast. A function held at one signature is the same
# function at another: seen there with its attribute, a `Dynamic` one through a new pointer.

"The function a held `Callable` value or a function argument stands for."
@inline _callable_fn(c::CObj) = (f = getfield(c, :f); f isa Erased ? getfield(f, :obj) : f)
@inline _callable_fn(h::HeldValue{C}) where {C<:Callable} = (t = getfield(h, :t); t isa CObj ? _callable_fn(t) : t)
"The function argument `f`, a plain function or a function argument, as a `Dynamic` at `Callable{A, S}`."
@inline _erased_at(::Type{A}, ::Type{S}, @nospecialize(f)) where {A,S} =
    f isa CObj{A,S,Erased{A,S}} ? f : CObj{A,S}(Erased{A,S}(f isa CObj ? _callable_fn(f) : f))
"Whether a value is a `Callable` value held with the attribute `Compiled` (the caller's `compiled_for`, or kept so)."
@inline _held_callable_compiled(@nospecialize(f)) = f isa CompiledFor || (f isa Compiled && f isa Compiled{<:Callable}) ||
    (f isa Kept && f isa Kept{<:Callable} && getfield(f, :compiled))
@inline _held_callable_dynamic(@nospecialize(f)) = f isa WithDynamic || (f isa Dynamic && f isa Dynamic{<:Callable}) ||
    (f isa Kept && f isa Kept{<:Callable} && !getfield(f, :compiled))

"""
    Dynamic{Callable{A, S}}(f)

`f` as a dynamic value of `Callable{A, S}`: a pointer to its code compiled for `A`, its result asserted
to `S`, of a type that does not depend on the function. Made from a plain function, or kept from a
`Dynamic` function (a `with_dynamic(f)`, a `Dynamic` or `Kept` value held at any signature); a
`Compiled` one is refused, since only `with_dynamic` changes an attribute. Calling it is the checked call.
"""
(::Type{Dynamic{C}})(@nospecialize(f)) where {C<:Callable} = _callable_dynamic(C, f)
function _callable_dynamic(::Type{C}, @nospecialize(f)) where {C<:Callable}
    u = Base.unwrap_unionall(C)
    A, S = u.parameters
    f isa Dynamic{C} && return f
    _held_callable_compiled(f) && Base.inferencebarrier(_cast_refuse)(C, :Dynamic, :Compiled)
    f isa WithDynamic && (f = getfield(f, :x))
    f isa HeldValue && (f = _callable_fn(f))
    return Dynamic{C}(Val(:checked), _erased_at(A, S, f))
end
(::Type{Dynamic{C}})(f::Dynamic{C}) where {C<:Callable} = f
#     Compiled{Callable{A, S}}(f)
# `f` as a compiled value of `Callable{A, S}`: the function itself, where the code that holds it does
# not know its type. A call selects the code compiled for the function by its type (one dynamic call);
# passed to a bound, the worker compiled for the function runs. Made from a plain function, or kept
# from a `Compiled` one; a `Dynamic` one is refused, since only `compiled_for` changes an attribute.
(::Type{Compiled{C}})(@nospecialize(f)) where {C<:Callable} = _callable_compiled(C, f)
function _callable_compiled(::Type{C}, @nospecialize(f)) where {C<:Callable}
    f isa Compiled{C} && return f
    _held_callable_dynamic(f) && Base.inferencebarrier(_cast_refuse)(C, :Compiled, :Dynamic)
    f isa CompiledFor && (f = getfield(f, :x))
    f isa HeldValue && (f = _callable_fn(f))
    f isa CObj && (f = _callable_fn(f))
    return Compiled{C}(Val(:checked), f)
end
(::Type{Compiled{C}})(f::Compiled{C}) where {C<:Callable} = f
#     Kept{Callable{A, S}}(f)
# `f` kept with its attribute: a function argument by how it is held (the function itself `Compiled`,
# an erased one `Dynamic`), a held value or a caller's cast as it is, a plain function by `Callable`'s
# default, `Dynamic`.
(::Type{Kept{C}})(@nospecialize(f)) where {C<:Callable} = _callable_kept(C, f)
function _callable_kept(::Type{C}, @nospecialize(f)) where {C<:Callable}
    u = Base.unwrap_unionall(C)
    A, S = u.parameters
    f isa Kept{C} && return f
    if f isa CObj
        return getfield(f, :f) isa Erased ? Kept{C}(Val(:checked), _erased_at(A, S, f), false) : Kept{C}(Val(:checked), _callable_fn(f), true)
    end
    _held_callable_compiled(f) && return Kept{C}(Val(:checked), getfield(Compiled{C}(f), :t), true)
    return Kept{C}(Val(:checked), getfield(Dynamic{C}(f), :t), false)
end
(::Type{Kept{C}})(f::Kept{C}) where {C<:Callable} = f
# between the forms at one signature, as for any trait (core.jl), stated for `Callable` too: its
# constructors above take any argument, so these resolve what would otherwise be ambiguous
(::Type{Dynamic{C}})(c::Compiled{C}) where {C<:Callable} = Base.inferencebarrier(_cast_refuse)(C, :Dynamic, :Compiled)
(::Type{Compiled{C}})(d::Dynamic{C}) where {C<:Callable} = Base.inferencebarrier(_cast_refuse)(C, :Compiled, :Dynamic)
(::Type{Dynamic{C}})(k::Kept{C}) where {C<:Callable} = getfield(k, :compiled) ?
    Base.inferencebarrier(_cast_refuse)(C, :Dynamic, :Compiled) : Dynamic{C}(Val(:checked), getfield(k, :t))
(::Type{Compiled{C}})(k::Kept{C}) where {C<:Callable} = getfield(k, :compiled) ?
    Compiled{C}(Val(:checked), getfield(k, :t)) : Base.inferencebarrier(_cast_refuse)(C, :Compiled, :Dynamic)
(::Type{Kept{C}})(d::Dynamic{C}) where {C<:Callable} = Kept{C}(Val(:checked), getfield(d, :t), false)
(::Type{Kept{C}})(c::Compiled{C}) where {C<:Callable} = Kept{C}(Val(:checked), getfield(c, :t), true)
Base.convert(::Type{Kept{C}}, c::CObj) where {C<:Callable} = Kept{C}(c)
Base.convert(::Type{Kept{C}}, c::Union{Dynamic{C},Compiled{C}}) where {C<:Callable} = Kept{C}(c)
@inline function (d::Dynamic{Callable{A,S}})(args...) where {A,S}
    return (getfield(d, :t)::CObj{A,S,Erased{A,S}})(args...)
end
# the function's type is not known here: one dynamic call, its result asserted to the declared type
@inline (c::Compiled{Callable{A,S}})(args...) where {A,S} = CObj{A,S}(getfield(c, :t))(args...)::S
@inline function (k::Kept{Callable{A,S}})(args...) where {A,S}
    getfield(k, :compiled) && return CObj{A,S}(getfield(k, :t))(args...)::S
    return (getfield(k, :t)::CObj{A,S,Erased{A,S}})(args...)
end
# the casts, on `Callable`'s held values: the function moves between its forms
compiled_for(d::Dynamic{C}) where {C<:Callable} = Compiled{C}(Val(:checked), _callable_fn(d))
compiled_for(k::Kept{C}) where {C<:Callable} = Kept{C}(Val(:checked), _callable_fn(k), true)
with_dynamic(c::Compiled{C}) where {C<:Callable} =
    (u = Base.unwrap_unionall(C); Dynamic{C}(Val(:checked), _erased_at(u.parameters[1], u.parameters[2], _callable_fn(c))))
with_dynamic(k::Kept{C}) where {C<:Callable} = getfield(k, :compiled) ?
    (u = Base.unwrap_unionall(C); Kept{C}(Val(:checked), _erased_at(u.parameters[1], u.parameters[2], _callable_fn(k)), false)) : k
Base.show(io::IO, d::Dynamic{C}) where {C<:Callable} = print(io, "Dynamic{", C, "}")
Base.show(io::IO, d::Compiled{C}) where {C<:Callable} = print(io, "Compiled{", C, "} at ", typeof(getfield(d, :t)))
Base.show(io::IO, d::Kept{C}) where {C<:Callable} =
    getfield(d, :compiled) ? print(io, "Kept{", C, "}: Compiled at ", typeof(getfield(d, :t))) : print(io, "Kept{", C, "}: Dynamic")
_dyn_identity(h::HeldValue{C}) where {C<:Callable} = _callable_fn(h)

"The trait list of `X`'s family, computed from `X` alone when the caller is specialized (a constant, so code compiled by facts needs no run-time site for it)."
@generated _family_list(::Type{X}) where {X} = :($(TraitList{Tuple{_family(X)}}()))

# `Dynamic{X}(x)` for a value that is no trait object is an inner constructor of `Dynamic` (core.jl).

# --- results like the input (note "Results like the input") -----------------------

"Functions with a method declared `::Like{t}`: their workers return a pending result, which their entry makes into the caller's type."
const _LIKE_FUNCS = Base.IdSet{Any}()
_like!(@nospecialize(f)) = (push!(_LIKE_FUNCS, typeof(f)); nothing)

"No new receiver: a result like the input with only fields replaced."
struct KeepSelf end

"""
A result like the input (note "Results like the input"): the input's trait object, a new
receiver or `KeepSelf()`, and new values of declared fields. Nothing operates on
it; only the entry inverts it, rebuilding the user's type.
"""
struct LikeResult{T<:TObj,S,F<:NamedTuple}
    t::T
    x::S
    f::F
end

"""
    like(t, x)

A result like `t` holding the new receiver `x`: what a function declared
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
@machinery function _like_out(res::LikeResult, us::Tuple, vs::Tuple)
    for i in eachindex(vs)
        vs[i] === res.t || continue
        u = us[i]
        v = getfield(res.t, :views)[1]
        X = _family(typeof(v).parameters[1])
        if typeof(v).parameters[2] === ErasedWit
            # a `Dynamic` trait object (lowering §11): the inverse needs the view at the held object's own
            # key; a new receiver made by a constructor operation came back as a `Dynamic` of it
            o = getfield(v, :o)
            kt = o isa TObj ? o : _assemble(TraitList{Tuple{X}}(), o)
            kt isa TObj && !(o isa TObj) && !ismutable(o) && (kt = _with_object(kt, o))
            v = viewof(kt, X)
            x = res.x isa HeldValue ? _dyn_object(res.x) : res.x
            res = LikeResult(kt, x, res.f)
        end
        if u isa HeldValue
            # a held value in, a held value of the same trait and attribute out (kept, not cast)
            o = _viewobject(v)
            o === nothing && getfield(_viewslot(v), :off) >= 0 && throw(TraitBoundError(
                "a dynamic value of an immutable type keeps the parts $X can see, not the whole object, " *
                "so a result like it cannot be rebuilt; pass the value itself"))
            nu = _invert(X, v, o === nothing ? getfield(getfield(v, :parts), 1) : o, res)
            b = _builder_for(Any[X], typeof(nu))
            b === NOTRAIT && throw(TraitBoundError("$(typeof(nu)) does not conform to $X"))
            return _keep_as(u, b(nu))
        end
        return _invert(X, v, u, res)
    end
    _like_none()
end

"""
A result like the input at the entry (lowering §11). Where the caller knows the user's type and that
type's own declaration fixed a builder (a constant), the inverse is compiled for the type: the slots
it replaces are the builder's, so the constructor's result has the type it builds (a sibling:
`LSeries{Float32}` from `LSeries{Float64}`). Otherwise the inverse runs when the call runs (`_like_out`).
"""
@inline function _like_return(res::LikeResult, us::Tuple, vs::Tuple)
    i = _like_pos(typeof(res.t), typeof(vs))
    if i > 0
        # the only position of the result's trait object type: if it is not that object, none is
        vs[i] === res.t || Base.inferencebarrier(_like_none)()
        r = _like_typed(res, us[i])
        r isa _NoPlan || return r
    end
    return Base.inferencebarrier(_like_out)(res, us, vs)
end
@noinline _like_none() = throw(TraitBoundError("a result like the input names no trait object the entry passed"))
"The one entry position whose trait object has type `T`, or 0 (none, or several: decided when the call runs)."
@generated function _like_pos(::Type{T}, ::Type{V}) where {T,V}
    is = [i for (i, P) in enumerate(V.parameters) if P === T]
    return length(is) == 1 ? is[1] : 0
end
"No compiled inverse: the user's type is not known here, or has no declaration of its own."
struct _NoPlan end
@inline function _like_typed(res::LikeResult, u::U) where {U}
    (u isa HeldValue || u isa CompiledFor || u isa WithDynamic || !isconcretetype(U)) && return _NoPlan()
    w = getfield(res.t, :views)[1]
    typeof(w).parameters[2] === ErasedWit && return _NoPlan()
    X = _family(typeof(w).parameters[1])
    b = _declared_builder(As{X}(), U)
    b isa Builder || return _NoPlan()
    s = _spec_of(X, getfield(b, :specs)...)
    s === nothing && return _NoPlan()
    r = getfield(s, :r)
    x = res.x
    if getfield(r, :off) < 0
        # the type implements the operations itself: the new value replaces it, of the same type family
        base = x isa KeepSelf ? u : _same_family(X, u, x)
        return _rebuild_typed(base, _field_repls(X, getfield(s, :fs), res.f))
    end
    reps = x isa KeepSelf ? _field_repls(X, getfield(s, :fs), res.f) :
                            ((getfield(r, :idx), x), _field_repls(X, getfield(s, :fs), res.f)...)
    return _rebuild_typed(u, reps)
end
"The spec of trait family `X` among a builder's specs (one per trait of the closure), or `nothing`."
@inline _spec_of(@nospecialize(X)) = nothing
@inline _spec_of(X, s::VSpec{Xi}, rest...) where {Xi} = _family(Xi) === X ? s : _spec_of(X, rest...)
@inline function _same_family(@nospecialize(X), u::U, x) where {U}
    typeof(x) <: Base.typename(U).wrapper ||
        throw(TraitBoundError("$U implements $X itself, but the result is a $(typeof(x)): " *
                              "a result like the input must be a $(Base.typename(U).wrapper)"))
    return x
end
"The replaced declared fields as (stored field index, value) pairs."
@inline _field_repls(X, fs::Tuple, f::NamedTuple{names}) where {names} =
    ntuple(k -> (getfield(fs[_fieldpos(X, Val(names[k]))], :idx), getfield(f, k)), Val(length(names)))
"A copy of `u` with stored fields replaced, by the type's constructor; the indices are constants where this is compiled."
Base.@constprop :aggressive @inline function _rebuild_typed(u::U, reps::Tuple) where {U}
    isempty(reps) && return u
    fs = ntuple(j -> _pick(j, u, reps...), Val(fieldcount(U)))
    try
        return Base.typename(U).wrapper(fs...)
    catch e
        e isa MethodError || rethrow()
        throw(TraitBoundError("$U cannot be rebuilt from its fields by its constructor, so a result like it cannot be built"))
    end
end
Base.@constprop :aggressive @inline _pick(j::Int, u) = getfield(u, j)
Base.@constprop :aggressive @inline _pick(j::Int, u, r::Tuple, rest...) = r[1] == j ? r[2] : _pick(j, u, rest...)

"""
The implementation's inverse: a value of the user's type `typeof(u)` with the new parts of `res`.
A type that implements the operations itself is replaced by the new value (of the same type);
otherwise the user's object is rebuilt by its constructor with the forwarding field and the
declared fields replaced, so its parameters follow the new fields.
"""
function _invert(@nospecialize(X), v::AbstractView, u, res::LikeResult)
    x = res.x
    r = _viewslot(v)
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
function _dyn_like(d::HeldValue{X}, x) where {X}
    t = opened(d)
    v = getfield(t, :views)[1]
    isempty(getfield(v, :fs)) || throw(TraitBoundError("$X declares fields, so a new value of its receiver type alone does not conform"))
    n = TObj(map(w -> _selfview(typeof(w).parameters[1], getfield(w, :w), x), getfield(t, :views)))
    return _like_held(d, n)
end
"A held value of the new receiver value `n`, with `d`'s form and attribute."
_like_held(::Dynamic{X}, n::TObj) where {X} = Dynamic{X}(Val(:hold), n)
_like_held(::Compiled{X}, n::TObj) where {X} = Compiled{X}(Val(:hold), n)
_like_held(k::Kept{X}, n::TObj) where {X} = (Dynamic{X}(Val(:hold), n); Kept{X}(Val(:checked), n, getfield(k, :compiled)))
"The user's object trait object `t` reads, kept with the form and attribute of held value `u`."
_keep_as(::Dynamic{X}, t::TObj) where {X} = Dynamic{X}(Val(:keep), t)
_keep_as(::Compiled{X}, t::TObj) where {X} = Compiled{X}(Val(:checked), getfield(Dynamic{X}(Val(:keep), t), :t))
_keep_as(k::Kept{X}, t::TObj) where {X} = Kept{X}(Val(:checked), getfield(Dynamic{X}(Val(:keep), t), :t), getfield(k, :compiled))

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
