# ---------------------------------------------------------------------------
# Untyped calls: the table of declared implementations (plan step 3 (c), with step 4).
#
# A caller that does not know an argument's type reaches the entry compiled at `Any`. There the
# entry does not compile anything per user type: each entry position keeps a table from the user
# type to its implementation's builder (data: the witnesses and the slots its views read), and
# one dynamic call reaches a method of the entry specialized on the builders' types, which is
# compiled once per key. The views are built from the builder's data, reading the user's object
# at the slots' offsets. This is how Swift opens a value of a protocol type: per-type metadata is
# data, the code is shared.
#
# Under the facts rule every call with an argument of abstract type is a run-time site. The path
# below therefore never passes the user's value to a function as `Any`: the entry reads its type
# (`typeof`, a builtin), and the specialized method holds the value in an `XAny`, a concrete
# type, so every call in it is at a fact signature.
# ---------------------------------------------------------------------------

"Whether inference knows the concrete type of `x` here (the compiler's `known_type`): the entry's switch between the folded path and the table."
const _known_type = isdefined(CC, :known_type) ? CC.known_type : (@nospecialize(x) -> false)

"A value of a type not known where it is used, held in a concrete type: calls on the holder are facts."
struct XAny
    x::Any
end

"One user type's implementation at an entry position: its builder (or `NOTRAIT`), valid in a range of worlds."
struct UEntry
    T::DataType
    b::Any
    lo::UInt
    hi::UInt
end
"An entry position's table, appended copy-on-write; the entries of another session are ignored."
mutable struct UTable
    @atomic entries::Vector{UEntry}
    @atomic session::UInt
end
UTable() = UTable(UEntry[], UInt(0))
"This session's identity: tables saved in package images hold the entries of the session that built them."
const _SESSION = Ref{UInt}(0)

"The table of entry position `P`, embedded in the code that reads it."
@generated _utable(::P) where {P} = UTable()

"The builder for the held value's type at a table in world `w`, or `nothing` when the table does not know it."
@inline function _ulookup(tbl::UTable, xa::XAny, w::UInt)
    T = typeof(getfield(xa, :x))
    (@atomic :acquire tbl.session) === _SESSION[] || return nothing
    es = @atomic :acquire tbl.entries
    for i in 1:length(es)
        e = @inbounds es[i]
        (e.T === T && e.lo <= w && w <= e.hi) && return e.b
    end
    return nothing
end

"""
The builder of user type `T` at entry position `p` in world `w` (or `NOTRAIT`, or `_UNTABLED` for
an implementation the table does not serve), added to the table.
It is valid in the worlds where each needed trait's implementation for `T` is the same method: a
declared implementation (a `conformance` method of `T`'s own) for the range of its dispatch; an
implementation found by the slow path (generic, family) for this world only.
"""
@machinery @noinline function _umiss(tbl::UTable, @nospecialize(p::EntryPos), T::DataType, w::UInt)
    L = _in_world(w, needed, p)
    Xs = Any[(L isa TraitList ? typeof(L) : L).parameters[1].parameters...]
    # one trait: the builder its declaration fixed (no reflection); several: built here
    b = length(Xs) == 1 ? _in_world(w, _declared_builder, As{Xs[1]}(), T) : nothing
    b isa Builder || (b = _in_world(w, _builder_for, Xs, T))
    lo, hi = UInt(1), Base.get_world_counter()
    tabled = true
    for X in Xs
        mn, mx = Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt))
        m = ccall(:jl_gf_invoke_lookup_worlds, Any, (Any, Any, UInt, Ptr{Csize_t}, Ptr{Csize_t}),
                  Tuple{typeof(conformance),As{X},T}, nothing, w, mn, mx)
        declared = m isa Core.MethodMatch && m.method.sig isa DataType && m.method.sig.parameters[3] === T   # a declaration for `T` itself
        if declared
            lo, hi = max(lo, mn[]), min(hi, mx[])
        else
            # a generic implementation or a family member: found and fixed by the entry's own path
            # (`_conformance_slow`, `_conf_family_slow`, which keep what they find)
            tabled = false
            lo, hi = max(lo, w), min(hi, w)
        end
    end
    # a position where containers may cross (`crossing`) takes the entry's own path, which crosses them
    _in_world(w, crossing, p) === nothing || (tabled = false)
    tabled || b === NOTRAIT || (b = _UNTABLED)
    (lo <= w <= hi) || (lo = hi = w)
    @lock _LOCK begin
        s = _SESSION[]
        old = (@atomic tbl.session) === s ? (@atomic tbl.entries) : UEntry[]
        new = UEntry[]
        for e in old                                    # a loop, not a comprehension: no closure to compile
            (e.T === T && e.lo <= hi && lo <= e.hi) || push!(new, e)
        end
        push!(new, UEntry(T, b, lo, hi))
        @atomic :release tbl.entries = new
        @atomic :release tbl.session = s
    end
    return b
end

Base.Experimental.@max_methods 1 function _declared_builder end
"`_declared_builder(As{X}(), T)`: the builder a declaration of `X` for `T` fixed (a method per declaration), or `nothing`."
_declared_builder(::As, @nospecialize(T)) = nothing

"In the table for a type whose implementation the table does not serve: the entry takes its own path."
const _UNTABLED = :untabled

"""
The builder of the held value's type at `p` in world `w`: from the table, or found and added. The
value comes in its holder: a type passed as a value is a kind, and a call at a kind is a run-time site.
"""
@inline function _ubuilder(p::EntryPos, xa::XAny, w::UInt)
    tbl = _utable(p)
    b = _ulookup(tbl, xa, w)
    b === nothing && return Base.inferencebarrier(_umiss)(tbl, p, typeof(getfield(xa, :x))::DataType, w)
    return b
end

# --- views built from a builder's data ------------------------------------------------------

"The trait object of the held value for the builder `b`: its views read the object at the slots."
@inline _build_any(b::Builder, xa::XAny) = TObj(_build_any_specs(xa, getfield(b, :specs)...))
@inline _build_any_specs(xa::XAny) = ()
@inline _build_any_specs(xa::XAny, s::VSpec, rest...) = (_buildview_any(xa, s), _build_any_specs(xa, rest...)...)

"""
One view from its spec. A user type that is its key's receiver type is known from the key: the
view is built as a typed entry builds it. Otherwise the object is read through its slots.
"""
@generated function _buildview_any(xa::XAny, s::VSpec{X,W,K,N,P,S}) where {X,W,K,N,P,S}
    if S
        R = _impl(K)
        return :(_buildview(getfield(xa, :x)::$R, s, Val(!ismutabletype($R))))
    end
    ts = P.parameters
    rd(T, slot) = Base.allocatedinline(T) && !(T isa DataType && isbitstype(T)) ?
        :(getfield(t, getfield($slot, :idx))::$T) :                       # an inline union: read by index
        :(Core.Intrinsics.getfield_at_offset(t, $T, getfield($slot, :off))::$T)
    first = ts[1] === Nothing ? :nothing : :(getfield(r, :off) < 0 ? t::$(ts[1]) : $(rd(ts[1], :r)))
    rest = [rd(ts[i + 1], :(fs[$i])) for i in 1:N]
    return quote
        t = getfield(xa, :x)
        r = getfield(s, :r)
        fs = getfield(s, :fs)
        mut = (getfield(getfield(typeof(t)::DataType, :name), :flags) & 0x2) == 0x2
        $(Expr(:new, View{X,W,K,N,P}, :(getfield(s, :w)), :(mut ? t : nothing), :r, :fs, Expr(:tuple, first, rest...)))
    end
end

"The trait object `v` of the held immutable value, its views reading the whole object (as `_with_object`)."
@inline function _with_object_any(v::TObj, xa::XAny)
    t = getfield(xa, :x)
    (getfield(getfield(typeof(t)::DataType, :name), :flags) & 0x2) == 0x2 && return v
    return TObj(map(x -> _view_with_any(x, xa), getfield(v, :views)))
end
@generated _view_with_any(v::View{X,W,K,N,P}, xa::XAny) where {X,W,K,N,P} =
    Expr(:new, View{X,W,K,N,P}, :(getfield(v, :w)), :(getfield(xa, :x)), :(getfield(v, :r)), :(getfield(v, :fs)), :(getfield(v, :parts)))
@inline _view_with_any(v, xa::XAny) = v

# --- the entry's method through a pointer (one trait position): no second dispatch -------------
# The step-1 pointer: a `cfunction` of the calling convention `:caller_world`, which runs in the
# caller's world through a world-checked cache. One per entry pattern and builder type: the
# `_UCall{G, B}` holds the builder; the wrapper `_UWrap` calls the pattern's method `G` with it, statically.

"An entry pattern's method `G` and the builder it is called with (by `_UWrap`, behind the pointer)."
struct _UCall{G,B}
    b::Any          # held by reference: an isbits callable behind a `Ref` argument is copied into a box per call
end
# The pointer's wrapper: fixed arities (a vararg method would build its argument tuple); the
# arguments come boxed and are not specialized on, so `Any` is a compileable signature and the
# pointer's thunk calls code compiled once (else it falls back to a dynamic dispatch, compiling the
# wrapper per type behind it). Every argument goes on in a concrete holder, and the pattern's method
# is called directly: a call with an `Any` argument would be a run-time site where the wrapper is
# compiled by facts.
struct _UWrap end
for n in 0:5
    as = [Symbol(:a, k) for k in 1:n]
    hs = [Expr(:new, :XAny, a) for a in as]
    @eval (::_UWrap)(o::_UCall{G,B}, $([:(@nospecialize($a)) for a in as]...)) where {G,B} = G.instance(getfield(o, :b)::B, $(hs...))
end
"A pointer to `o(args...)` for the callable type `F` and `N` arguments, all passed boxed, in the caller's world."
@generated function _ufptr(::Type{F}, ::Val{N}) where {F,N}
    return Expr(:cfunction, Ptr{Cvoid}, QuoteNode(_UWrap()), Any,
                :(Core.svec($(Ref{F}), $(fill(Any, N)...))), QuoteNode(:caller_world))
end

"One user type's pointer for an entry pattern: the pointer, the callable it is called with, a range of worlds."
struct PEntry
    T::DataType
    fp::Ptr{Cvoid}
    fo::Any
    lo::UInt
    hi::UInt
end
mutable struct PTable
    @atomic entries::Vector{PEntry}
    @atomic session::UInt
end
"The pointer table of entry pattern `G`, embedded in the code that reads it."
@generated _ptable(::G) where {G} = PTable(PEntry[], UInt(0))

"The pointer entry for the held value's type, or `nothing`."
@inline function _plookup(t::PTable, xa::XAny, w::UInt)
    T = typeof(getfield(xa, :x))
    (@atomic :acquire t.session) === _SESSION[] || return nothing
    es = @atomic :acquire t.entries
    for i in 1:length(es)
        e = @inbounds es[i]
        (e.T === T && e.lo <= w && w <= e.hi) && return e
    end
    return nothing
end

"""
The pointer entry of entry pattern `g` (a method of `N` arguments after the builder) for the
held value's type: from its position's builder, made once, valid for the builder's worlds. Its
pointer is `C_NULL` when the table does not serve the type (no builder).
"""
@machinery @noinline function _pmiss(t::PTable, @nospecialize(p::EntryPos), @nospecialize(g), xa::XAny, w::UInt, N::Int)
    T = typeof(getfield(xa, :x))::DataType
    tbl = _utable(p)
    b = _ulookup(tbl, xa, w)
    b === nothing && (b = _umiss(tbl, p, T, w))
    lo, hi = w, w
    for e in @atomic tbl.entries
        (e.T === T && e.lo <= w <= e.hi) && (lo = e.lo; hi = e.hi)
    end
    if b isa Builder
        fo = _UCall{typeof(g),typeof(b)}(b)
        fp = Base.invokelatest(_ufptr, typeof(fo), Val(N))::Ptr{Cvoid}
    else
        fo, fp = b, C_NULL
    end
    e = PEntry(T, fp, fo, lo, hi)
    @lock _LOCK begin
        s = _SESSION[]
        old = (@atomic t.session) === s ? (@atomic t.entries) : PEntry[]
        new = PEntry[]
        for x in old
            (x.T === T && x.lo <= hi && lo <= x.hi) || push!(new, x)
        end
        push!(new, e)
        @atomic :release t.entries = new
        @atomic :release t.session = s
    end
    return e
end
"The pointer entry for the held value at entry pattern `g`, from its table, or made."
@inline function _pentry(p::EntryPos, g, xa::XAny, w::UInt, ::Val{N}) where {N}
    t = _ptable(g)
    e = _plookup(t, xa, w)
    e === nothing && return Base.inferencebarrier(_pmiss)(t, p, g, xa, w, N)::PEntry
    return e
end
