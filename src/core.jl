# ---------------------------------------------------------------------------
# Core types: traits, trait objects, witnesses, operation calls.
#
# Inside library code a trait object is a `TObj`, a tuple of views, one per
# trait it carries (with supertraits). Each trait defines one method per
# operation on `TObj{T} where {T >: Trait}`, which forwards to the view's
# implementation. Nothing else has methods for `TObj`, so library code can do
# with a trait object exactly what its traits declare: the contract is
# enforced by dispatch, and `check_worker` reports violations by name.
# ---------------------------------------------------------------------------

"Supertype of every trait: `@trait ColTable{R}` defines `abstract type ColTable{R} <: Trait end`."
abstract type Trait end
# defined before the generators that use it (`_carries_static`): a generator run as plain code
# executes in the world of its definition
"`is_trait(X)`: whether `X` was declared with `@trait`."
is_trait(@nospecialize(X)) = X isa Type && X !== Union{} && X <: Trait

"""
    Callable{A, S}

The built-in trait for a function argument: called with arguments of the tuple type `A`, it
returns an `S`. Any callable conforms; every call is checked. Its default attribute is `Dynamic`
(traits reference §5.8): a function from plain code is erased to a pointer to its code compiled for
`A`, and the worker is compiled once per signature; `Compiled{Callable{A, S}}` at the position, or
`compiled_for(f)` at the call, compiles the worker per function type. Functions of the trait world
are not affected by the default.
"""
abstract type Callable{A<:Tuple,S} end

"One trait's view of a value: the witness that says where its operations come from, and the key `K`."
abstract type AbstractView{X,W,K} end

"""
Where a part of the user's object lives: its byte offset and its field index. The
offset -1 means the object itself (a type that implements the operations).
"""
struct Slot
    off::Int
    idx::Int
end
const SELF = Slot(-1, 0)

"""
    Key{I, F}

The key of a trait that declares fields (note "Terms": what a bound can see): the
receiver type `I` (`Nothing` for a trait with fields only) and `F`, a named-tuple
type of the declared fields' types in the conforming type. A trait without fields is
keyed by its receiver type alone.
"""
struct Key{I,F} end
"The receiver type of a key."
_impl(::Type{K}) where {K} = K
_impl(::Type{Key{I,F}}) where {I,F} = I
"The type of declared field `f` in a key."
_keyfield(::Type{Key{I,F}}, f::Symbol) where {I,F} = fieldtype(F, f)

"""
A view: the witness, the user's object `o` when its type is mutable (`nothing` otherwise),
the slots of the receiver and of the declared fields, and `parts`, those values
held, typed by the key (note "Declaring a trait": a mutable object is read through, an
immutable one held, which is equivalent because none of its fields can be rebound). Its
type depends on the trait and the key, never on the user's type, so one worker compiled
per key serves every conforming type, mutable or immutable, and an immutable user type is
never boxed.
"""
struct View{X,W,K,N,P} <: AbstractView{X,W,K}
    w::W
    o::Any
    r::Slot
    fs::NTuple{N,Slot}
    parts::P
end
"""
A held view: the view of an immutable value that is its own receiver, holding the whole
value (`parts[1]`) and its declared fields' values, with no read-through object or slot (the
user's decision, session 29). Reading it is a field load, and a trait object of an immutable value
is as large as the value: a `Dynamic` of it is one box, as a plain abstractly typed value is. A key
used both held and read through has one worker per view type. The declared fields' slots are kept
only to rebuild a result like the input.
"""
struct Held{X,W,K,N,P} <: AbstractView{X,W,K}
    w::W
    fs::NTuple{N,Slot}
    parts::P
end
"The view of `r` as its own receiver, with no declared fields (generic implementations' constraints, `Like` results): held when immutable."
@inline _selfview(::Type{X}, w::W, r) where {X,W} = ismutable(r) ?
    View{X,W,typeof(r),0,Tuple{typeof(r)}}(w, r, SELF, (), (r,)) :
    Held{X,W,typeof(r),0,Tuple{typeof(r)}}(w, (), (r,))
"The view type `_selfview` makes for a value of type `R`."
_selfview_type(@nospecialize(X), @nospecialize(W), @nospecialize(R)) =
    isconcretetype(R) && !ismutabletype(R) ? Held{X,W,R,0,Tuple{R}} : View{X,W,R,0,Tuple{R}}

"The receiver a view stands for: the user's object, or its forwarding field, read now (held for an immutable type)."
@inline function _rep(v::View{X,W,K}) where {X,W,K}
    getfield(v, :o) === nothing && return getfield(getfield(v, :parts), 1)
    return _loadpart(_impl(K), v, getfield(v, :r))
end
@inline _rep(v::Held) = getfield(getfield(v, :parts), 1)
"Whether a view holds its parts (an immutable value): its fields cannot be written."
@inline _isheld(v::View) = getfield(v, :o) === nothing
@inline _isheld(::Held) = true
"The slot of a view's receiver in the user's object (`SELF`: the object itself)."
@inline _viewslot(v::View) = getfield(v, :r)
@inline _viewslot(::Held) = SELF
"The user's object a view reads, or `nothing` when it holds only parts (a held view holds the whole value)."
@inline _viewobject(v::View) = getfield(v, :o)
@inline _viewobject(v::Held) = getfield(getfield(v, :parts), 1)
"The key of a view type."
_reptype(::Type{<:AbstractView{X,W,K}}) where {X,W,K} = K

# --- reading and writing the user's object at an offset (experiments/lens/layout.md) ---------------
#
# The loads and stores carry Julia's own alias metadata (TBAA `jtbaa_mutab`), so a loop
# that reads `t.data[i]` while storing into another array vectorizes as in plain Julia;
# without it, LLVM reloads the field after every store (5× on such loops).

@inline _objptr(o) = ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), o)
const _TBAA_MD = """
!0 = !{!"jtbaa"}
!1 = !{!"jtbaa", !0, i64 0}
!2 = !{!"jtbaa_value", !1, i64 0}
!3 = !{!"jtbaa_mutab", !2, i64 0}
!4 = !{!3, !3, i64 0}
"""
const _LLVM_PRIM = IdDict{Any,String}(Float64 => "double", Float32 => "float", Int64 => "i64", UInt64 => "i64",
                                      Int32 => "i32", UInt32 => "i32", Int16 => "i16", UInt16 => "i16")
@generated function _tbaa_load(p::Ptr{T}) where {T}
    t = T <: Ptr ? "ptr" : get(_LLVM_PRIM, T, nothing)
    t === nothing && return :(unsafe_load(p))
    ir = "define $t @entry(ptr %p) #0 {\n  %v = load $t, ptr %p, align $(Base.datatype_alignment(T)), !tbaa !4\n  ret $t %v\n}\nattributes #0 = { alwaysinline }\n" * _TBAA_MD
    return :(Base.llvmcall(($ir, "entry"), $T, Tuple{Ptr{$T}}, p))
end
@generated function _tbaa_store(p::Ptr{T}, x::T) where {T}
    t = get(_LLVM_PRIM, T, nothing)
    t === nothing && return :(unsafe_store!(p, x); nothing)
    ir = "define void @entry(ptr %p, $t %x) #0 {\n  store $t %x, ptr %p, align $(Base.datatype_alignment(T)), !tbaa !4\n  ret void\n}\nattributes #0 = { alwaysinline }\n" * _TBAA_MD
    return :(Base.llvmcall(($ir, "entry"), Cvoid, Tuple{Ptr{$T},$T}, p, x); nothing)
end

"How a field of declared type `T` is stored: `:singleton`, `:bits` (inline, isbits), `:ref` (a pointer), or `:other` (read with `getfield`)."
function _storage(@nospecialize(T))
    T isa DataType && Base.issingletontype(T) && return :singleton
    isbitstype(T) && return :bits
    (T isa Union && Base.isbitsunion(T)) && return :other
    T isa DataType && Base.allocatedinline(T) && return :other
    return :ref
end
"A part of the user's object, of exactly the type `T` in the key: the object itself, or its field at slot `s`."
# The view is passed, not the user's object it holds (`o::Any`): every call on this path then has
# concrete argument types, a fact, and the object is read only by builtins and intrinsics.
@inline function _loadpart(::Type{T}, v::View, s::Slot) where {T}
    getfield(s, :off) < 0 && return getfield(v, :o)::T
    return _loadfield(T, v, s)
end
"No receiver type (every operation served by a default): there is no receiver."
@inline _loadpart(::Type{Nothing}, v::View, s::Slot) = nothing
"Whether the runtime has the field-offset intrinsics (patched Julia, julia-support.md piece 3)."
const _HAS_FIELD_INTRINSICS = isdefined(Core.Intrinsics, :getfield_at_offset)

@generated function _loadfield(::Type{T}, v::View, s::Slot) where {T}
    k = _storage(T)
    k === :singleton && return :($(T.instance))
    # the runtime's intrinsic: a load at the offset with Julia's alias metadata, and the null check
    _HAS_FIELD_INTRINSICS && k in (:bits, :ref) &&
        return :(Core.Intrinsics.getfield_at_offset(getfield(v, :o), $T, getfield(s, :off))::$T)
    o = :(getfield(v, :o))
    # no GC.@preserve: the trait object holding `o` is live for the call, and no safepoint lies
    # between computing the address and the load (a preserve region boxes values in loops)
    k === :bits && return :(_tbaa_load(Ptr{$T}(_objptr($o) + getfield(s, :off))))
    k === :other && return :(getfield($o, getfield(s, :idx))::$T)
    return quote
        p = _tbaa_load(Ptr{Ptr{Cvoid}}(_objptr($o) + getfield(s, :off)))
        p == C_NULL && throw(UndefRefError())
        unsafe_pointer_to_objref(p)::$T
    end
end
"Write a field of the user's (mutable) object: an isbits field at its offset, any other through `setfield!` and its write barrier."
@generated function _storefield(::Type{T}, v::View, s::Slot, x) where {T}
    o = :(getfield(v, :o))
    _HAS_FIELD_INTRINSICS && _storage(T) in (:bits, :ref) &&
        return :(Core.Intrinsics.setfield_at_offset($o, $T, getfield(s, :off), x::$T); nothing)
    _storage(T) === :bits && return :(_tbaa_store(Ptr{$T}(_objptr($o) + getfield(s, :off)), x::$T); nothing)
    return :(setfield!($o, getfield(s, :idx), x::$T); nothing)
end

"""
    TObj{T, V}

A trait object inside library code. `T` is the union of the traits it
carries, `V` the tuple of their views. Workers specialize on `V`, so code is
compiled per representation, never per user type.
"""
struct TObj{T,V<:Tuple}
    views::V
    TObj{T,V}(views::V) where {T,V<:Tuple} = new{T,V}(views)
end
"The trait family of a trait instance (`ArrayLike{Float64, 1, Vector{Float64}}` gives `ArrayLike`), or `X` itself."
_family(@nospecialize(X)) = (u = Base.unwrap_unionall(X); u isa DataType && u <: Trait ? u.name.wrapper : X)
"""
    PTag{F, i, v}

In a trait object's trait set: parameter `i` of trait family `F` has the value `v`. The set is a
union of trait families and these tags, never of trait instances with type variables, so a
worker's signature, `TObj{T} where T >: Union{StateVector, PTag{StateVector, 1, Float64}}`,
has no static parameter that its argument does not determine. (With one, `T >: StateVector{Float64, R}`,
Julia cannot specialize the call and passes the trait object boxed.)
"""
struct PTag{F,i,v} end
_isptag(@nospecialize(X)) = X isa DataType && X <: PTag

"""
    Through{Y, A}

A bound's item parameter that names a trait (traits reference §8.2): items seen through `Y`, with
the attribute `A` the bound gives them (`:default`, `:compiled`, `:dynamic`). In a worker's bound it is
the value of the parameter's tag; a trait object whose item type is a held value of `Y` (`Compiled{Y}`,
`Dynamic{Y}`, `Kept{Y}`) or a trait object carrying `Y` has the tag for every `A`, so one worker
takes `Compiled` and `Dynamic` items alike.
"""
struct Through{Y,A} end
"The item parameter `p` with each held value of `Y` (`Compiled{Y}`, `Dynamic{Y}`, `Kept{Y}`), or trait object type carrying `Y`, replaced by `Through{Y, A}`; the variants, one per such `Y`."
function _through_variants(@nospecialize(p), @nospecialize(A))
    # a held value of `Y`: `Compiled{Y}`, `Dynamic{Y}`, `Kept{Y}` (a trait's name in storage)
    Y = _kept_item(p)
    Y === nothing || return Any[Through{Y,A}]
    u = Base.unwrap_unionall(p)
    u isa DataType || return Any[]
    if u.name === Base.typename(TObj)          # a trait object, or "any trait object carrying Y" (`TObj{T} where T >: Y`)
        Ts = u.parameters[1]
        out = Any[]
        for Y in Base.uniontypes(Ts isa TypeVar ? Ts.lb : Ts)
            (_isptag(Y) || !(Y isa Type) || !is_trait(Y)) && continue
            push!(out, Through{_family(Y),A})
        end
        return out
    end
    p isa DataType || return Any[]
    out = Any[]
    ps = p.parameters
    for (i, q) in enumerate(ps)
        for v in _through_variants(q, A)
            args = Any[ps...]
            args[i] = v
            push!(out, Core.apply_type(p.name.wrapper, args...))
        end
    end
    return out
end
"""
The trait `Y` of a held value's type, `Compiled{Y}`, `Dynamic{Y}` or `Kept{Y}`; else `nothing`. By
name: this runs in generators, in a world before `Dynamic` is defined.
"""
function _kept_item(@nospecialize(p))
    p isa DataType && (p.name.name === :Dynamic || p.name.name === :Compiled || p.name.name === :Kept) &&
        p.name.module === TraitWorld && return p.parameters[1]
    return nothing
end
"The trait set of trait instances: their families, and a tag per parameter they fix (the receiver type excluded); for an item type seen through a trait, its `Through` tags too."
function _encode_traits(insts)
    ms = Any[]
    for X in insts
        F = _family(X)
        any(m -> m === F, ms) || push!(ms, F)
        u = Base.unwrap_unionall(X)
        u isa DataType || continue
        ps = u.parameters
        Yc = _compiled_view_item(ps[end])
        for i in 1:length(ps)-1
            p = ps[i]
            p isa TypeVar && continue
            t = PTag{F,i,p}
            any(m -> m === t, ms) || push!(ms, t)
            for A in (:default, :compiled, :dynamic)
                vs = _through_variants(p, A)
                Yc === nothing || append!(vs, _any_variants(p, Through{Yc,A}))
                for v in vs
                    tv = PTag{F,i,v}
                    any(m -> m === tv, ms) || push!(ms, tv)
                end
            end
        end
    end
    return Union{ms...}
end
"""
The item trait of BaseTraits' `CompiledItems{Y}` or `CompiledValues{Y}` at a key, whose items of an
abstract type are read at their own keys but declared `Any`; else `nothing`. By name: this runs in
generators, in a world before BaseTraits is defined.
"""
function _compiled_view_item(@nospecialize(K))
    K isa DataType || return nothing
    # a `Dynamic` trait object of such a view keeps the item trait in its erased key (by name, as above)
    K.name.name === :ErasedKey && K.name.module === TraitWorld && return K.parameters[2] === Nothing ? nothing : K.parameters[2]
    (K.name.name === :CompiledItems || K.name.name === :CompiledValues) && nameof(K.name.module) === :BaseTraits || return nothing
    return K.parameters[1]
end
"The item parameter `p` with `Any` (at the top, or as a type's parameter) replaced by `t`."
function _any_variants(@nospecialize(p), @nospecialize(t))
    p === Any && return Any[t]
    p isa DataType || return Any[]
    out = Any[]
    for (i, q) in enumerate(p.parameters)
        q === Any || continue
        args = Any[p.parameters...]
        args[i] = t
        push!(out, Core.apply_type(p.name.wrapper, args...))
    end
    return out
end

"""
A trait set or a worker's lower bound decoded into trait patterns: each family applied to the
parameters its tags fix and a type variable for each other one, the receiver type last
(`StateVector{Float64, R} where R`). What the machinery reasons about.
"""
function _decode_traits(@nospecialize(lb))
    ms = Base.uniontypes(lb)
    pats = Any[]
    for F in ms
        (_isptag(F) || !is_trait(F)) && continue
        u = Base.unwrap_unionall(F)::DataType
        np = length(u.parameters)
        args = Any[]
        vars = TypeVar[]
        for i in 1:np
            v = nothing
            if i < np
                for m in ms
                    if _isptag(m) && (mp = (m::DataType).parameters; mp[1] === F && mp[2] === i && !(mp[3] isa TypeVar))
                        v = mp[3]
                        break
                    end
                end
            end
            if v === nothing
                tv = TypeVar(i == np ? :Self : Symbol(:P, i))
                push!(vars, tv)
                push!(args, tv)
            else
                push!(args, v)
            end
        end
        body = Core.apply_type(F, args...)
        for tv in reverse(vars)
            body = UnionAll(tv, body)
        end
        push!(pats, body)
    end
    return Union{pats...}
end

@generated function _traitset(::Type{V}) where {V<:Tuple}
    return _encode_traits(Any[(p::DataType).parameters[1] for p in (V::DataType).parameters])
end
@inline TObj(views::Tuple) = TObj{_traitset(typeof(views)),typeof(views)}(views)

@inline viewof(t::TObj, ::Type{X}) where {X} = _viewof(X, getfield(t, :views)...)
# a view carries a trait instance (`ArrayLike{Float64, 1, Vector{Float64}}`); `X` is the trait family
@inline _viewof(::Type{X}, v::AbstractView{Y}, rest::AbstractView...) where {X,Y} = Y <: X ? v : _viewof(X, rest...)

# --- trait parameters: associated types (note "Declaring a trait": Parameters) ------------

Base.Experimental.@max_methods 1 function trait_params end
"`trait_params(X)`: the names of trait `X`'s parameters besides the representation, in order."
trait_params(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function param end
"""
`param(X, Val(p), R)`: parameter `p` of trait `X` at representation `R`, an
associated type: one value per implementation, defined by the trait's equation
(`T = eltype(R)`) or by the implementation (`@implement ArrayLike{Float64, 1} MyVector`).
"""
param
Base.Experimental.@max_methods 1 function param_bound end
@doc "`param_bound(X, Val(p))`: the bound a trait declares on its parameter `p` (`T <: NumberLike`)." param_bound
"The trait instance a view of representation `R` carries: `X` with its parameters at `R`, the representation last."
function _instance(@nospecialize(X), @nospecialize(R))
    ps = trait_params(X)
    isempty(ps) && return X{R}
    return Core.apply_type(X, Any[param(X, Val(p), R) for p in ps]..., R)
end
"Whether a trait object carrying the trait set `T` carries `X`, a family or a partly applied instance."
_carries(@nospecialize(T), @nospecialize(X)) = any(Y -> Y <: X, Base.uniontypes(_decode_traits(T)))
"""
`_carries` at types known to the compiler, as a constant: a pure computation on types (no method
table read), made by a generator, so compiled code holds its answer and no edge to the reflective
code that computes it (whose native code a load may invalidate).

The generators' own code is compiled into the image like any plain code, so it is written fully
typed (the types it reflects on asserted: `::DataType`, `::Int`): fully typed code is invalidated
only by stakeholders and pirates. Untyped, `length(u.parameters)` left an edge at `Colon(::Int,
::Any)`, which Unitful matches, and a package loaded before TraitWorld made the image's code invalid.
"""
@generated _carries_static(::Type{T}, ::Type{X}) where {T,X} = _carries(T, X)

# --- dynamic values ----------------------------------------------------------

"""
    Dynamic{X}

A value of any type conforming to trait `X`, kept beyond a call and reached through `X`'s
operations (note "Dynamic values"). It holds the user's object (traits reference §7; lowering
§13): the view of `X` for the object's type is made when an operation runs, folded where the type
is one of the call site's candidates. Made from a value, `Dynamic{X}(x)`, or from a trait object
inside a trait module, `Dynamic{X}(t)`, or by storing one where a `Dynamic{X}` is declared.
A trait object whose views hold only parts of an immutable value (no whole object to hold), and a
new receiver value of a constructor operation, are held as trait objects instead.
An operation of `X` on it is split over the candidate types at the call site and asserts the
declared result type; passed to a function bounded by `X`, it is opened, and the worker for its
key runs.
"""
struct Dynamic{X}
    t::Any            # the user's object, or (see above) a trait object
    # from a trait object: only one at the erased key (a `Dynamic` value); one at its key is refused,
    # since only `with_dynamic` changes an attribute
    function Dynamic{X}(t::TObj{T,V}) where {X,T,V}
        _carries_static(T, X) || Base.inferencebarrier(_dyn_refuse)(X, T)     # another trait first: the clearer error
        _is_erased(V) || Base.inferencebarrier(_cast_refuse)(X, :Dynamic, :Compiled)
        return Dynamic{X}(Val(:keep), t)
    end
    "The user's object a trait object reads, kept whatever its key (`Kept{X}(t)` records the key's attribute)."
    function Dynamic{X}(::Val{:keep}, t::TObj{T}) where {X,T}
        _carries_static(T, X) || Base.inferencebarrier(_dyn_refuse)(X, T)
        tn = _narrow(X, t)               # the trait object is the user's object: a kept value follows its fields
        o = _tobj_object(tn)
        if o === nothing                 # only parts of an immutable value: keep the trait object
            _register_candidate!(_family_of(X), typeof(tn))   # a candidate of the call-site splits (part (D))
            return new{X}(tn)
        end
        _NoteCandidate{_family_of(X)}()(o)
        return new{X}(o)
    end
    @inline function Dynamic{X}(x) where {X}
        v = _assemble(_family_list(X), x)
        v === NOTRAIT && _dyn_nonconforming(X, x)
        _register_candidate!(_family_of(X), typeof(x))
        return new{X}(x)
    end
    "A dynamic value holding the trait object `t` itself (a new receiver value of a constructor operation)."
    function Dynamic{X}(::Val{:hold}, t::TObj) where {X}
        _register_candidate!(_family_of(X), typeof(t))
        return new{X}(t)
    end
    "A dynamic value holding `x`, checked to conform by the caller (`@dynamic_of`): reached by `invoke`, so `x` keeps its box."
    Dynamic{X}(::Val{:checked}, @nospecialize(x)) where {X} = new{X}(x)
    "A dynamic value holding what the held value `h` holds: a call at `h`'s concrete type, never at the `Any`-typed object."
    Dynamic{X}(::Val{:of}, h) where {X} = new{X}(getfield(h, :t))
end
"""
    Compiled{X}

A value of any type conforming to trait `X` whose attribute is `Compiled`, held where the code does
not know its type (traits reference §7; lowering §13): `compiled_for(d)` of a `Dynamic{X}`, or made
from a value, `Compiled{X}(x)`, or from a trait object at its key. Like `Dynamic{X}` it holds the
user's object, and an operation or a field read on it is the same call-site split. Passed to a
function bounded by `X`, it is opened by its type: the code compiled for its key is selected once
per call (a function barrier), where a `Dynamic{X}` runs the code compiled once.
"""
struct Compiled{X}
    t::Any            # the user's object, or a trait object (as for `Dynamic`)
    # from a trait object at its key; one at the erased key is refused (only `compiled_for` casts)
    function Compiled{X}(t::TObj{T,V}) where {X,T,V}
        _carries_static(T, X) || Base.inferencebarrier(_dyn_refuse)(X, T, :Compiled)
        _is_erased(V) && Base.inferencebarrier(_cast_refuse)(X, :Compiled, :Dynamic)
        tn = _narrow(X, t)
        o = _tobj_object(tn)
        if o === nothing
            _register_candidate!(_family_of(X), typeof(tn))
            return new{X}(tn)
        end
        _NoteCandidate{_family_of(X)}()(o)
        return new{X}(o)
    end
    @inline function Compiled{X}(x) where {X}
        v = _assemble(_family_list(X), x)
        v === NOTRAIT && _dyn_nonconforming(X, x)
        _register_candidate!(_family_of(X), typeof(x))
        return new{X}(x)
    end
    "A compiled value holding the trait object `t` itself (a new receiver value of a constructor operation)."
    function Compiled{X}(::Val{:hold}, t::TObj) where {X}
        _register_candidate!(_family_of(X), typeof(t))
        return new{X}(t)
    end
    "A compiled value holding `x`, checked to conform by the caller: reached by `invoke`, so `x` keeps its box."
    Compiled{X}(::Val{:checked}, @nospecialize(x)) where {X} = new{X}(x)
    "A compiled value holding what the held value `h` holds: a call at `h`'s concrete type."
    Compiled{X}(::Val{:of}, h) where {X} = new{X}(getfield(h, :t))
end
"""
    Kept{X}

A value of any type conforming to trait `X`, with its attribute as data: `Compiled` or `Dynamic`
(traits reference §7). What a trait's name means as the type of a field or of a container's items
in a trait module, where values of both attributes sit side by side: one concrete type, so it is
stored inline and reading or making one allocates nothing. It holds the user's object, as
`Compiled{X}` and `Dynamic{X}` do; an operation or a field read on it is the same call-site split;
at a bound its attribute decides. Made by storing a trait object (its key gives the attribute) or
any value of the trait world (it keeps its attribute), or `Kept{X}(x)` from a plain value (the
trait's default: `Dynamic` under `@default_with_dynamic_self`, else `Compiled`).
"""
struct Kept{X}
    t::Any            # the user's object, or a trait object (as for `Dynamic`)
    compiled::Bool
    "A kept value holding `x`, checked to conform by the caller."
    Kept{X}(::Val{:checked}, @nospecialize(x), compiled::Bool) where {X} = new{X}(x, compiled)
    "A kept value holding what the held value `h` holds: a call at `h`'s concrete type."
    Kept{X}(::Val{:of}, h, compiled::Bool) where {X} = new{X}(getfield(h, :t), compiled)
end
"Any value of `X` that holds the user's object: `Compiled{X}`, `Dynamic{X}`, `Kept{X}`."
const HeldValue{X} = Union{Compiled{X},Dynamic{X},Kept{X}}
"Whether a held value is `Compiled`."
@inline _held_compiled(::Compiled) = true
@inline _held_compiled(::Dynamic) = false
@inline _held_compiled(k::Kept) = getfield(k, :compiled)
@noinline _dyn_nonconforming(@nospecialize(X), @nospecialize(x)) = throw(TraitBoundError("a $(typeof(x)) does not conform to $X"))
"The user's object a trait object reads (that of its first view), or `nothing` when its views hold only parts."
@inline _tobj_object(t::TObj) = _viewobject(getfield(t, :views)[1])
"Registers the type of a dynamic value's object as a candidate of `F`'s call-site splits (called with an object of unknown type)."
struct _NoteCandidate{F} end
@inline (::_NoteCandidate{F})(o) where {F} = _register_candidate!(F, typeof(o))
"""
The flag of a candidate type `C` of family `F`: the session in which it was registered. One flag per
pair, a constant of the code that makes such a `Dynamic`, so that making one registers the type once
per session instead of searching the registry each time (157 ns with 64 candidates, E-125). A flag
saved in a package image holds another session's stamp, so the type is registered again, once.
"""
@generated _cand_flag(::Type{F}, ::Type{C}) where {F,C} = :($(Ref{UInt}(0)))
@inline function _register_candidate!(::Type{F}, ::Type{C}) where {F,C}
    flag = _cand_flag(F, C)
    flag[] === _SESSION[] && return nothing
    Base.inferencebarrier(_register_candidate_slow!)(F, C, flag)
    return nothing
end
@noinline function _register_candidate_slow!(@nospecialize(F), @nospecialize(C), flag::Base.RefValue{UInt})
    CC.register_dynamic_candidate!(F, C)
    flag[] = _SESSION[]
    return nothing
end
"""
A dynamic value of `X` keeps only the views of `X` and its supertraits: what its operations and
the bounds that open it can see (note "Keys"). A column made from a reader's `CSVColumn` trait
object and kept as a `Dynamic{Column}` then runs the table's workers compiled for `Column` alone,
not new ones for the pair of views. A trait object with one view is kept as it is.
"""
@inline _narrow(::Type{X}, t::TObj{T,V}) where {X,T,V} = fieldcount(V) == 1 ? t : Base.inferencebarrier(_narrow_slow)(X, t)
const _NARROW = IdDict{Any,Any}()
@machinery function _narrow_slow(@nospecialize(X), @nospecialize(t::TObj))
    V = typeof(getfield(t, :views))
    keep = @lock _LOCK get(_NARROW, (X, V), nothing)
    if keep === nothing
        F = _family(X)
        if F isa DataType || F isa UnionAll
            fams = Any[]
            for B in bound_traits(F), Y in trait_closure(_family(B))
                push!(fams, _family(Y))
            end
            keep = Tuple(i for (i, P) in enumerate(V.parameters) if any(G -> P.parameters[1] <: G, fams))
        else
            keep = Tuple(1:fieldcount(V))
        end
        @lock _LOCK (_NARROW[(X, V)] = keep)
    end
    length(keep) == fieldcount(V) && return t
    views = getfield(t, :views)
    return TObj(Tuple(views[i] for i in keep))
end
# Constructors make or keep a value, never cast (traits reference §6): only `compiled_for` and
# `with_dynamic` change an attribute. On a value that has one they keep it where it matches, else
# they refuse, naming the cast.
Dynamic{X}(d::Dynamic{X}) where {X} = d
Compiled{X}(c::Compiled{X}) where {X} = c
Kept{X}(k::Kept{X}) where {X} = k
Dynamic{X}(c::Compiled{X}) where {X} = Base.inferencebarrier(_cast_refuse)(X, :Dynamic, :Compiled)
Compiled{X}(d::Dynamic{X}) where {X} = Base.inferencebarrier(_cast_refuse)(X, :Compiled, :Dynamic)
Dynamic{X}(k::Kept{X}) where {X} = getfield(k, :compiled) ? Base.inferencebarrier(_cast_refuse)(X, :Dynamic, :Compiled) :
    Dynamic{X}(Val(:of), k)
Compiled{X}(k::Kept{X}) where {X} = getfield(k, :compiled) ? Compiled{X}(Val(:of), k) :
    Base.inferencebarrier(_cast_refuse)(X, :Compiled, :Dynamic)
Kept{X}(d::Dynamic{X}) where {X} = Kept{X}(Val(:of), d, false)
Kept{X}(c::Compiled{X}) where {X} = Kept{X}(Val(:of), c, true)
"A trait object kept: its key gives the attribute, at its own key `Compiled`, at the erased key `Dynamic`."
function Kept{X}(t::TObj{T,V}) where {X,T,V}
    d = Dynamic{X}(Val(:keep), t)
    return Kept{X}(Val(:of), d, !_is_erased(V))
end
"A plain value kept: the trait's default, `Dynamic` under `@default_with_dynamic_self` for a value not of the trait world, else `Compiled`."
@inline function Kept{X}(x) where {X}
    c = Compiled{X}(x)
    dyn = default_attribute(_family_of(X)) === :dynamic && !_from_trait_world(x)
    return Kept{X}(Val(:of), c, !dyn)
end
Base.convert(::Type{Kept{X}}, k::Kept{X}) where {X} = k
"A plain value assigned where a trait's name is declared: first seen there, the trait's default (traits reference §7)."
Base.convert(::Type{Kept{X}}, x) where {X} = Kept{X}(x)
Base.convert(::Type{Kept{X}}, t::Union{TObj,Dynamic{X},Compiled{X}}) where {X} = Kept{X}(t)
Base.convert(::Type{Dynamic{X}}, t::TObj) where {X} = Dynamic{X}(t)
Base.convert(::Type{Compiled{X}}, t::TObj) where {X} = Compiled{X}(t)
@noinline _cast_refuse(@nospecialize(X), to::Symbol, from::Symbol) =
    throw(TraitBoundError("a $from value of $X cannot be made a $to{$X}: only a cast changes a value's attribute; write " *
                          (to === :Dynamic ? "`with_dynamic(x)`" : "`compiled_for(x)`")))
@noinline _dyn_refuse(@nospecialize(X), @nospecialize(T), how::Symbol = :Dynamic) =
    throw(ArgumentError("a trait object carrying $(join(string.(Base.uniontypes(_decode_traits(T))), ", ")) cannot be kept as a $how{$X}"))
"""
The trait object of a dynamic value: what a bound opens, and what its operations run on. Made
from the user's object, as `Dynamic{X}(x)` would keep it (`_dyn_tobj`), or the trait object it holds.
"""
@inline opened(d::HeldValue{X}) where {X} = _Open{X}()(getfield(d, :t))
"Opening a dynamic value's object: as a value of its own type, so a call with an object of unknown type dispatches on the object alone."
struct _Open{X} end
@inline (::_Open{X})(t::TObj) where {X} = t
@inline (::_Open{X})(x) where {X} = _dyn_tobj(X, x)
"""
An operation `f` on a dynamic value of `X`, as the function a call-site split calls with the value's
object first (`Compiler.split_call`): `f` on the object's trait object. One method per arity up to
six, so a recursion through dynamic values passes no varargs tuple.
"""
struct _DynOp{X,F}
    f::F
end
@inline _dynop(::Type{X}, f::F) where {X,F} = _DynOp{X,F}(f)
@inline (op::_DynOp{X})(t) where {X} = op.f(_Open{X}()(t))
@inline (op::_DynOp{X})(t, a) where {X} = op.f(_Open{X}()(t), a)
@inline (op::_DynOp{X})(t, a, b) where {X} = op.f(_Open{X}()(t), a, b)
@inline (op::_DynOp{X})(t, a, b, c) where {X} = op.f(_Open{X}()(t), a, b, c)
@inline (op::_DynOp{X})(t, a, b, c, e) where {X} = op.f(_Open{X}()(t), a, b, c, e)
@inline (op::_DynOp{X})(t, a, b, c, e, g) where {X} = op.f(_Open{X}()(t), a, b, c, e, g)
@inline (op::_DynOp{X})(t, a, b, c, e, g, h) where {X} = op.f(_Open{X}()(t), a, b, c, e, g, h)
@inline (op::_DynOp{X})(t, args...) where {X} = op.f(_Open{X}()(t), args...)
"""
The user's object a dynamic value holds: what a view over the user's container stores back
(BaseTraits' `DynamicItems`). An `ArgumentError` if the value holds only the parts its trait sees.
"""
@inline function _dyn_object(d::HeldValue)
    t = getfield(d, :t)
    t isa TObj || return t
    return Base.inferencebarrier(_dyn_object_slow)(t)
end
function _dyn_object_slow(t::TObj)
    o = _tobj_object(t)
    o === nothing && throw(ArgumentError("this dynamic value holds the parts its trait sees, not the user's object"))
    return o
end
"What a dynamic value's identity is: the user's object, or the trait object where it holds one without an object."
@inline function _dyn_identity(d::HeldValue)
    t = getfield(d, :t)
    t isa TObj || return t
    o = Base.inferencebarrier(_tobj_object)(t)
    return o === nothing ? t : o
end
"""
    DynamicOf{X}()

The function `x -> Dynamic{X}(x)` as a value of its own type. Called with a value of unknown type,
it dispatches on that value alone, through the call site's cache. A constructor call `Dynamic{X}(x)`
passes the type `Dynamic{X}` as the function, which the per-site cache does not serve (compiler §3.2):
100 ns against 25 at a run-time site.
"""
struct DynamicOf{X} end
@inline (::DynamicOf{X})(x) where {X} = Dynamic{X}(x)
"""
    @dynamic_of X x

`Dynamic{X}(x)` for a value `x` of unknown type, split over `X`'s candidate types at the call site
(`Compiler.split_call`): for a candidate the conformance folds to a constant and the user's object
is held as it is, already boxed; any other type is dispatched (`DynamicOf{X}`). Written out at the
call, since a function taking `x` would be a run-time site of trait code. What a view over a user's
container does at each read (BaseTraits' `DynamicItems`).
"""
macro dynamic_of(X, x)
    TW = TraitWorld
    v = gensym(:x)
    return esc(quote
        let $v = $x
            $TW.CC.split_call($TW._family_of($X), Bool, $TW._ConformsTo{$X}(), $v)::Bool || $TW._dyn_nonconforming($X, $v)
            # an invoke at the method's own signature: a fact, so the call is inlined and `x` is held in
            # the box it came in (a call at `Any` would be a run-time site, and a call at the narrowed
            # type would box it again)
            invoke($TW.Dynamic{$X}, Tuple{Val{:checked}, Any}, Val(:checked), $v)::$TW.Dynamic{$X}
        end
    end)
end
"""
    @kept_of X x attr

A value `x` of unknown type read where it is seen through `X`, an item of a user's container
(traits reference §8.3), as a `Kept{X}`: a value that carries its attribute keeps it (`Kept{X}`,
`Compiled{X}`, `Dynamic{X}`, `compiled_for(y)`, `with_dynamic(y)`); any other value is first seen
here, `Compiled` if `attr` is `:compiled`, else `Dynamic`. The tests are `isa`, builtins; the
conformance of a plain value is split as in `@dynamic_of`; the `Kept{X}` is made by an `invoke` at
its constructor's own signature, a fact, so `x` is held in the box it came in.
"""
macro kept_of(X, x, attr)
    TW = TraitWorld
    v = gensym(:x)
    y = gensym(:y)
    plainc = attr === QuoteNode(:compiled)
    kept(o, c) = :(invoke($TW.Kept{$X}, Tuple{Val{:checked}, Any, Bool}, Val(:checked), $o, $c)::$TW.Kept{$X})
    return esc(quote
        let $v = $x
            if $v isa $TW.Kept{$X}
                $v
            elseif $v isa $TW.Dynamic{$X}
                $(kept(:(getfield($v, :t)), false))
            elseif $v isa $TW.Compiled{$X}
                $(kept(:(getfield($v, :t)), true))
            elseif $v isa $TW.WithDynamic || $v isa $TW.CompiledFor
                $y = getfield($v, :x)
                $TW.CC.split_call($TW._family_of($X), Bool, $TW._ConformsTo{$X}(), $y)::Bool || $TW._dyn_nonconforming($X, $y)
                $(kept(y, :($v isa $TW.CompiledFor)))
            else
                $TW.CC.split_call($TW._family_of($X), Bool, $TW._ConformsTo{$X}(), $v)::Bool || $TW._dyn_nonconforming($X, $v)
                $(kept(v, plainc))
            end
        end
    end)
end
"Whether `x` conforms to `X`, registering its type as a candidate (the check `@dynamic_of` splits; folded for a candidate)."
struct _ConformsTo{X} end
@inline function (::_ConformsTo{X})(x) where {X}
    _assemble(_family_list(X), x) === NOTRAIT && return false
    _register_candidate!(_family_of(X), typeof(x))
    return true
end

"""
Parameter `i` of trait family `F` as the trait object `t` carries it: the value a `where` variable named
in a bound takes (traits reference §5.1). A constant of the compiled body, per key.
"""
@generated function _trait_param(t::TObj{T,V}, ::Type{F}, ::Val{i}) where {T,V,F,i}
    for Vt in (V::DataType).parameters
        X = Base.unwrap_unionall((Vt::DataType).parameters[1])
        X isa DataType && X.name.wrapper === F || continue
        p = X.parameters[i]
        p isa TypeVar && break
        p === OpenParam && return :(Base.inferencebarrier(_param_open)($F, $i))
        return p isa Type ? :($p) : QuoteNode(p)
    end
    return :(Base.inferencebarrier(_param_open)($F, $i))
end
@noinline _param_open(@nospecialize(F), i::Int) =
    throw(TraitBoundError("parameter $i of $F is not known for this value: fix it in the bound, or pass the value Compiled"))
@noinline _param_mismatch(nm::Symbol, @nospecialize(F), i::Int, v::Symbol, @nospecialize(want), @nospecialize(got)) =
    throw(TraitBoundError("argument `$nm`: parameter $i of $F is $got, but `$v` is $want"))

"The trait family of `X`, a constant of the specialized caller (the key of the call-site splits)."
@generated _family_of(::Type{X}) where {X} = :($(_family(X)))

"""
Register the types of the implementations declared since the last call, at concrete types, as
candidates of the call-site splits of dynamic values (`Compiler.register_dynamic_candidate!`):
types with their own methods (`implementation` records) and types that forward (`projection`
records). Each batch in declaration order (file, then line), so a session that loads a package
splits over the same first candidates as the code its image compiled. Called after each
declaration (`_bump!`) and when a package is loaded (images do not run top-level code again).
"""
@machinery function _note_conformances!()
    try
        new = Any[]
        for rec in (implementation, projection), m in methods(rec)
            (@lock _CAND_LOCK m in _CAND_SEEN) && continue
            @lock _CAND_LOCK push!(_CAND_SEEN, m)
            sig = Base.unwrap_unionall(m.sig)
            (sig isa DataType && length(sig.parameters) == 3) || continue
            A, B = sig.parameters[2], sig.parameters[3]
            (A isa DataType && A <: Type && B isa DataType && B <: Type) || continue
            XA, T = A.parameters[1], B.parameters[1]
            (T isa DataType && isconcretetype(T)) || continue
            push!(new, (string(m.file), Int(m.line), _family(XA), T))
        end
        sort!(new; by = x -> (x[1], x[2]))
        for (_, _, F, T) in new
            CC.register_dynamic_candidate!(F, T)
        end
    catch
    end
    return nothing
end
const _CAND_SEEN = Base.IdSet{Any}()
const _CAND_LOCK = ReentrantLock()
"The trait object `Dynamic{X}(x)` opens to: its views of `X` and `X`'s supertraits, the whole object kept."
@inline function _dyn_tobj(::Type{X}, x) where {X}
    v = _assemble(_family_list(X), x)
    ismutable(x) || (v = _with_object(v, x))
    return _narrow(X, v)
end

# equal when they keep the same trait object: same representation type, same implementation, egal data
# equal when they hold the same object, whatever their attribute (a choice of speed, never of results)
Base.:(==)(a::HeldValue{X}, b::HeldValue{X}) where {X} = _dyn_identity(a) === _dyn_identity(b)
Base.hash(d::HeldValue, h::UInt) = hash(_dyn_identity(d), hash(:TraitWorldHeld, h))
Base.show(io::IO, d::Dynamic{X}) where {X} = print(io, "Dynamic{", X, "} at ", _represented(typeof(opened(d))))
Base.show(io::IO, d::Compiled{X}) where {X} = print(io, "Compiled{", X, "} at ", _represented(typeof(opened(d))))
Base.show(io::IO, d::Kept{X}) where {X} =
    print(io, "Kept{", X, "}: ", getfield(d, :compiled) ? "Compiled" : "Dynamic", " at ", _represented(typeof(opened(d))))
_represented(@nospecialize(T)) = T <: TObj ? join(unique([sprint(_show_key, v.parameters[3]) for v in T.parameters[2].parameters]), ", ") : string(T)
@inline _dyn_assert(x, ::Type{S}) where {S} = x::S

# --- printing by bound and representation (note "Identical or error", findings §16, §17) --------
#
# A trait object's type is machinery: `TObj{ColTable{Ramp}, Tuple{View{ColTable{Ramp}, Impl{()}, Ramp}}}`.
# It prints as what a reader needs, the bound and the representation, `ColTable at Ramp`, in
# stack traces, `MethodError`s and `typeof` alike. The concrete type stays the worker's key.

"Whether `T` is a trait object's concrete type, with views whose parameters are all known."
_printable_tobj(@nospecialize(T)) = T isa DataType && T <: TObj && T.parameters[2] isa DataType &&
    all(v -> v isa DataType && v <: AbstractView && v.parameters[1] isa DataType, T.parameters[2].parameters)

"A trait instance without its representation: `StateVector{Float64}` for `StateVector{Float64, Vector{Float64}}`."
function _show_bound(io::IO, @nospecialize(X))
    show(io, Base.typename(X).wrapper)
    ps = X.parameters[1:end-1]
    isempty(ps) && return
    print(io, "{")
    for (i, p) in enumerate(ps)
        i > 1 && print(io, ", ")
        show(io, p)
    end
    print(io, "}")
end

function _show_tobj(io::IO, @nospecialize(T))
    # views grouped by representation and how it is held: `ColTable & RowTable at Vector{Vector{Float64}}`
    groups = Any[]
    for V in T.parameters[2].parameters
        X, W, R = V.parameters[1], V.parameters[2], V.parameters[3]
        how = W <: Dyn ? " (dynamic)" : ""
        k = findfirst(g -> g[1] === R && g[2] == how, groups)
        k === nothing ? push!(groups, (R, how, Any[X])) : push!(groups[k][3], X)
    end
    for (i, (R, how, Xs)) in enumerate(groups)
        i > 1 && print(io, ", ")
        for (j, X) in enumerate(Xs)
            j > 1 && print(io, " & ")
            _show_bound(io, X)
        end
        print(io, " at ")
        _show_key(io, R)
        print(io, how)
    end
end

# A trait object's type prints by bound and key, wherever Julia prints a type, through type
# printers (`Base.Experimental.register_type_printer`, patched Julia) rather than methods of
# `show(::IO, ::Type{<:TObj})`: such a method invalidates every caller compiled for
# `show(::IO, ::Type)`, most code that prints a type (CSV's parser among them: 1.0 s on its
# first read, session 26). Without the registry (stock Julia) types print as Julia prints them.
function _show_tobj_type(io::IO, @nospecialize(T))
    _printable_tobj(T) || return _show_type_plain(io, T)
    return _show_tobj(io, T)
end
_show_type_plain(io::IO, @nospecialize(T)) =
    isdefined(Base.Experimental, :show_type_plain) ? Base.Experimental.show_type_plain(io, T) : invoke(show, Tuple{IO,Type}, io, T)
"Register the printers of trait objects' and function bounds' types, where Julia has the registry."
function _register_type_printers()
    isdefined(Base.Experimental, :register_type_printer) || return nothing
    Base.Experimental.register_type_printer(Base.typename(TObj), _show_tobj_type)
    Base.Experimental.register_type_printer(Base.typename(CObj), _show_cobj_type)
    Base.Experimental.register_type_printer(Base.typename(Builder), _show_builder_type)
    return nothing
end
"A builder's type (an untyped call's frame) prints as the implementation it builds: `implementation of PVec{Float64} at Vector{Float64}`."
function _show_builder_type(io::IO, @nospecialize(T))
    S = T isa DataType && length(T.parameters) == 1 ? T.parameters[1] : nothing
    (S isa DataType && S <: Tuple && all(V -> V isa DataType && V <: VSpec && length(V.parameters) == 6, S.parameters)) ||
        return _show_type_plain(io, T)
    print(io, "implementation of ")
    for (i, V) in enumerate(S.parameters)
        i > 1 && print(io, " & ")
        _show_bound(io, V.parameters[1])
        print(io, " at ")
        _show_key(io, V.parameters[3])
    end
end
Base.show(io::IO, t::TObj) = (print(io, "trait object "); _show_tobj(io, typeof(t)))
"A key as a reader wants it: the receiver type, then the declared fields' types, `Vector{Float64}; u::Vector{Float64}, p::Params`."
function _show_key(io::IO, @nospecialize(K))
    K isa DataType && K <: ErasedKey && return print(io, "Dynamic")
    if K isa DataType && K <: Key && length(K.parameters) == 2
        I, F = K.parameters
        I === Nothing || (show(io, I); print(io, "; "))
        F isa DataType && F <: NamedTuple || return show(io, F)
        names, types = F.parameters[1], F.parameters[2].parameters
        print(io, join(("$n::$(sprint(show, t))" for (n, t) in zip(names, types)), ", "))
    else
        show(io, K)
    end
end

# --- fields: properties a trait declares --------------------------------------

Base.Experimental.@max_methods 1 function trait_fields end
"`trait_fields(X)`: the fields trait `X` declares, as `(name, writable)` pairs."
trait_fields(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function field_type end
@doc "`field_type(X, Val(f), R)`: the declared type of field `f` at representation `R`." field_type
Base.Experimental.@max_methods 1 function trait_uses_self end
"`trait_uses_self(X)`: whether trait `X`'s declarations name the receiver type (`Self` in an operation's types, or a defining equation)."
trait_uses_self(@nospecialize(X)) = false
Base.Experimental.@max_methods 1 function _fieldmatch end
@doc "`_fieldmatch(X, Val(f), FT)`: the parameters field `f` of trait `X` defines, matched against its type `FT` in a conforming type (methods added by @trait)." _fieldmatch
Base.Experimental.@max_methods 1 function trait_field_params end
"`trait_field_params(X)`: the parameters of `X` that its declared fields define (`u::U`, `data::Vector{T}`)."
trait_field_params(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function field_isrep end
"`field_isrep(X, Val(f))`: whether field `f` is declared with the receiver type: it names the forwarding field of a one-line implementation."
field_isrep(@nospecialize(X), @nospecialize(f)) = false

# `t.f` on a trait object: a field one of its traits declares (methods added by @trait), else an error
@inline Base.getproperty(t::TObj, s::Symbol) = _tgetprop(t, Val(s))
@inline Base.setproperty!(t::TObj, s::Symbol, x) = _tsetprop!(t, Val(s), x)
@noinline _tgetprop(t::TObj, ::Val{s}) where {s} = Base.inferencebarrier(_nofield)(typeof(t), s)
@noinline _tsetprop!(t::TObj, ::Val{s}, x) where {s} = Base.inferencebarrier(_nofield)(typeof(t), s)
@noinline _nofield(@nospecialize(T), s::Symbol) =
    throw(ArgumentError("`t.$s`: no trait this trait object carries declares a field `$s`"))
@noinline _readonly(@nospecialize(X), s::Symbol) = throw(ArgumentError("field `$s` of $X is `const`: read-only"))
# a declared field of a dynamic value: split over its object, typed by the declared type at the
# parameters the `Dynamic` fixes (lowering §13)
Base.@constprop :aggressive @inline Base.getproperty(d::HeldValue{X}, s::Symbol) where {X} = _dyn_getprop(d, Val(s))
Base.@constprop :aggressive @inline Base.setproperty!(d::HeldValue{X}, s::Symbol, x) where {X} = _dyn_setprop!(d, Val(s), x)
@inline function _dyn_getprop(d::HeldValue{X}, ::Val{f}) where {X,f}
    F = _family_of(X)
    RT = _erased_ft(field_type(F, Val(f), _erased_key_of(X)))
    return CC.split_call(F, RT, _DynField{F,f}(), getfield(d, :t))::RT
end
@inline function _dyn_setprop!(d::HeldValue{X}, ::Val{f}, x) where {X,f}
    F = _family_of(X)
    y = x::_erased_ft(field_type(F, Val(f), _erased_key_of(X)))
    CC.split_call(F, Nothing, _DynFieldSet{F,f}(), getfield(d, :t), y)
    return y
end
"The erased key of `Dynamic{X}`: the parameter values `X` fixes, `Any` for an open one."
@generated function _erased_key_of(::Type{X}) where {X}
    u = Base.unwrap_unionall(X)
    (u isa DataType && u <: Trait) || return :(ErasedKey{Tuple{},Nothing})
    ps = (u::DataType).parameters
    vals = Any[(ps[i] isa TypeVar ? :OpenParam : ps[i]) for i in 1:(length(ps)::Int)-1]
    return :(ErasedKey{Tuple{$(vals...)},Nothing})
end

Base.Experimental.@max_methods 1 function _fieldpos end
@doc "`_fieldpos(X, Val(f))`: the position of declared field `f` among trait `X`'s fields (methods added by @trait)." _fieldpos
"The type of declared field `f` in key `K`: the conforming type's own field type."
_fieldkeytype(::Type{X}, ::Val{f}, ::Type{K}) where {X,f,K} = K <: Key ? _keyfield(K, f) : field_type(X, Val(f), K)

"A field `f` of trait `X` read on a trait object: a load from the user's object."
@inline function fieldget(::Type{X}, ::Val{f}, t::TObj) where {X,f}
    v = viewof(t, X)
    return _fget(X, Val(f), getfield(v, :w), v, _reptype(typeof(v)))
end
@inline function _fget(::Type{X}, ::Val{f}, w, v, ::Type{K}) where {X,f,K}
    _isheld(v) && return getfield(getfield(v, :parts), 1 + _fieldpos(X, Val(f)))
    return _loadpart(_fieldkeytype(X, Val(f), K), v, getfield(v, :fs)[_fieldpos(X, Val(f))])
end
"A field `f` of trait `X` written on a trait object: a store into the user's object, as `u.f = x` in plain Julia."
@inline function fieldset!(::Type{X}, ::Val{f}, t::TObj, x) where {X,f}
    v = viewof(t, X)
    K = _reptype(typeof(v))
    T = _erased_ft(_fieldkeytype(X, Val(f), K))
    y = x::T
    if getfield(v, :w) isa ErasedWit                          # at the erased key: split over the held object
        CC.split_call(_family_of(X), Nothing, _DynFieldSet{X,f}(), getfield(v, :o), y)
        return y
    end
    _isheld(v) && Base.inferencebarrier(_readonly)(X, f)     # the check at `@implement` refuses writable fields on immutable types
    _storefield(T, v, getfield(v, :fs)[_fieldpos(X, Val(f))], y)
    return y
end

# --- witnesses -------------------------------------------------------------

"The representation's own methods implement the trait; `D` lists the operations served by the trait's defaults."
struct Impl{D} end
# whether operation `op` is the receiver type's own method, called with the representation
@inline _direct_ok(::Impl{D}, ::Val{op}) where {D,op} = !Base.sym_in(op, D)
@inline _direct_ok(::Any, ::Val) = false
"A constraint trait's witness inside a generic implementation."
struct Wit{X,W}
    w::W
end
Wit{X}(w::W) where {X,W} = Wit{X,W}(w)
"A generic implementation `k` of trait `X`, with the witnesses of its constraint traits; `D` lists the operations left to defaults."
struct Generic{X,k,S<:Tuple,D}
    sub::S
end
"""
A type's own operations (`@implement … dynamic`): erased calls; the trait's
defaults for the operations it leaves out (`D`), which then call its own
operations. Never the representation's implementation: a type that brings its
own behaviour on a shared representation means something else by it.
"""
struct Dyn{NT<:NamedTuple,D}
    table::NT
end

# --- trait declarations, as methods defined by `@trait` --------------------

Base.Experimental.@max_methods 1 function trait_ops end
@doc "`trait_ops(X)`: the operation names of trait `X`, in declaration order." trait_ops
Base.Experimental.@max_methods 1 function op_function end
@doc "`op_function(X, Val(op))`: the function an operation is." op_function
Base.Experimental.@max_methods 1 function op_ret end
@doc "`op_ret(X, Val(op), R, Val(N))`: the declared result type at representation `R`, for `N` arguments after `r`." op_ret
Base.Experimental.@max_methods 1 function op_args end
@doc "`op_args(X, Val(op), R, Val(N))`: the declared types of the arguments after `r`, as a tuple type." op_args
Base.Experimental.@max_methods 1 function op_default end
@doc "`op_default(X, Val(op), t, args...)`: the trait's default for an operation, with `t` a trait object." op_default
Base.Experimental.@max_methods 1 function generic_op end
@doc "`generic_op(X, Val(k), Val(op), t, args...)`: generic implementation `k` of an operation." generic_op
Base.Experimental.@max_methods 1 function generic_rec end
@doc "`generic_rec(X, Val(k))`: the constraints of generic implementation `k` of trait `X` (one method per implementation)." generic_rec
Base.Experimental.@max_methods 1 function has_default end
has_default(@nospecialize(X), @nospecialize(op)) = false
Base.Experimental.@max_methods 1 function is_mutating end
is_mutating(@nospecialize(X), @nospecialize(op)) = false
Base.Experimental.@max_methods 1 function trait_concreteness end
"""
`trait_concreteness(X)`: the parts of an implementation trait `X` asks to be concrete (traits reference
§11.1), as `((name, level), …)`: a parameter's name or `:Self`, with `:error` (`@enforce_concrete_only`)
or `:warn` (`@warn_on_abstract`). Empty by default: any part may be abstract, silently.
"""
trait_concreteness(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function supertraits end
"`supertraits(X)`: traits whose operations `X` includes; their views travel with every `X` view."
supertraits(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function bundle end
"`bundle(X)`: for a bundle trait, the traits it names; `t::Table` means `t::(ColTable, RowTable)`."
bundle(@nospecialize(X)) = nothing

# --- operation calls -------------------------------------------------------

struct TraitArgumentError <: Exception
    trait::Any
    op::Symbol
    R::Any
    args::Any
end
Base.showerror(io::IO, e::TraitArgumentError) =
    print(io, "TraitArgumentError: operation `", e.op, "` of trait ", e.trait, " at representation ", e.R,
          " is declared for arguments ", op_args(e.trait, Val(e.op), e.R, Val(length(e.args))),
          ", got ", typeof(e.args))

"""
An operation call on a trait object: check the arguments against the
declaration, run the implementation the witness names, assert the result to
the declared type. Everything folds for a known view type.
"""
@inline function opcall(::Type{X}, ::Val{op}, f::F, t::TObj, args0::Vararg{Any,N}) where {X,op,F,N}
    v = viewof(t, X)
    K = _reptype(typeof(v))
    args = _seams(op_args(X, Val(op), K, Val(N)), args0)     # a trait object where `Dynamic{Y}` is declared
    args isa op_args(X, Val(op), K, Val(N)) || throw(TraitArgumentError(X, op, K, args))
    RT = op_ret(X, Val(op), K, Val(N))
    # at the erased key (a `Dynamic` trait object): the call-site split over the held object
    getfield(v, :w) isa ErasedWit && return _erased_op(X, f, RT, v, args...)
    x = _dispatch(X, Val(op), f, getfield(v, :w), _rep(v), t, args...)
    return x::RT
end

# A default receives the whole trait object, with its supertraits' views, so it
# may call their operations too (`lastel(r) = r[length(r)]` with `length` from HasLength).
@inline function _dispatch(::Type{X}, ::Val{op}, f::F, w::Impl{D}, r, t, args...) where {X,op,F,D}
    Base.sym_in(op, D) && return op_default(X, Val(op), t, args...)
    return f(r, args...)
end
@inline function _dispatch(::Type{X}, ::Val{op}, f::F, w::Generic{X,k,S,D}, r, t, args...) where {X,op,F,k,S,D}
    Base.sym_in(op, D) && return op_default(X, Val(op), t, args...)
    return generic_op(X, Val(k), Val(op), _subobj(w.sub, r), args...)
end
@inline function _dispatch(::Type{X}, ::Val{op}, f::F, w::Dyn{NT,D}, r, t, args...) where {X,op,F,NT,D}
    Base.sym_in(op, fieldnames(NT)) && return getfield(w.table, op)(r, args...)
    return op_default(X, Val(op), t, args...)
end

@inline _subobj(sub::Tuple, r) = TObj(_subviews(r, sub...))
@inline _subviews(r) = ()
@inline _subviews(r, s::Wit{X}, rest...) where {X} = (_selfview(X, s.w, r), _subviews(r, rest...)...)

# --- Callable: erased function pointers and checked calls ------------------

"""
The pointer of an `Erased`, in a mutable cell: a package image resets a mutable struct's `Ptr`
fields to null (an immutable one's it saves as the old session's address, which crashes when
called), so a value kept in an image (`const D = Dynamic{Callable{A, S}}(f)`) finds null in a new session and
makes its pointer again, once. A load and a compare per call; compiled code cannot fold the
address in as a constant.
"""
mutable struct _PtrCell
    @atomic ptr::Ptr{Cvoid}
end
"""
    Erased{A, S}

A function from above, erased to a pointer to its code compiled for `A`
(the FunctionWrappers.jl technique). Library code compiled for an `Erased{A,
S}` serves every function with that signature; each call is indirect. The
result is asserted, never converted.
"""
struct Erased{A,S}
    cell::_PtrCell
    obj::Any
end
struct _CallWrap{S} end
# fixed arities: a varargs callee would not be specialized behind the pointer
(::_CallWrap{S})(o) where {S} = o()::S
(::_CallWrap{S})(o, a) where {S} = o(a)::S
(::_CallWrap{S})(o, a, b) where {S} = o(a, b)::S
(::_CallWrap{S})(o, a, b, c) where {S} = o(a, b, c)::S
(::_CallWrap{S})(o, a, b, c, d) where {S} = o(a, b, c, d)::S
(::_CallWrap{S})(o, a, b, c, d, e) where {S} = o(a, b, c, d, e)::S
(::_CallWrap{S})(o, a, b, c, d, e, f) where {S} = o(a, b, c, d, e, f)::S
# The callee side declares concrete types (`Ref{T}` for non-bits values), so
# the call inside is static; the caller passes non-bits values as boxes
# (`Any`): the same pointer, without allocating a `RefValue`.
# (a zero-size type, `Nothing`, is no C type: it goes as a reference too)
_ctype(@nospecialize(T)) = isbitstype(T) && sizeof(T) > 0 ? T : Any
# (an abstract type is `Any` on both sides: `Ref{T}` there would mean a pointer to a slot holding the value)
_cdecl(@nospecialize(T)) = isbitstype(T) && sizeof(T) > 0 ? T : isconcretetype(T) ? Ref{T} : Any
# The calling convention `:caller_world` (a patch of the compiler): the call runs in the caller's
# world, as a direct call does; the pointer's thunk is a world-checked call-site cache. (A plain
# `@cfunction` runs in the latest world, as a callback from C must.)
@generated function _fptr(::Type{A}, ::Type{S}, ::Type{F}) where {A,S,F}
    ats = Any[_cdecl(a) for a in (A::DataType).parameters]
    return Expr(:cfunction, Ptr{Cvoid}, QuoteNode(_CallWrap{S}()), _ctype(S),
                :(Core.svec($(Ref{F}), $(ats...))), QuoteNode(:caller_world))
end
"`f` erased to `Callable{A, S}`, not specialized on `f`: its pointer is made at the first call, so a function kept and never called compiles nothing."
Erased{A,S}(@nospecialize(f)) where {A,S} = Erased{A,S}(_PtrCell(C_NULL), f)
"The pointer of `e` in this session: made at its first call, and again after an image load reset it."
@noinline function _erased_ptr_slow(e::Erased{A,S}) where {A,S}
    p = Base.invokelatest(_fptr, A, S, typeof(getfield(e, :obj)))::Ptr{Cvoid}
    @atomic getfield(e, :cell).ptr = p
    return p
end
@generated function (e::Erased{A,S})(args...) where {A,S}
    aps = (A::DataType).parameters
    length(aps) <= 6 || return :(error("Erased: at most 6 arguments"))
    ats = Any[_ctype(a) for a in aps]
    argex = [:(args[$i]) for i in 1:length(ats)]
    return quote
        Base.@_inline_meta
        p = @atomic :monotonic getfield(e, :cell).ptr
        p == C_NULL && (p = _erased_ptr_slow(e))
        x = ccall(p, $(_ctype(S)), (Any, $(ats...)), e.obj, $(argex...))
        x::$S
    end
end

"""
    CObj{A, S, F}

A function inside library code, bounded by `Callable{A, S}`: the function
itself (`F` its type: specialized, the call inlined) or an `Erased{A, S}`.
Calling it checks the arguments against `A` and asserts the result to `S`.
"""
struct CObj{A,S,F}
    f::F
end
CObj{A,S}(f::F) where {A,S,F} = CObj{A,S,F}(f)
@inline function (c::CObj{A,S})(args...) where {A,S}
    args isa A || throw(MethodError(c.f, args))
    return c.f(args...)::S
end

# a function inside library code prints as its bound and how it is called (a type printer,
# registered in `__init__`: see `_register_type_printers`)
function _show_cobj_type(io::IO, @nospecialize(T))
    T isa DataType && length(T.parameters) == 3 && T.parameters[3] isa Type ||
        return _show_type_plain(io, T)
    A, S, F = T.parameters
    print(io, "Callable{")
    show(io, A); print(io, ", "); show(io, S)
    print(io, "} at ")
    F <: Erased ? print(io, "Dynamic") : show(io, F)
end

"""
    CMulti{C}

A function argument bounded by several `Callable`s, one per signature it is
called at: a tuple of `CObj`. A call picks the signature its arguments match.
"""
struct CMulti{C<:Tuple}
    cs::C
end
@generated function (m::CMulti{C})(args...) where {C}
    for (i, c) in enumerate(C.parameters)
        A = c.parameters[1]
        Tuple{args...} <: A && return :(m.cs[$i](args...))
    end
    return :(throw(MethodError(m, args)))
end
