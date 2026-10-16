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

"""
    Callable{A, S, M}

The built-in trait for a function argument: called with arguments of the tuple
type `A`, it returns an `S`. Any callable conforms; every call is checked. `M`
is the mode the library sets as its default: `DynamicCall` (a pointer to the
function's code, the worker compiled once per signature) or `CompiledCall`
(a worker compiled per function type, outside the library's cache). A bound
without `M` accepts either and supplies `DynamicCall`; the caller overrides per
value with `compiled_call(f)` or `dynamic_call(f)`.
"""
abstract type CallMode end
struct DynamicCall <: CallMode end
struct CompiledCall <: CallMode end
abstract type Callable{A<:Tuple,S,M<:CallMode} end

"""
    compiled_call(f), dynamic_call(f), Callable{A, S, M}(f)

The caller's choice of mode for one value, which wins over the bound's default;
the entry strips the wrapper. The long form also fixes the signature, as
FunctionWrappers does.
"""
struct CallAs{M<:CallMode,A,S,F}
    f::F
end
compiled_call(f::F) where {F} = CallAs{CompiledCall,Nothing,Nothing,F}(f)
dynamic_call(f::F) where {F} = CallAs{DynamicCall,Nothing,Nothing,F}(f)
(::Type{Callable{A,S,M}})(f::F) where {A,S,M<:CallMode,F} = CallAs{M,A,S,F}(f)

"One trait's view of a value: the witness that says where its operations come from, and the representation."
abstract type AbstractView{X,W,R} end

"A view holding its representation: what an entry builds, and what a worker sees within a call."
struct View{X,W,R} <: AbstractView{X,W,R}
    w::W
    r::R
end
View{X}(w::W, r::R) where {X,W,R} = View{X,W,R}(w, r)

"""
A view of a field projection of a mutable user type: the representation held,
as in `View`, and the user's object and the field's index, so that a value kept
beyond the call can follow the field (note "Dynamic values": kept values follow
the user's fields).
"""
struct FieldView{X,W,R} <: AbstractView{X,W,R}
    w::W
    r::R
    o::Any
    i::Int
end
FieldView{X}(w::W, r::R, o, i::Int) where {X,W,R} = FieldView{X,W,R}(w, r, o, i)

"""
A live view, a lens: the representation read from the user's field at every
use, and written there. Made for a trait that declares its projection field
writable, and for a kept field projection.
"""
struct LiveView{X,W,R} <: AbstractView{X,W,R}
    w::W
    o::Any
    i::Int
end

"The representation a view stands for: held, or read through the lens."
@inline _rep(v::View) = getfield(v, :r)
@inline _rep(v::FieldView) = getfield(v, :r)
@inline _rep(v::LiveView{X,W,R}) where {X,W,R} = getfield(getfield(v, :o), getfield(v, :i))::R
_reptype(::Type{<:AbstractView{X,W,R}}) where {X,W,R} = R
"Write the representation through a lens: the user's field is rebound, as `t.data = v` in plain Julia."
@inline _setrep!(v::LiveView{X,W,R}, x) where {X,W,R} = (setfield!(getfield(v, :o), getfield(v, :i), x::R); nothing)
_setrep!(v::AbstractView, x) = Base.inferencebarrier(_notlens)(typeof(v))
@noinline _notlens(@nospecialize(V)) =
    throw(ArgumentError("this trait object holds its representation, so its projection field cannot be rebound ($V)"))

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
@generated function _traitset(::Type{V}) where {V<:Tuple}
    return Union{Any[p.parameters[1] for p in V.parameters]...}
end
@inline TObj(views::Tuple) = TObj{_traitset(typeof(views)),typeof(views)}(views)

@inline viewof(t::TObj, ::Type{X}) where {X} = _viewof(X, getfield(t, :views)...)
# a view carries a trait instance (`ArrayLike{Float64, 1, Vector{Float64}}`); `X` is the trait family
@inline _viewof(::Type{X}, v::AbstractView{Y}, rest::AbstractView...) where {X,Y} = Y <: X ? v : _viewof(X, rest...)

# --- trait parameters: associated types (note "Declaring a trait": Parameters) ------------

"The trait family of a trait instance (`ArrayLike{Float64, 1, Vector{Float64}}` gives `ArrayLike`), or `X` itself."
_family(@nospecialize(X)) = (u = Base.unwrap_unionall(X); u isa DataType && u <: Trait ? u.name.wrapper : X)
"`trait_params(X)`: the names of trait `X`'s parameters besides the representation, in order."
trait_params(@nospecialize(X)) = ()
"""
`param(X, Val(p), R)`: parameter `p` of trait `X` at representation `R`, an
associated type: one value per conformance, defined by the trait's equation
(`T = eltype(R)`) or by the conformance (`@implement ArrayLike{Float64, 1} MyVector`).
"""
function param end
"`param_bound(X, Val(p))`: the bound a trait declares on its parameter `p` (`T <: NumberLike`)."
function param_bound end
"The trait instance a view of representation `R` carries: `X` with its parameters at `R`, the representation last."
function _instance(@nospecialize(X), @nospecialize(R))
    ps = trait_params(X)
    isempty(ps) && return X{R}
    return Core.apply_type(X, Any[param(X, Val(p), R) for p in ps]..., R)
end
"Whether a trait object carrying the traits `T` (a union of instances) carries `X`, a family or a partly applied instance."
_carries(@nospecialize(T), @nospecialize(X)) = any(Y -> Y <: X, Base.uniontypes(T))

# --- dynamic values ----------------------------------------------------------

"""
    Dynamic{X}

A value of any type conforming to trait `X`, kept beyond a call and reached
through `X`'s operations (note "Dynamic values"). It keeps a trait object of
`X`: made from one inside a trait module, `Dynamic{X}(t)`, or by storing one
where a `Dynamic{X}` is declared, so its type decides it. An operation of `X`
on it dispatches on the trait object inside and asserts the declared result
type; passed to a function bounded by `X`, it is opened, and the worker for
its representation runs.
"""
struct Dynamic{X}
    t::Any
    function Dynamic{X}(t::TObj{T}) where {X,T}
        _carries(T, X) || Base.inferencebarrier(_dyn_refuse)(X, T)
        return new{X}(_kept(t))
    end
end
Dynamic{X}(d::Dynamic{X}) where {X} = d
Base.convert(::Type{Dynamic{X}}, t::TObj) where {X} = Dynamic{X}(t)
@noinline _dyn_refuse(@nospecialize(X), @nospecialize(T)) =
    throw(ArgumentError("a trait object carrying $(join(string.(Base.uniontypes(T)), ", ")) cannot be kept as a Dynamic{$X}"))
"The trait object a dynamic value keeps: what a bound opens."
@inline opened(d::Dynamic) = getfield(d, :t)
# equal when they keep the same trait object: same representation type, same implementation, egal data
Base.:(==)(a::Dynamic{X}, b::Dynamic{X}) where {X} = getfield(a, :t) === getfield(b, :t)
Base.hash(d::Dynamic, h::UInt) = hash(getfield(d, :t), hash(:TraitWorldDynamic, h))
Base.show(io::IO, d::Dynamic{X}) where {X} = print(io, "Dynamic{", X, "} at ", _represented(typeof(getfield(d, :t))))
_represented(@nospecialize(T)) = T <: TObj ? join(unique([string(v.parameters[3]) for v in T.parameters[2].parameters]), ", ") : string(T)
@inline _dyn_assert(x, ::Type{S}) where {S} = x::S
# keeping a trait object: a field projection of a mutable user type is kept as a lens
@inline _kept(t::TObj) = TObj(map(_keepview, getfield(t, :views)))
@inline _keepview(v::FieldView{X,W,R}) where {X,W,R} = LiveView{X,W,R}(getfield(v, :w), getfield(v, :o), getfield(v, :i))
@inline _keepview(v::AbstractView) = v

# --- fields: properties a trait declares --------------------------------------

"`trait_fields(X)`: the fields trait `X` declares, as `(name, writable)` pairs."
trait_fields(@nospecialize(X)) = ()
"`field_type(X, Val(f), R)`: the declared type of field `f` at representation `R`."
function field_type end
"`field_isrep(X, Val(f))`: whether field `f` has the type `R`: it names the projection."
field_isrep(@nospecialize(X), @nospecialize(f)) = false

# `t.f` on a trait object: a field one of its traits declares (methods added by @trait), else an error
@inline Base.getproperty(t::TObj, s::Symbol) = _tgetprop(t, Val(s))
@inline Base.setproperty!(t::TObj, s::Symbol, x) = _tsetprop!(t, Val(s), x)
@noinline _tgetprop(t::TObj, ::Val{s}) where {s} = Base.inferencebarrier(_nofield)(typeof(t), s)
@noinline _tsetprop!(t::TObj, ::Val{s}, x) where {s} = Base.inferencebarrier(_nofield)(typeof(t), s)
@noinline _nofield(@nospecialize(T), s::Symbol) =
    throw(ArgumentError("`t.$s`: no trait this trait object carries declares a field `$s`"))
@noinline _readonly(@nospecialize(X), s::Symbol) = throw(ArgumentError("field `$s` of $X is `const`: read-only"))
Base.getproperty(d::Dynamic, s::Symbol) = getproperty(getfield(d, :t), s)
Base.setproperty!(d::Dynamic, s::Symbol, x) = setproperty!(getfield(d, :t), s, x)

"A field `f` of trait `X` read on a trait object: the representation itself for the projection field, else its property."
@inline function fieldget(::Type{X}, ::Val{f}, t::TObj) where {X,f}
    v = viewof(t, X)
    return _fget(X, Val(f), getfield(v, :w), v, _reptype(typeof(v)))
end
@inline _fget(::Type{X}, ::Val{f}, w, v, ::Type{R}) where {X,f,R} =
    (field_isrep(X, Val(f)) ? _rep(v) : getproperty(_rep(v), f))::field_type(X, Val(f), R)
"A field `f` of trait `X` written on a trait object: the projection field through the lens, else the representation's property."
@inline function fieldset!(::Type{X}, ::Val{f}, t::TObj, x) where {X,f}
    v = viewof(t, X)
    y = x::field_type(X, Val(f), _reptype(typeof(v)))
    field_isrep(X, Val(f)) ? _setrep!(v, y) : setproperty!(_rep(v), f, y)
    return y
end

# --- witnesses -------------------------------------------------------------

"The representation's own methods implement the trait; `D` lists the operations served by the trait's defaults."
struct Impl{D} end
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

"`trait_ops(X)`: the operation names of trait `X`, in declaration order."
function trait_ops end
"`op_function(X, Val(op))`: the function an operation is."
function op_function end
"`op_ret(X, Val(op), R, Val(N))`: the declared result type at representation `R`, for `N` arguments after `r`."
function op_ret end
"`op_args(X, Val(op), R, Val(N))`: the declared types of the arguments after `r`, as a tuple type."
function op_args end
"`op_default(X, Val(op), t, args...)`: the trait's default for an operation, with `t` a trait object."
function op_default end
"`generic_op(X, Val(k), Val(op), t, args...)`: generic implementation `k` of an operation."
function generic_op end
"`generic_rec(X, Val(k))`: the constraints of generic implementation `k` of trait `X` (one method per implementation)."
function generic_rec end
has_default(@nospecialize(X), @nospecialize(op)) = false
is_mutating(@nospecialize(X), @nospecialize(op)) = false
"`supertraits(X)`: traits whose operations `X` includes; their views travel with every `X` view."
supertraits(@nospecialize(X)) = ()
"`bundle(X)`: for a bundle trait, the traits it names; `t::Table` means `t::(ColTable, RowTable)`."
bundle(@nospecialize(X)) = nothing
"`is_trait(X)`: whether `X` was declared with `@trait`."
is_trait(@nospecialize(X)) = X isa Type && X !== Union{} && X <: Trait

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
@inline function opcall(::Type{X}, ::Val{op}, f::F, t::TObj, args::Vararg{Any,N}) where {X,op,F,N}
    v = viewof(t, X)
    R = _reptype(typeof(v))
    args isa op_args(X, Val(op), R, Val(N)) || throw(TraitArgumentError(X, op, R, args))
    x = _dispatch(X, Val(op), f, getfield(v, :w), _rep(v), t, args...)
    return x::op_ret(X, Val(op), R, Val(N))
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
@inline _subviews(r, s::Wit{X}, rest...) where {X} = (View{X}(s.w, r), _subviews(r, rest...)...)

# --- Callable: erased function pointers and checked calls ------------------

"""
    Erased{A, S}

A function from above, erased to a pointer to its code compiled for `A`
(the FunctionWrappers.jl technique). Library code compiled for an `Erased{A,
S}` serves every function with that signature; each call is indirect. The
result is asserted, never converted.
"""
struct Erased{A,S}
    ptr::Ptr{Cvoid}
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
_ctype(@nospecialize(T)) = isbitstype(T) ? T : Any
_cdecl(@nospecialize(T)) = isbitstype(T) ? T : Ref{T}
@generated function _fptr(::Type{A}, ::Type{S}, ::Type{F}) where {A,S,F}
    ats = map(_cdecl, A.parameters)
    return :(@cfunction($(_CallWrap{S}()), $(_ctype(S)), ($(Ref{F}), $(ats...))))
end
Erased{A,S}(f::F) where {A,S,F} = Erased{A,S}(_fptr(A, S, F), f)
@generated function (e::Erased{A,S})(args...) where {A,S}
    length(A.parameters) <= 6 || return :(error("Erased: at most 6 arguments"))
    ats = map(_ctype, A.parameters)
    argex = [:(args[$i]) for i in 1:length(ats)]
    return quote
        Base.@_inline_meta
        x = ccall(e.ptr, $(_ctype(S)), (Any, $(ats...)), e.obj, $(argex...))
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
