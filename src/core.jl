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
    Callable{A, S}

The built-in trait for a function argument: called with arguments of the tuple
type `A`, it returns an `S`. Any callable conforms; every call is checked.
"""
abstract type Callable{A<:Tuple,S} end

"One trait's view of a value: the witness `w` that says where its operations come from, and the representation `r`."
struct View{X,W,R}
    w::W
    r::R
end
View{X}(w::W, r::R) where {X,W,R} = View{X,W,R}(w, r)

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

@inline viewof(t::TObj, ::Type{X}) where {X} = _viewof(X, t.views...)
@inline _viewof(::Type{X}, v::View{X}, rest::View...) where {X} = v
@inline _viewof(::Type{X}, v::View, rest::View...) where {X} = _viewof(X, rest...)

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
is_trait(@nospecialize(X)) = X isa Type && X <: Trait

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
    R = typeof(v.r)
    args isa op_args(X, Val(op), R, Val(N)) || throw(TraitArgumentError(X, op, R, args))
    x = _dispatch(X, Val(op), f, v.w, v.r, t, args...)
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
