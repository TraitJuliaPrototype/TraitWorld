# ---------------------------------------------------------------------------
# `Compiled` and `Dynamic` (traits reference §6.6; lowering §5, §8.2, §13).
#
# Every value in trait code is `Compiled` or `Dynamic`. The attribute is the trait object's
# representation: a `Compiled` value is a trait object at its key, a `Dynamic` one a trait object at
# the erased key (`ErasedKey`), whose views hold the user's object and whose operations and field
# reads are split over the candidates at the call site. One worker per bounded function serves both:
# the erased key is one more key. A value keeps its attribute by its type; only an entry decides,
# for a plain value: the position's attribute, else the traits' default (`@dynamic`, for a value
# whose type is not of the trait world), else `Compiler.known_type`, evaluated in the entry's own
# body (E-148). `compiled_for(x)` and `with_dynamic(x)` always win.
# ---------------------------------------------------------------------------

"""
    Compiled{X}

An attribute on a bound, `x::Compiled{X}`: a plain value entering there is `Compiled`, compiled for
its key, whatever its caller knew of its type. Never the type of a value.
"""
abstract type Compiled{X} end

"""
    ErasedKey{P, Y}

The key of a `Dynamic` trait object: the trait's parameter values `P` (a tuple type, in order),
and nothing of the user's type. A worker is compiled once per erased key. `Y` is the item trait of
a container view whose items of an abstract type are read at their own keys (BaseTraits'
`CompiledItems{Y}`), else `Nothing`: its trait set keeps saying how its items are seen.
"""
struct ErasedKey{P,Y} end
"What `Self` names at an erased key: the receiver's type is not known there."
struct ErasedSelf end
_impl(::Type{ErasedKey{P,Y}}) where {P,Y} = ErasedSelf
"Parameter `i` of a trait at an erased key (`param` methods added by `@trait`)."
_erasedparam(::Type{ErasedKey{P,Y}}, i::Int) where {P,Y} = fieldtype(P, i)
"""
The witness of a view at the erased key: an operation, or a field read, is split over the
candidate types at the call site, on the user's object the view holds.
"""
struct ErasedWit end

"The view type of trait instance `Xi`'s view at the erased key."
function _erased_view_type(@nospecialize(Xi))
    u = Base.unwrap_unionall(Xi)::DataType
    ps = u.parameters
    n = length(ps)::Int
    vals = Any[ps[i] for i in 1:n-1]
    Yc = _compiled_view_item(ps[n])
    E = ErasedKey{Tuple{vals...},Yc === nothing ? Nothing : Yc}
    Xe = Core.apply_type(u.name.wrapper, vals..., E)
    return View{Xe,ErasedWit,E,0,Tuple{}}
end
"Whether a view type is at the erased key."
_is_erased_view(@nospecialize(V)) = V isa DataType && V <: AbstractView && (V::DataType).parameters[2] === ErasedWit

"""
    _erase(t, o)

The `Dynamic` trait object of trait object `t`: each view at its erased key, holding `o`, the
user's object (or `t` itself where its views hold only parts of an immutable value).
"""
@generated function _erase(t::TObj{T,V}, o) where {T,V}
    views = Any[]
    for Vt in (V::DataType).parameters
        push!(views, _is_erased_view(Vt) ? Vt : _erased_view_type((Vt::DataType).parameters[1]))
    end
    TT = TObj{_encode_traits(Any[(v::DataType).parameters[1] for v in views]),Tuple{views...}}
    return :($TT(($([:($VT(ErasedWit(), o, SELF, (), ())) for VT in views]...),)))
end
"Whether a trait object is `Dynamic`: its views are at the erased key."
@generated _is_erased(::Type{V}) where {V<:Tuple} = all(_is_erased_view, (V::DataType).parameters)
is_dynamic(t::TObj{T,V}) where {T,V} = _is_erased(V)
"The object a trait object's views read, or the trait object itself where they hold only parts."
@inline function _held_object(t::TObj)
    o = _tobj_object(t)
    return o === nothing ? t : o
end
"The views of trait object type `V`'s traits, as a `TraitList` of their families."
@generated function _traits_of(::Type{V}) where {V<:Tuple}
    fams = Any[]
    for Vt in (V::DataType).parameters
        F = _family((Vt::DataType).parameters[1])
        any(x -> x === F, fams) || push!(fams, F)
    end
    return :(TraitList{Tuple{$(fams...)}}())
end

# --- operations and fields at the erased key ------------------------------------

@inline _rep(v::View{X,ErasedWit}) where {X} = getfield(v, :o)

"""
An operation at the erased key: the operation on a `Dynamic` of the held object (the call-site split
over the candidates, `trait.jl`), its result asserted to the declared type at the erased key, which
carries the trait's parameters. An operation whose result is `Self` gives a `Dynamic` of the new value.
"""
@inline function _erased_op(::Type{X}, f::F, ::Type{RT}, v, args...) where {X,F,RT}
    # an invoke at the constructor's own signature: a fact, so it is inlined and the call stays typed
    # (a call with the `Any`-typed object would be a run-time site of code compiled by facts)
    d = invoke(Dynamic{X}, Tuple{Val{:checked},Any}, Val(:checked), getfield(v, :o))::Dynamic{X}
    RT === ErasedSelf && return f(d, args...)
    return f(d, args...)::RT
end

"A declared field read on a held object of unknown type: the field on its trait object."
struct _DynField{X,f} end
@inline (::_DynField{X,f})(o) where {X,f} = getproperty(_Open{X}()(o), f)
"A declared field written on a held object of unknown type."
struct _DynFieldSet{X,f} end
@inline (::_DynFieldSet{X,f})(o, y) where {X,f} = (setproperty!(_Open{X}()(o), f, y); nothing)   # a `@const` field raises
"""
A parameter a `Dynamic{X}` leaves open (`Dynamic{IntegratorView}` for `IntegratorView{T, P}`), at its
erased key: a type no value has, so that a type naming it (`Vector{OpenParam}`) is known to be unknown.
"""
struct OpenParam end
"Whether `T` names `OpenParam` anywhere."
_has_open(@nospecialize(T)) = T === OpenParam || (T isa DataType && any(_has_open, T.parameters)) ||
    (T isa Union && (_has_open(T.a) || _has_open(T.b)))
"""
A declared field's type at the erased key: `Any` where it is declared with the receiver type (`Self`),
or names a parameter a `Dynamic{X}` leaves open, unknown there. A generator, so that it folds to a constant.
"""
@generated _erased_ft(::Type{T}) where {T} = (T === ErasedSelf || _has_open(T)) ? Any : T
@inline _fget(::Type{X}, ::Val{f}, w::ErasedWit, v, ::Type{K}) where {X,f,K} =
    CC.split_call(_family_of(X), _erased_ft(field_type(X, Val(f), K)), _DynField{X,f}(), getfield(v, :o))::_erased_ft(field_type(X, Val(f), K))

"""
The seams: an argument of an operation or of a `Callable` declared `Dynamic{Y}` that receives a
trait object gets a `Dynamic{Y}` of it (lowering §13). Every other argument passes as it is.
"""
@generated function _seams(::Type{AT}, args::Tuple) where {AT}
    asis = :(Base.@_inline_meta; args)          # inlined in every case: the arguments never go through a tuple
    AT isa DataType && AT <: Tuple || return asis
    ds = (AT::DataType).parameters
    as = (args::DataType).parameters
    length(ds) == length(as) || return asis
    any(i -> as[i] <: TObj && ds[i] isa DataType && ds[i] <: Dynamic, 1:length(as)) || return asis
    return quote
        Base.@_inline_meta          # inlined, so the caller's arguments are never stored in a tuple
        ($([as[i] <: TObj && ds[i] isa DataType && ds[i] <: Dynamic ? :($(ds[i])(args[$i])) : :(args[$i]) for i in 1:length(as)]...),)
    end
end

# --- the conversions: `compiled_for`, `with_dynamic` --------------------------------

"""
    compiled_for(x)

`x` as a `Compiled` value: at the next bound, the code compiled for its key runs, selected once by
its type when the call runs (a function barrier). On a `Dynamic` value or trait object it opens it.
Always wins over a position's attribute and a trait's default.
"""
compiled_for(x::T) where {T} = CompiledFor{T}(x)
compiled_for(d::Dynamic) = Base.inferencebarrier(opened)(d)
compiled_for(t::TObj{T,V}) where {T,V} = _is_erased(V) ? Base.inferencebarrier(_open_erased)(t) : t
"""
    with_dynamic(x)

`x` as a `Dynamic` value: at the next bound, the code compiled once for the position runs, and each
operation on it dispatches when it runs. Always wins over a position's attribute and a trait's default.
"""
with_dynamic(x) = WithDynamic(x)
with_dynamic(d::Dynamic) = d
with_dynamic(t::TObj) = _erase(t, _held_object(t))
"A value converted by `compiled_for`, until the next entry."
struct CompiledFor{T}
    x::T
end
"A value converted by `with_dynamic`, until the next entry."
struct WithDynamic
    x::Any
end
"The trait object at its own key of a `Dynamic` trait object's held object: what `compiled_for` opens it to."
function _open_erased(t::TObj{T,V}) where {T,V}
    o = getfield(getfield(t, :views)[1], :o)
    o isa TObj && return o
    v = _assemble(_traits_of(V), o)
    ismutable(o) || (v = _with_object(v, o))
    return v
end

# --- attributes: a position's, a trait's default ---------------------------------

Base.Experimental.@max_methods 1 function default_attribute end
"""
    default_attribute(X)

`:dynamic` for a trait that declares `@dynamic` (`Callable` does), else `:compiled`: how a plain value
whose type is not of the trait world enters a bound of `X` where neither the position nor the caller
says otherwise.
"""
default_attribute(@nospecialize(X)) = :compiled
"Whether any trait of a list declares `@dynamic`."
@inline _any_dynamic_default(::TraitList{L}) where {L} = _any_dyn(L)
@inline _any_dyn(::Type{Tuple{}}) = false
@inline _any_dyn(::Type{T}) where {T<:Tuple} = default_attribute(fieldtype(T, 1)) === :dynamic || _any_dyn(Base.tuple_type_tail(T))

Base.Experimental.@max_methods 1 function attribute end
"""
    attribute(EntryPos{F, pos, nargs}())

The attribute a bound at an entry position declares, `:compiled` or `:dynamic`, or `nothing` where none
does. A trait module defines a method per annotated position when it is complete (`_fix_attribute!`).
"""
attribute(::EntryPos) = nothing

"""
Whether a plain value `t` enters position `p` as `Dynamic`: the position's attribute, else the traits'
default for a value whose type is not of the trait world, else whether the caller did not know its
type (`kn`, evaluated in the entry's body).
"""
@inline function _enters_dynamic(p::EntryPos, t, ::Val{kn}) where {kn}
    a = attribute(p)
    a === :dynamic && return true
    a === :compiled && return false
    _any_dynamic_default(needed(p)) && !_from_trait_world(t) && return true
    return !kn
end

"""
Whether a value from a caller that does not know its type enters position `p` as `Compiled`:
converted by `compiled_for`, or a plain value at a position whose attribute is `Compiled`. The
table of declared implementations serves it (untyped.jl): one lookup by its type, then the code
compiled for its key (lowering §9.2).
"""
@inline _tabled(p::EntryPos, @nospecialize(t)) =
    t isa CompiledFor || (attribute(p) === :compiled && !(t isa Dynamic || t isa TObj || t isa WithDynamic))
"The plain value a `compiled_for` holds, or the value itself."
@inline _unconverted(@nospecialize(t)) = t isa CompiledFor ? getfield(t, :x) : t

Base.Experimental.@max_methods 1 function result_params end
"`result_params(X)`: the parameters of trait `X` that its operations' declared result types and its declared fields' types use (methods added by `@trait`)."
result_params(@nospecialize(X)) = ()

"""
A `Dynamic{X}` attribute must fix every parameter of `X` its operations' result types use, so that
code after an operation stays typed (traits reference §6.1; decision log, 2026-10-20): refused at the
definition otherwise.
"""
function _check_dynamic_params(@nospecialize(X), attr::Symbol, @nospecialize(name))
    attr === :dynamic || return nothing
    F = _family(X)
    ps = trait_params(F)
    isempty(ps) && return nothing
    u = Base.unwrap_unionall(X)
    u isa DataType || return nothing
    used = result_params(F)
    bad = Symbol[p for (i, p) in enumerate(ps) if (i > length(u.parameters) - 1 || u.parameters[i] isa TypeVar) && p in used]
    isempty(bad) && return nothing
    throw(TraitBoundError("argument `$name`: `Dynamic{$X}` leaves open the parameter(s) $(join(bad, ", ")) of $F, which " *
                          "the results of its operations use; fix them in the bound, or write the bound without `Dynamic`"))
end

"Whether a function argument inside library code is `Dynamic` (erased to a pointer) or `Compiled`."
is_dynamic(c::CObj{A,S,F}) where {A,S,F} = F <: Erased

"""
Rule 8 (traits reference §6.6): an attribute on a function that is neither exported nor declared
`public` warns at the trait module's end. No plain value crosses there, so it decides nothing; the
conversion at the call does (`compiled_for(x)`, `with_dynamic(x)`).
"""
function _warn_hidden_attributes(mod::Module)
    isdefined(mod, :__tw_attrs__) || return nothing
    seen = Base.IdSet{Any}()
    for (k, a) in mod.__tw_attrs__
        f = k[1]
        f in seen && continue
        push!(seen, f)
        f isa Function || continue
        m = parentmodule(f)
        Base.ispublic(m, nameof(f)) && continue
        @warn "`$(nameof(f))` has a `$(a === :dynamic ? "Dynamic" : "Compiled")` attribute on a bound, but it is neither " *
              "exported nor public in $m: no value from plain code enters there, so the attribute decides nothing. " *
              "Convert at the call instead: `compiled_for(x)`, `with_dynamic(x)`." _module = mod
    end
    return nothing
end

Base.Experimental.@max_methods 1 function is_operation_function end
"""
    is_operation_function(f)

Whether `f` is an operation's function (methods added by `@trait`). In its methods an argument
declared `Dynamic{X}` keeps the type's meaning (traits reference §3.1): those methods implement
operations, so they are not bounded functions.
"""
is_operation_function(@nospecialize(f)) = false
"Whether the function a definition names is an operation's function."
_is_operation_function(mod::Module, @nospecialize(fname)) = (f = _tryeval(mod, fname); f !== nothing && is_operation_function(f))
