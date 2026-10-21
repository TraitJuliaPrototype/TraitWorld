"""
    BaseTraits

Traits for Base's concepts, loaded with TraitWorld: the trait world's standard library, as
Rust's `core::iter` and Swift's `Sequence` ship with their languages (traits reference
§10.1–10.4). `using TraitWorld` brings its names into scope.

Version 0 has what heterogeneous collections need:
- `HasLength`, `Iterable{T}`, `Indexable{T}`, `MutableIndexable{T}`, `Resizable`, `Keyed{K, V}`:
  Base's iteration, indexing, mutation and keyed access, each with its item types as associated
  types. Base's own containers conform through Base's existing methods, declared here, for
  families through Base's abstract types: `AbstractArray`, `AbstractVector`, `Vector`,
  `AbstractDict`.
- A function bounded by `Iterable{Shape}` and the like takes a user's container whose items are
  not kept values of `Shape` directly: its entry translates it into a view, `DynamicItems{X}(v)`,
  `CompiledItems{X}(v)`, `DynamicValues{X}(d)` or `CompiledValues{X}(d)`, which sees each item
  through the trait when it is read. An item that carries its attribute keeps it. No copy: reads
  and writes go to the user's container. The views can also be made explicitly.
- `retain!(f, xs)`: keeps the items for which `f` is `true`, in place.

The owner of these traits is TraitWorld. As their owner it declares Base's types' conformance
(traits reference §10.1).
"""
@trait_module module BaseTraits
using ..TraitWorld
using ..TraitWorld: _dyn_object, @dynamic_of, @kept_of, TObj, Kept, compiled_for, with_dynamic

export HasLength, Iterable, Indexable, MutableIndexable, Resizable, Keyed,
       DynamicItems, DynamicValues, CompiledItems, CompiledValues, retain!

# --- the traits ------------------------------------------------------------------------------

"A finite number of items: `length`."
@trait HasLength begin
    Base.length(c::HasLength)::Int
end

"""
    Iterable{T}

Base's iteration protocol, with the item type `T` as an associated type (`eltype`): a `for`
loop over a value bounded by `Iterable{T}` sees items of type `T`. Inside a trait module,
`Iterable{Shape}` names an item position: items seen through `Shape`, each `Compiled` or `Dynamic`.
"""
@trait Iterable{T} begin
    T = eltype(Self)
    Base.iterate(c::Iterable)::Union{Nothing, Tuple{T, Any}}
    Base.iterate(c::Iterable, state)::Union{Nothing, Tuple{T, Any}}
end

"Reading by position, `1:length(c)`: `c[i]` is a `T`."
@trait Indexable{T} <: HasLength begin
    T = eltype(Self)
    Base.getindex(c::Indexable, i::Int)::T
end

"Writing by position: `c[i] = x` for an `x` of the item type."
@trait MutableIndexable{T} <: Indexable begin
    T = eltype(Self)
    Base.setindex!(c::MutableIndexable, x::T, i::Int)::Any
end

"Changing the number of items: `resize!`."
@trait Resizable <: HasLength begin
    Base.resize!(c::Resizable, n::Int)::Any
end

"""
    Keyed{K, V}

Reading by key: `d[k]` is a `V`, `haskey(d, k)`. Its pairs are iterated through `Iterable`:
a `Dict{String, Int}` is `Iterable{Pair{String, Int}}`.
"""
@trait Keyed{K, V} <: HasLength begin
    K = keytype(Self)
    V = valtype(Self)
    Base.getindex(d::Keyed, k::K)::V
    Base.haskey(d::Keyed, k::K)::Bool
end

# --- Base's containers, by Base's own methods --------------------------------------------------

@implement HasLength A where {A <: AbstractArray}
@implement HasLength D where {D <: AbstractDict}
@implement Iterable A where {A <: AbstractArray}
@implement Iterable D where {D <: AbstractDict}
@implement Indexable A where {A <: AbstractVector}
@implement MutableIndexable A where {A <: Vector}
@implement Resizable A where {A <: Vector}
@implement Keyed D where {D <: AbstractDict}

# --- a user's container, its items seen through a trait ------------------------------------------
#
# Items of an abstract type are read as `Kept{X}`: each keeps the attribute it carries (a `Kept{X}`,
# `Compiled{X}`, `Dynamic{X}`, `compiled_for(x)`, `with_dynamic(x)`), and a plain item is first seen
# there, `Dynamic` in `DynamicItems`, `Compiled` in `CompiledItems` (traits reference §8.3). A write
# stores what reads back as the same value with the same attribute, in plain code's own forms: the
# user's object where a plain item of the view reads so, else `compiled_for(o)` or `with_dynamic(o)`;
# a container that can hold neither refuses it (types never cast).

"""
The value to store for `x` into a user's container of items `E`, whose plain items the view reads with
attribute `plain_compiled`: the user's object, or plain code's cast of it.
"""
@inline function _written(::Type{E}, plain_compiled::Bool, x) where {E}
    o = _dyn_object(x)
    TraitWorld._held_compiled(x) === plain_compiled && return o
    w = plain_compiled ? with_dynamic(o) : compiled_for(o)
    w isa E || Base.inferencebarrier(_unwritable)(E, x)
    return w
end
@noinline _unwritable(@nospecialize(E), @nospecialize(x)) =
    throw(TraitBoundError("a $(TraitWorld._held_compiled(x) ? "Compiled" : "Dynamic") value cannot be written to a container of $E, " *
                          "whose plain items are read with the other attribute: types never cast; cast it with " *
                          (TraitWorld._held_compiled(x) ? "`with_dynamic`" : "`compiled_for`")))

"""
    DynamicItems{X}(v)

The vector `v`, its items seen through `X`, each a `Kept{X}`: an item that carries its attribute keeps
it, a plain item is `Dynamic`. Each item is seen when it is read, and `v` itself is read and written,
never copied. An item that does not conform to `X` raises `TraitBoundError` when it is read.
"""
struct DynamicItems{X, V <: AbstractVector}
    data::V
end
DynamicItems{X}(v::V) where {X, V <: AbstractVector} = DynamicItems{X, V}(v)
Base.eltype(::Type{DynamicItems{X, V}}) where {X, V} = Kept{X}
Base.parent(d::DynamicItems) = d.data
Base.length(d::DynamicItems) = length(d.data)
Base.size(d::DynamicItems) = size(d.data)
# The wrapping is written out at each read (`@kept_of`): a helper taking the item, typed `Any`,
# would be a run-time site of the trait module (facts §5), its result `Any`.
Base.@propagate_inbounds Base.getindex(d::DynamicItems{X}, i::Int) where {X} = @kept_of(X, d.data[i], :dynamic)
# The store is split over the object's candidate types, as an operation on it is: at a candidate's
# type, `setindex!` on the user's vector is a call at concrete types, not a run-time site.
Base.@propagate_inbounds function Base.setindex!(d::DynamicItems{X, V}, x::TraitWorld.HeldValue{X}, i::Int) where {X, V}
    if TraitWorld._held_compiled(x)
        d.data[i] = _written(eltype(V), false, x)
    else
        TraitWorld.CC.split_call(TraitWorld._family_of(X), Nothing, _store!, _dyn_object(x), d.data, i)
    end
    return d
end
Base.@propagate_inbounds _store!(o, data, i::Int) = (data[i] = o; nothing)
@inline function Base.iterate(d::DynamicItems{X}, i::Int = 1) where {X}
    i > length(d.data) && return nothing
    return (@kept_of(X, @inbounds(d.data[i]), :dynamic), i + 1)
end
Base.resize!(d::DynamicItems, n::Int) = (resize!(d.data, n); d)
Base.show(io::IO, d::DynamicItems{X}) where {X} = print(io, "DynamicItems{", X, "} of a ", typeof(d.data))

@implement HasLength D where {D <: DynamicItems}
@implement Iterable D where {D <: DynamicItems}
@implement Indexable D where {D <: DynamicItems}
@implement MutableIndexable D where {D <: DynamicItems}
@implement Resizable D where {D <: DynamicItems{<:Any, <:Vector}}

"""
    DynamicValues{X}(d)

The dictionary `d`, its values seen through `X` as `DynamicItems` sees a vector's items, each a
`Kept{X}`: `Keyed{K, Kept{X}}`, and `Iterable{Pair{K, Kept{X}}}`. `d` is not copied.
"""
struct DynamicValues{X, D <: AbstractDict}
    data::D
end
DynamicValues{X}(d::D) where {X, D <: AbstractDict} = DynamicValues{X, D}(d)
Base.keytype(::Type{DynamicValues{X, D}}) where {X, D} = keytype(D)
Base.valtype(::Type{DynamicValues{X, D}}) where {X, D} = Kept{X}
Base.eltype(::Type{DynamicValues{X, D}}) where {X, D} = Pair{keytype(D), Kept{X}}
Base.parent(d::DynamicValues) = d.data
Base.length(d::DynamicValues) = length(d.data)
Base.getindex(d::DynamicValues{X}, k) where {X} = @kept_of(X, d.data[k], :dynamic)
Base.haskey(d::DynamicValues, k) = haskey(d.data, k)
# keys and values iterate in the same order (Base's `keys` and `values`): iterating both avoids the
# `Pair{K, Any}` that iterating a `Dict{K, Any}` itself builds at a run-time site
# (`getfield` on the iterators' results: indexing a `Tuple{Any, Int}` would be a run-time site)
@inline function Base.iterate(d::DynamicValues{X}) where {X}
    kr = iterate(keys(d.data)); vr = iterate(values(d.data))
    (kr === nothing || vr === nothing) && return nothing
    return (getfield(kr, 1) => @kept_of(X, getfield(vr, 1), :dynamic), (getfield(kr, 2), getfield(vr, 2)))
end
@inline function Base.iterate(d::DynamicValues{X}, s) where {X}
    kr = iterate(keys(d.data), getfield(s, 1)); vr = iterate(values(d.data), getfield(s, 2))
    (kr === nothing || vr === nothing) && return nothing
    return (getfield(kr, 1) => @kept_of(X, getfield(vr, 1), :dynamic), (getfield(kr, 2), getfield(vr, 2)))
end
Base.show(io::IO, d::DynamicValues{X}) where {X} = print(io, "DynamicValues{", X, "} of a ", typeof(d.data))

@implement HasLength D where {D <: DynamicValues}
@implement Iterable D where {D <: DynamicValues}
@implement Keyed D where {D <: DynamicValues}

# --- a user's container, its items seen as trait objects at their own keys --------------------------------

"""
    CompiledItems{X}(v)

The vector `v`, its items seen through `X` as `Compiled` values (traits reference §8.3). For a
concrete item type each item is read as its trait object at its own key, a type the code knows, and
the code over the items is compiled for it. For an abstract one each item is a `Kept{X}`: `Compiled`,
opened by its type at the next bound, unless it carries `Dynamic`. `v` is read and written, never
copied. An item that does not conform raises `TraitBoundError` when it is read.
"""
struct CompiledItems{X, V <: AbstractVector}
    data::V
end
CompiledItems{X}(v::V) where {X, V <: AbstractVector} = CompiledItems{X, V}(v)
"The type of an item of type `E` seen through `X` as `Compiled`: its trait object's type where `E` is concrete, else `Kept{X}`."
function _compiled_item_type(::Type{X}, ::Type{E}) where {X, E}
    if isconcretetype(E)
        T = Base.promote_op(_item_tobj, Type{X}, E)
        T isa DataType && T <: TObj && isconcretetype(T) && return T
        return Any
    end
    return Kept{X}
end
"The trait object of an item at its own key, or an error if it does not conform."
@inline function _item_tobj(::Type{X}, x) where {X}
    v = TraitWorld._assemble(TraitWorld._family_list(X), x)
    v === TraitWorld.NOTRAIT && TraitWorld._dyn_nonconforming(X, x)
    return v
end
Base.eltype(::Type{CompiledItems{X, V}}) where {X, V} = _compiled_item_type(X, eltype(V))
Base.parent(d::CompiledItems) = d.data
Base.length(d::CompiledItems) = length(d.data)
Base.size(d::CompiledItems) = size(d.data)
Base.@propagate_inbounds Base.getindex(d::CompiledItems{X, V}, i::Int) where {X, V} =
    isconcretetype(eltype(V)) ? _item_tobj(X, d.data[i]) : @kept_of(X, d.data[i], :compiled)
Base.@propagate_inbounds function Base.setindex!(d::CompiledItems{X, V}, x::TObj{T, W}, i::Int) where {X, V, T, W}
    TraitWorld._is_erased(W) && return setindex!(d, Kept{X}(x), i)
    d.data[i] = _object_of(x)
    return d
end
Base.@propagate_inbounds function Base.setindex!(d::CompiledItems{X, V}, x::TraitWorld.HeldValue{X}, i::Int) where {X, V}
    if TraitWorld._held_compiled(x)
        TraitWorld.CC.split_call(TraitWorld._family_of(X), Nothing, _store!, _dyn_object(x), d.data, i)
    else
        d.data[i] = _written(eltype(V), true, x)
    end
    return d
end
"The user's object a trait object reads, to store back into the user's container."
function _object_of(x::TObj)
    o = TraitWorld._tobj_object(x)
    o === nothing && throw(ArgumentError("this trait object holds the parts its trait sees, not the user's object, so it cannot be stored"))
    return o
end
@inline function Base.iterate(d::CompiledItems{X, V}, i::Int = 1) where {X, V}
    i > length(d.data) && return nothing
    return (isconcretetype(eltype(V)) ? _item_tobj(X, @inbounds(d.data[i])) : @kept_of(X, @inbounds(d.data[i]), :compiled), i + 1)
end
Base.resize!(d::CompiledItems, n::Int) = (resize!(d.data, n); d)
Base.show(io::IO, d::CompiledItems{X}) where {X} = print(io, "CompiledItems{", X, "} of a ", typeof(d.data))

@implement HasLength D where {D <: CompiledItems}
@implement Iterable D where {D <: CompiledItems}
@implement Indexable D where {D <: CompiledItems}
@implement MutableIndexable D where {D <: CompiledItems}
@implement Resizable D where {D <: CompiledItems{<:Any, <:Vector}}

"""
    CompiledValues{X}(d)

The dictionary `d`, its values seen through `X` as `Compiled` values, as `CompiledItems` sees a vector's
items: `Keyed{K, …}` and `Iterable{Pair{K, …}}`. `d` is not copied.
"""
struct CompiledValues{X, D <: AbstractDict}
    data::D
end
CompiledValues{X}(d::D) where {X, D <: AbstractDict} = CompiledValues{X, D}(d)
Base.keytype(::Type{CompiledValues{X, D}}) where {X, D} = keytype(D)
Base.valtype(::Type{CompiledValues{X, D}}) where {X, D} = _compiled_item_type(X, valtype(D))
Base.eltype(::Type{CompiledValues{X, D}}) where {X, D} = Pair{keytype(D), _compiled_item_type(X, valtype(D))}
Base.parent(d::CompiledValues) = d.data
Base.length(d::CompiledValues) = length(d.data)
Base.getindex(d::CompiledValues{X, D}, k) where {X, D} = isconcretetype(valtype(D)) ? _item_tobj(X, d.data[k]) : @kept_of(X, d.data[k], :compiled)
Base.haskey(d::CompiledValues, k) = haskey(d.data, k)
@inline function Base.iterate(d::CompiledValues{X, D}) where {X, D}
    kr = iterate(keys(d.data)); vr = iterate(values(d.data))
    (kr === nothing || vr === nothing) && return nothing
    return (isconcretetype(valtype(D)) ? getfield(kr, 1) => _item_tobj(X, getfield(vr, 1)) :
                getfield(kr, 1) => @kept_of(X, getfield(vr, 1), :compiled), (getfield(kr, 2), getfield(vr, 2)))
end
@inline function Base.iterate(d::CompiledValues{X, D}, s) where {X, D}
    kr = iterate(keys(d.data), getfield(s, 1)); vr = iterate(values(d.data), getfield(s, 2))
    (kr === nothing || vr === nothing) && return nothing
    return (isconcretetype(valtype(D)) ? getfield(kr, 1) => _item_tobj(X, getfield(vr, 1)) :
                getfield(kr, 1) => @kept_of(X, getfield(vr, 1), :compiled), (getfield(kr, 2), getfield(vr, 2)))
end
Base.show(io::IO, d::CompiledValues{X}) where {X} = print(io, "CompiledValues{", X, "} of a ", typeof(d.data))

@implement HasLength D where {D <: CompiledValues}
@implement Iterable D where {D <: CompiledValues}
@implement Keyed D where {D <: CompiledValues}

# --- the crossing: a user's container taken by a bound with dynamic items ------------------------------

# A function bounded by `Iterable{Shape}` (`Indexable`, `MutableIndexable`, `Keyed{K, Shape}`,
# `Iterable{Pair{K, Shape}}`) takes a user's vector or dictionary whose items are not `Dynamic{Shape}`:
# its entry translates it by its bound into the view (traits reference §8.3). Items of a type that
# cannot hold a conforming value refuse the container at the entry; otherwise a non-conforming item
# fails when it is read.
#
# Which view (traits reference §8.2's table): items of a concrete type that conforms are `Compiled`
# (`CompiledItems`), items of an abstract type `Dynamic` (`DynamicItems`), unless the bound's attribute
# says otherwise (`Iterable{Compiled{Shape}}`, `Iterable{Dynamic{Shape}}`), and only for items that do
# not carry an attribute. Items already kept values of `Y` (`Dynamic{Y}`, `Compiled{Y}`, both) meet the
# bound as they are (they carry their attribute).
TraitWorld.crossed(::Type{Y}, a::Symbol, v::AbstractVector) where {Y} = _cross_view(Y, a, eltype(v)) === :compiled ? CompiledItems{Y}(v) :
    _cross_view(Y, a, eltype(v)) === :dynamic ? DynamicItems{Y}(v) : nothing
TraitWorld.crossed(::Type{Y}, a::Symbol, d::AbstractDict) where {Y} = _cross_view(Y, a, valtype(d)) === :compiled ? CompiledValues{Y}(d) :
    _cross_view(Y, a, valtype(d)) === :dynamic ? DynamicValues{Y}(d) : nothing
"How items of type `E` cross into a bound of item trait `Y` with attribute `a`: `:compiled`, `:dynamic`, or `:no`."
@inline function _cross_view(::Type{Y}, a::Symbol, ::Type{E}) where {Y, E}
    E !== Union{} && E <: TraitWorld.HeldValue && return :no   # held values of `Y` meet as they are; another trait's do not cross
    _may_hold(Y, E) || return :no
    a === :dynamic && return :dynamic
    a === :compiled && return :compiled
    # no annotation: the item trait's default, else the first-seen rule (the item type the code knows)
    d = TraitWorld.default_attribute(TraitWorld._family_of(Y))
    d === :compiled && return :compiled
    d === :dynamic && !(isconcretetype(E) && Base.inferencebarrier(TraitWorld._type_from_trait_world)(E)::Bool) && return :dynamic
    return isconcretetype(E) ? :compiled : :dynamic
end
"""
Whether items declared `E` can be values that conform to `Y`: `Any`, an abstract type, a `Union`
with such a member, or a concrete type that conforms. Not a `Dynamic` of another trait. Kept per
pair and session once true (a flag), so a call pays a load.
"""
@inline _may_hold(::Type{Y}, ::Type{E}) where {Y,E} = E === Any || _hold_flag(Y, E)[] === TraitWorld._SESSION[] ||
    Base.inferencebarrier(_may_hold_slow)(Y, E, _hold_flag(Y, E))::Bool
@generated _hold_flag(::Type{Y}, ::Type{E}) where {Y,E} = :($(Ref{UInt}(0)))
function _may_hold_slow(@nospecialize(Y), @nospecialize(E), flag::Base.RefValue{UInt})
    ok = false
    for u in Base.uniontypes(E)
        if u isa DataType && u <: TraitWorld.HeldValue
            continue                                      # a kept value of another trait does not cross
        elseif !isconcretetype(u) || conforms(u, Y)
            ok = true
            break
        end
    end
    ok && (flag[] = TraitWorld._SESSION[])
    return ok
end

# --- algorithms ---------------------------------------------------------------------------------

"""
    retain!(f, xs)

Keep the items of `xs` for which `f(x)` is `true`, in order, and shorten `xs` (Rust's
`Vec::retain`, Swift's `removeAll(where:)` negated, Base's `filter!`). `f` is called with items
of `xs`'s item type and must return a `Bool`. Returns `nothing`.
"""
function retain!(f, xs::(MutableIndexable, Resizable))
    j = 1
    for i in 1:length(xs)
        x = xs[i]
        xs[j] = x
        j = ifelse(f(x)::Bool, j + 1, j)
    end
    resize!(xs, j - 1)
    return nothing
end

end
