"""
    BaseTraits

Traits for Base's concepts, loaded with TraitWorld: the trait world's standard library, as
Rust's `core::iter` and Swift's `Sequence` ship with their languages (traits reference §18,
"BaseTraits"). `using TraitWorld` brings its names into scope.

Version 0 has what heterogeneous collections need:
- `HasLength`, `Iterable{T}`, `Indexable{T}`, `MutableIndexable{T}`, `Resizable`, `Keyed{K, V}`:
  Base's iteration, indexing, mutation and keyed access, each with its item types as associated
  types. Base's own containers conform through Base's existing methods, declared here, for
  families through Base's abstract types: `AbstractArray`, `AbstractVector`, `Vector`,
  `AbstractDict`.
- `DynamicItems{X}(v)` and `DynamicValues{X}(d)`: a user's container seen with items
  `Dynamic{X}`, wrapping each element when it is read. No copy: reads and writes go to the
  user's container.
- `retain!(f, xs)`: keeps the items for which `f` is `true`, in place.

The owner of these traits is TraitWorld. As their owner it declares Base's types' conformance
(traits reference §12.1).
"""
@trait_module module BaseTraits
using ..TraitWorld
using ..TraitWorld: _dyn_object, @dynamic_of

export HasLength, Iterable, Indexable, MutableIndexable, Resizable, Keyed,
       DynamicItems, DynamicValues, retain!

# --- the traits ------------------------------------------------------------------------------

"A finite number of items: `length`."
@trait HasLength begin
    Base.length(c::HasLength)::Int
end

"""
    Iterable{T}

Base's iteration protocol, with the item type `T` as an associated type (`eltype`): a `for`
loop over a value bounded by `Iterable{T}` sees items of type `T`. Inside a trait module,
`Iterable{Shape}` means `Iterable{Dynamic{Shape}}`, as a trait's name in a container does.
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

# --- a user's container, its items seen as `Dynamic{X}` ------------------------------------------

"""
    DynamicItems{X}(v)

The vector `v`, its items seen as `Dynamic{X}`: each item is wrapped when it is read, and `v`
itself is read and written, never copied. An item that does not conform to `X` raises
`TraitBoundError` when it is read. Writing a `Dynamic{X}` stores the user's object it holds.
"""
struct DynamicItems{X, V <: AbstractVector}
    data::V
end
DynamicItems{X}(v::V) where {X, V <: AbstractVector} = DynamicItems{X, V}(v)
Base.eltype(::Type{DynamicItems{X, V}}) where {X, V} = Dynamic{X}
Base.parent(d::DynamicItems) = d.data
Base.length(d::DynamicItems) = length(d.data)
Base.size(d::DynamicItems) = size(d.data)
# The wrapping is written out at each read (`@dynamic_of`): a helper taking the item, typed `Any`,
# would be a run-time site of the trait module (facts §5), its result `Any`.
Base.@propagate_inbounds Base.getindex(d::DynamicItems{X}, i::Int) where {X} = @dynamic_of(X, d.data[i])
# The store is split over the object's candidate types, as an operation on it is: at a candidate's
# type, `setindex!` on the user's vector is a call at concrete types, not a run-time site.
Base.@propagate_inbounds function Base.setindex!(d::DynamicItems{X}, x::Dynamic{X}, i::Int) where {X}
    TraitWorld.CC.split_call(TraitWorld._family_of(X), Nothing, _store!, _dyn_object(x), d.data, i)
    return d
end
Base.@propagate_inbounds _store!(o, data, i::Int) = (data[i] = o; nothing)
@inline function Base.iterate(d::DynamicItems{X}, i::Int = 1) where {X}
    i > length(d.data) && return nothing
    return (@dynamic_of(X, @inbounds d.data[i]), i + 1)
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

The dictionary `d`, its values seen as `Dynamic{X}`: `Keyed{K, Dynamic{X}}`, and
`Iterable{Pair{K, Dynamic{X}}}`. Each value is wrapped when it is read; `d` is not copied.
"""
struct DynamicValues{X, D <: AbstractDict}
    data::D
end
DynamicValues{X}(d::D) where {X, D <: AbstractDict} = DynamicValues{X, D}(d)
Base.keytype(::Type{DynamicValues{X, D}}) where {X, D} = keytype(D)
Base.valtype(::Type{DynamicValues{X, D}}) where {X, D} = Dynamic{X}
Base.eltype(::Type{DynamicValues{X, D}}) where {X, D} = Pair{keytype(D), Dynamic{X}}
Base.parent(d::DynamicValues) = d.data
Base.length(d::DynamicValues) = length(d.data)
Base.getindex(d::DynamicValues{X}, k) where {X} = @dynamic_of(X, d.data[k])
Base.haskey(d::DynamicValues, k) = haskey(d.data, k)
# keys and values iterate in the same order (Base's `keys` and `values`): iterating both avoids the
# `Pair{K, Any}` that iterating a `Dict{K, Any}` itself builds at a run-time site
# (`getfield` on the iterators' results: indexing a `Tuple{Any, Int}` would be a run-time site)
@inline function Base.iterate(d::DynamicValues{X}) where {X}
    kr = iterate(keys(d.data)); vr = iterate(values(d.data))
    (kr === nothing || vr === nothing) && return nothing
    return (getfield(kr, 1) => @dynamic_of(X, getfield(vr, 1)), (getfield(kr, 2), getfield(vr, 2)))
end
@inline function Base.iterate(d::DynamicValues{X}, s) where {X}
    kr = iterate(keys(d.data), getfield(s, 1)); vr = iterate(values(d.data), getfield(s, 2))
    (kr === nothing || vr === nothing) && return nothing
    return (getfield(kr, 1) => @dynamic_of(X, getfield(vr, 1)), (getfield(kr, 2), getfield(vr, 2)))
end
Base.show(io::IO, d::DynamicValues{X}) where {X} = print(io, "DynamicValues{", X, "} of a ", typeof(d.data))

@implement HasLength D where {D <: DynamicValues}
@implement Iterable D where {D <: DynamicValues}
@implement Keyed D where {D <: DynamicValues}

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
