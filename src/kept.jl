# Kept{X}: storage that holds a member of X with its attribute, in one concrete type (traits §7.8).
# It is no member of X: its type is the same under either attribute, so what a program asks of a
# stored item does not depend on who stored it.

"""
    Kept{X}(x)

A member of the trait `X` with the attribute it is kept with: `Compiled` for a member, `Dynamic` for a
`Dynamic{X}`, whose object it holds. A field or element typed `Kept{X}` converts what is assigned to
it, so `push!(v, keep(x))` stores the argument with its attribute. `unwrap(k)` is the object, `k[]`
the value with its attribute, `kept_call(f, k, args…)` the call under it.
"""
struct Kept{X}
    object::X
    dynamic::Bool
    function Kept{X}(@nospecialize(x)) where {X}
        X isa UnionAll && throw(ArgumentError("Kept{X} needs the trait's parameters"))
        istrait(X) || throw(ArgumentError("Kept{X}: $X is not a trait"))
        dyn = false
        if x isa Kept
            dyn = getfield(x, :dynamic); x = getfield(x, :object)
        elseif x isa Dynamic
            dyn = true; x = unwrap(x)
        end
        x isa X || throw(TypeError(:Kept, "", X, x))
        return new{X}(x, dyn)
    end
end

unwrap(k::Kept) = getfield(k, :object)
"Whether the value was kept with the attribute `Dynamic`."
isdynamic(k::Kept) = getfield(k, :dynamic)

Base.convert(::Type{Kept{X}}, k::Kept{X}) where {X} = k
Base.convert(::Type{Kept{X}}, @nospecialize(x)) where {X} = Kept{X}(x)
# No conversion of a `Kept{X}` into storage typed by the trait: one method `convert(::Type{T}, ::Kept{<:T})`
# invalidates 6,863 log entries of plain code at the library's load (W-149). `unwrap(k)` is assigned there.

# the value with its attribute: the object where it was kept `Compiled`, a `Dynamic{X}` where `Dynamic`
Base.getindex(k::Kept{X}) where {X} = getfield(k, :dynamic) ? Dynamic{X}(getfield(k, :object)) : getfield(k, :object)

"""
    kept_call(f, k::Kept, args…)

`f(unwrap(k), args…)` under the attribute `k` was kept with (traits §7.8): `Dynamic` runs the code
compiled once; `Compiled` runs the code compiled for the object's type, chosen when the call runs.
"""
@inline kept_call(f, k::Kept, args...) =
    Core.attributed_call(getfield(k, :dynamic) ? 4294967297 : 1, f, getfield(k, :object), args...)

Base.:(==)(a::Kept, b::Kept) = getfield(a, :object) === getfield(b, :object) && getfield(a, :dynamic) == getfield(b, :dynamic)
Base.isequal(a::Kept, b::Kept) = a == b
Base.hash(k::Kept, h::UInt) = hash(getfield(k, :dynamic), hash(objectid(getfield(k, :object)), hash(:Kept, h)))
function Base.show(io::IO, k::Kept{X}) where {X}
    print(io, "Kept{"); show(io, X); print(io, "}(")
    show(io, getfield(k, :object))
    print(io, getfield(k, :dynamic) ? ", Dynamic)" : ", Compiled)")
end
