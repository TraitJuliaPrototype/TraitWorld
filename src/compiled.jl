# The wrapper: a member kept so that code for it is compiled for its type (W-151, the prototype of the
# review's P1 as accepted, "values carry, by type"; open issue 186). The two kept forms of a member of a
# trait `X` are the box `Dynamic{X}` (compiled once per trait instance) and `Compiled{T}` (compiled per
# type `T` of the object). Each is a concrete type and a member of `X`, so the choice travels with the value:
# through storage, untyped parameters and records made before a signature is known.

"""
    Compiled(x)

`x` kept so that code for it is compiled for its type: what `compiled_for(x)` returns. A member of every
trait `x` is a member of (each `@trait` declares the family `Compiled{Z} where {Z <: X}`); its
operations forward to `x` statically, its declared fields are `x`'s. It is not `x`: a method at `x`'s own
type of a function outside the contract needs `unwrap(w)`. `Compiled(d)` of a `Dynamic{X}` holds the
object `d` holds; `Compiled` of a `Compiled` is itself.
"""
struct Compiled{T}
    object::T
    Compiled{T}(x) where {T} = new{T}(x)
end
Compiled(x::T) where {T} = Compiled{T}(x)
Compiled(w::Compiled) = w
Compiled(d::Dynamic) = Compiled(getfield(d, :object))

unwrap(w::Compiled) = getfield(w, :object)

# Every trait the wrapper is a member of forwards to its object (the trait's method for an operation reads
# `_fwd`, trait.jl): resolved at the wrapper's type, so the operation's call is the object's own method.
_fwd(w::Compiled, @nospecialize(X::Type)) = getfield(w, :object)

# a function kept compiled: called as itself (traits §9)
(w::Compiled)(args...; kws...) = getfield(w, :object)(args...; kws...)

# the object's declared fields, read and written through the wrapper: any trait's, since the wrapper is a
# member of each of its object's traits
Base.getproperty(w::Compiled, s::Symbol) = getproperty(getfield(w, :object), s)
Base.setproperty!(w::Compiled, s::Symbol, v) = setproperty!(getfield(w, :object), s, v)
Base.propertynames(w::Compiled) = propertynames(getfield(w, :object))

# equality by the objects' identity, as a box's (traits §8.3)
Base.:(==)(a::Compiled, b::Compiled) = getfield(a, :object) === getfield(b, :object)
Base.isequal(a::Compiled, b::Compiled) = getfield(a, :object) === getfield(b, :object)
Base.hash(w::Compiled, h::UInt) = hash(objectid(getfield(w, :object)), hash(:Compiled, h))

function Base.show(io::IO, w::Compiled)
    print(io, "Compiled(")
    show(io, getfield(w, :object))
    print(io, ")")
end

# A box of a wrapper holds the object: the wrapper's choice is erased there.
(::Type{Dynamic{X}})(w::Compiled) where {X} = Dynamic{X}(getfield(w, :object))
# A box of the same trait is itself, and a box of a subtrait holds its object at the trait: neither tests the
# membership again. (Julia's constructor, compiled once for any value, makes a new box and tests the object
# against the trait when it runs: a run-time membership query at each re-boxing, E-403.)
(::Type{Dynamic{X}})(d::Dynamic{X}) where {X} = d
(::Type{Dynamic{X}})(d::Dynamic{Y}) where {X, Y <: X} = _new_box(Dynamic{X}, getfield(d, :object))

# Storage typed `Dynamic{X}` converts what is assigned to it: a member is boxed, a wrapper's object boxed, a
# box of another trait boxed again at `X` (the review's addendum, the storage table). A method of `convert`
# at the box's type only.
Base.convert(::Type{Dynamic{X}}, d::Dynamic{X}) where {X} = d
Base.convert(::Type{Dynamic{X}}, @nospecialize(x)) where {X} = Dynamic{X}(x)

# `like` on a wrapper: a wrapper of the value like its object (traits §6.5)
_like(w::Compiled, x) = Compiled(like(getfield(w, :object), x))
