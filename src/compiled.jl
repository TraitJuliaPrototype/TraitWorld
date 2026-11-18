# The wrapper (traits §7.4, §7.6): a member kept so that code for it is compiled for its type. The two kept forms
# of a member of a trait `X` are the box `Dynamic{X}` (compiled once per trait instance) and `Compiled{T}`
# (compiled per type `T` of the object). Each is a concrete type and a member of `X`, so the choice travels with
# the value: through storage, untyped parameters and records made before a signature is known.

"""
    Compiled(x)

`x` kept so that code for it is compiled for its type: what `compiled_for(x)` returns. The struct is Julia's
`Core.Compiled` (compiler §6.9), as the box is `Core.Dynamic`; the library declares its memberships (each
`@trait` declares the family `Compiled{Z} where {Z <: X}`) and defines its methods here. Its operations forward
to `x` statically, its declared fields are `x`'s. It is not `x`: a method at `x`'s own type of a function
outside the contract needs `unwrap(w)`. `Compiled(d)` of a `Dynamic{X}` holds the object `d` holds; `Compiled`
of a `Compiled` is itself (Core's constructors).
"""
const Compiled = Core.Compiled

unwrap(w::Compiled) = getfield(w, :object)

"""
    compiled_for(x)

`x` kept so that code for it is compiled for its type: the wrapper `Compiled{typeof(x)}`, a value made in plain
code, a member of every trait `x` is a member of (traits §7.6). On a `Dynamic{X}`, the wrapper of the object it
holds; on a wrapper, the wrapper itself. `unwrap(w)` is the object.
"""
compiled_for(x) = Compiled(x)

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

# Storage typed `Dynamic{X}` converts what is assigned to it: a member is boxed, a wrapper's object boxed, a
# box of another trait boxed again at `X` (the review's addendum, the storage table). A method of `convert`
# at the box's type only.
Base.convert(::Type{Dynamic{X}}, d::Dynamic{X}) where {X} = d
Base.convert(::Type{Dynamic{X}}, @nospecialize(x)) where {X} = Dynamic{X}(x)

# `like` on a wrapper: a wrapper of the value like its object (traits §6.5)
_like(w::Compiled, x) = Compiled(like(getfield(w, :object), x))
