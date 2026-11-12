# BaseTraits (traits §10; lowering §10): the library's standard set of traits for the concepts Base
# defines informally, each with its item types as associated types. Its traits are ordinary traits;
# the language depends on none. The library owns them and declares Base's types' memberships, by
# Base's abstract types. The prior art behind the contracts:
# writeup/record/collection-and-linalg-traits-research-2026-11-07.md; the review of the choices:
# writeup/reviews/2026-11-07-basetraits-choices.md.
module BaseTraits

using ..TraitWorld
using ..TraitWorld: keep
import LinearAlgebra
using LinearAlgebra: Factorization, ldiv!, mul!
import Dates

@trait_module

export HasLength, Iterable, Indexable, MutableIndexable, Resizable, Keyed, Solvable,
       LinearOp, apply!, BoundedText, textbound, HasProperty, asvector, IndexableVector, retain!

# --- the traits ----------------------------------------------------------------------------------

@trait HasLength begin
    Base.length(c::HasLength)::Int
end
@doc """
    HasLength

A finite number of items: `length(c)::Int`, expected in constant time. A membership's check verifies
the result's type, not its value: trait code does not index without bounds checks on a member's
`length` alone. Not `Base.HasLength`, the value of `Base.IteratorSize`.
""" HasLength

@trait Iterable{T} begin
    T = eltype(Self)
    Base.iterate(c::Iterable)::Union{Nothing, Tuple{T, Any}}
    Base.iterate(c::Iterable, state)::Union{Nothing, Tuple{T, Any}}
end
@doc """
    Iterable{T}

Base's iteration protocol, with the item type `T = eltype(Self)`. Iteration is repeatable and leaves
the collection unchanged: a single-pass iterator (`eachline`, `Iterators.Stateful`) is no member.
""" Iterable

@trait Indexable{T} <: HasLength begin
    T = eltype(Self)
    Base.getindex(c::Indexable, i::Int)::T
    Base.firstindex(c::Indexable)::Int
end
@doc """
    Indexable{T} <: HasLength

Reading by position: `c[i]` is a `T` for `i` in `firstindex(c):firstindex(c)+length(c)-1`. The first
position is the member's: an offset vector is a member.
""" Indexable

@trait MutableIndexable{T} <: Indexable{T} begin
    T = eltype(Self)
    Base.setindex!(c::MutableIndexable, x::T, i::Int)::Any
end
@doc """
    MutableIndexable{T} <: Indexable{T}

Writing by position: `c[i] = x` for an `x` of the item type keeps the number of items, and `c[i]` then
reads `x` back.
""" MutableIndexable

@trait Resizable{T} <: HasLength begin
    T = eltype(Self)
    Base.resize!(c::Resizable, n::Int)::Any
    Base.push!(c::Resizable, x::T)::Any
end
@doc """
    Resizable{T} <: HasLength

Changing the number of items: `push!(c, x)` adds an item of the item type at the end; `resize!(c, n)`
for `n ≤ length(c)` keeps the first `n`. Growing without a value is outside the contract (Julia's
`resize!` grows a `Vector` with undefined items).
""" Resizable

@trait Keyed{K, V} <: HasLength begin
    K = keytype(Self)
    V = valtype(Self)
    Base.getindex(d::Keyed, k::K)::V
    Base.haskey(d::Keyed, k::K)::Bool
    Base.get(d::Keyed, k::K, default::D)::Union{V, D} where {D}
end
@doc """
    Keyed{K, V} <: HasLength

Reading by key: `d[k]` is a `V` where `haskey(d, k)`; `get(d, k, default)` is the value or the default,
which may be of any type (`get(d, k, nothing)`). Its pairs are iterated through `Iterable`: a
`Dict{String, Int}` is `Iterable{Pair{String, Int}}`.
""" Keyed

@trait Solvable{T} begin
    T = eltype(Self)
    LinearAlgebra.ldiv!(x::AbstractVector{T}, F::Solvable, b::AbstractVector{T})::AbstractVector{T}
end
@doc """
    Solvable{T}

A factorization, or any operator that solves in place: `ldiv!(x, F, b)` writes the solution of
`F x = b` into `x`, for the vectors of the element type the member accepts (LinearAlgebra's
factorizations: one-based vectors in host memory, views included).
""" Solvable

"""
    apply!(y, A, x)

Write `A x` into `y`, where `A` is a `LinearOp`. A function of BaseTraits' own: a method of
LinearAlgebra's `mul!` at the trait would hide `mul!`'s untyped fallback for every matrix (E-281).
"""
function apply! end

@trait LinearOp{T} begin
    T = eltype(Self)
    Base.size(A::LinearOp)::Tuple{Int, Int}
    apply!(y::AbstractVector{T}, A::LinearOp, x::AbstractVector{T})::AbstractVector{T}
end
@doc """
    LinearOp{T}

A linear map, matrix or matrix-free: `size(A)`, `eltype(A)`, and `apply!(y, A, x)`, which writes
`A x` into `y` and returns `y`. A member with its own `mul!` joins with a block,
`apply!(y, A, x) = mul!(y, A, x)`, as Base's matrices do.
""" LinearOp

"""
    textbound(x)
    textbound(T::Type) -> Union{Int, Nothing}

An upper bound on the bytes `print(io, x)` writes. For a type, the bound that holds for every value of
it, or `nothing` where none is fixed: a writer sizes a column without visiting its cells, and visits
them only where the type has no bound. Code that preallocates by it still checks what `print` wrote.
"""
function textbound end

@trait BoundedText begin
    textbound(x::BoundedText)::Int
end
@doc """
    BoundedText

A value whose printed form has a known upper bound in bytes: `textbound(x)::Int`; `textbound(T)`
for a type with a fixed bound.
""" BoundedText

@trait HasProperty{N, R} begin
    @input N
    @const N::R
end
@doc """
    HasProperty{N, R}

A property by name: `x.N` is an `R` (`getproperty` at the constant name `N`), served by a stored
field or by the member's own `getproperty`. `N` is an input: a type joins at each name,
`@implement HasProperty{:ps, PView} Integ`. On a value known only by its trait, `x.N` has the
declared type, as a declared field's read.
""" HasProperty

# --- Base's types, by Base's abstract types and Base's own methods (lowering §10) ---------------

@implement HasLength AbstractArray
@implement HasLength AbstractDict
@implement HasLength AbstractSet
@implement Iterable{T} AbstractArray{T} where {T}
@implement Iterable{Pair{K, V}} AbstractDict{K, V} where {K, V}
@implement Iterable{T} AbstractSet{T} where {T}
@implement Iterable{Char} AbstractString
@implement Indexable{T} AbstractVector{T} where {T}
@implement MutableIndexable{T} Vector{T} where {T}
@implement MutableIndexable{Bool} BitVector
# a view is writable where its parent is: a family whose variable a trait bounds
@implement MutableIndexable{T} SubArray{T, 1, P} where {T, P <: MutableIndexable{T}}
@implement Resizable{T} Vector{T} where {T}
@implement Resizable{Bool} BitVector
@implement Keyed{K, V} AbstractDict{K, V} where {K, V}
@implement LinearOp{T} AbstractMatrix{T} where {T} begin
    apply!(y, A, x) = mul!(y, A, x)
end
# the factorizations that solve, and the matrix types `factorize` returns, by their own `ldiv!`
@implement Solvable{T} LinearAlgebra.LU{T} where {T}
@implement Solvable{T} LinearAlgebra.Cholesky{T} where {T}
@implement Solvable{T} LinearAlgebra.CholeskyPivoted{T} where {T}
@implement Solvable{T} LinearAlgebra.QR{T} where {T}
@implement Solvable{T} LinearAlgebra.QRCompactWY{T} where {T}
@implement Solvable{T} LinearAlgebra.QRPivoted{T} where {T}
@implement Solvable{T} LinearAlgebra.LQ{T} where {T}
@implement Solvable{T} LinearAlgebra.BunchKaufman{T} where {T}
@implement Solvable{T} LinearAlgebra.LDLt{T} where {T}
@implement Solvable{T} LinearAlgebra.SVD{T} where {T}
@implement Solvable{T} LinearAlgebra.Diagonal{T} where {T}
@implement Solvable{T} LinearAlgebra.UpperTriangular{T} where {T}
@implement Solvable{T} LinearAlgebra.LowerTriangular{T} where {T}
@implement Solvable{T} LinearAlgebra.Bidiagonal{T} where {T}

# BoundedText: a constant per type where the width is fixed, a value's own bound otherwise
textbound(::Type) = nothing
textbound(::Type{Bool}) = 5
@generated textbound(::Type{T}) where {T <: Base.BitInteger} = ndigits(typemax(T)) + (T <: Signed)
textbound(::Type{Float64}) = 24
textbound(::Type{Float32}) = 16
textbound(::Type{Float16}) = 10
textbound(::Type{<:AbstractChar}) = 4
textbound(::Type{Dates.Date}) = 24
textbound(::Type{Dates.DateTime}) = 32
textbound(::Type{Dates.Time}) = 18
function textbound(::Type{Rational{T}}) where {T}
    b = textbound(T)
    return b === nothing ? nothing : 2b + 2
end
function textbound(::Type{Complex{T}}) where {T}
    b = textbound(T)
    return b === nothing ? nothing : 2b + 5
end
textbound(x::Number) = something(textbound(typeof(x)), ncodeunits(string(x)))
textbound(x::Rational) = textbound(numerator(x)) + textbound(denominator(x)) + 2
textbound(x::Complex) = textbound(real(x)) + textbound(imag(x)) + 5
textbound(x::AbstractChar) = 4
textbound(x::Union{String, SubString{String}}) = ncodeunits(x)
textbound(x::AbstractString) = 4 * length(x)          # printed as UTF-8: at most four bytes a character
textbound(x::Symbol) = sizeof(x)
textbound(x::Union{Dates.Date, Dates.DateTime, Dates.Time}) = textbound(typeof(x))
textbound(x::Union{Dates.Period, Dates.CompoundPeriod}) = ncodeunits(string(x))
@implement BoundedText Number
@implement BoundedText AbstractChar
@implement BoundedText AbstractString
@implement BoundedText Symbol
@implement BoundedText Dates.TimeType
@implement BoundedText Dates.Period
@implement BoundedText Dates.CompoundPeriod

# --- algorithms (traits §10.3) ------------------------------------------------------------------

"""
    IndexableVector{T, C}

An `Indexable{T}` as a read-only `AbstractVector{T}` for plain code, without a copy, its positions
`1:length(c)`. The member checks every read's bounds.
"""
struct IndexableVector{T, C} <: AbstractVector{T}
    c::C
end
Base.size(v::IndexableVector) = (length(v.c),)
Base.IndexStyle(::Type{<:IndexableVector}) = IndexLinear()
Base.getindex(v::IndexableVector, i::Int) = v.c[firstindex(v.c) + i - 1]

"""
    asvector(x::Indexable{T})

`x` as a read-only `AbstractVector{T}` for plain code, without a copy (an `IndexableVector`).
"""
@unbounded function asvector(x::Indexable{T}) where {T}
    k = keep(x)
    return IndexableVector{T, typeof(k)}(k)
end

"""
    retain!(f, xs)

Keep the items of `xs` for which `f` is `true`, in place, in order: Base's `filter!` for trait code.
Compiled once per item type for a closure or a function of the user's (`f` is a `Callable`, `Dynamic`
by default), per function for a function Julia defines.
"""
function retain!(f::Callable{Tuple{T}, Bool}, xs::All{MutableIndexable{T}, Resizable{T}}) where {T}
    first = firstindex(xs)
    j = first - 1
    for i in first:first+length(xs)-1
        x = xs[i]
        if f(x)
            j += 1
            xs[j] = x
        end
    end
    resize!(xs, j - first + 1)
    return xs
end

end # module
