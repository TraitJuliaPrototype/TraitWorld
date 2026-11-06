# W-106's acceptance cases: F1–F8, F10, F11, F14 of the proposal "traits are abstract types"
# (writeup/plans/2026-11-06-traits-are-abstract-types.md §2), on the unified build.
using TraitWorld, Test

@trait Shape begin
    area(s::Shape)::Float64
    describe(s::Shape)::String = "a shape of area $(area(s))"
end
struct Circle; r::Float64; end
area(c::Circle) = π * c.r^2
@implement Shape Circle
struct Square <: Shape; a::Float64; end           # with its definition
area(s::Square) = s.a^2
@implement Shape Square
mutable struct Holder; s::Shape; end
struct Problem{F <: Shape}; f::F; end

@testset "F1: a trait stands wherever a type stands" begin
    f1(x::Shape) = :shape
    g1(v::Vector{<:Shape}) = length(v)
    h1(x::T) where {T <: Shape} = T
    @test f1(Circle(1.0)) === :shape
    @test g1([Circle(1.0), Circle(2.0)]) == 2
    @test h1(Circle(1.0)) === Circle
    @test Dict{String,Shape}("a" => Circle(1.0))["a"] isa Circle
    @test Ref{Shape}(Circle(1.0))[] isa Circle
    @test Union{Nothing,Shape} >: Circle
    @test convert(Shape, Circle(1.0)) === Circle(1.0)
    @test Circle(1.0)::Shape === Circle(1.0)
    @test Type{Circle} <: Type{<:Shape}
    @test Square <: Shape && supertype(Square) === Shape
end

@trait KV{T} begin
    T = eltype(Self)
    kn(v::KV)::Int
end
struct IntVec; xs::Vector{Int}; end
Base.eltype(::Type{IntVec}) = Int
kn(v::IntVec) = length(v.xs)
@implement KV IntVec

@testset "F2, F3: the bare name is a UnionAll; parameters follow Julia" begin
    @test KV isa UnionAll && IntVec <: KV
    @test IntVec <: KV{Int} && !(IntVec <: KV{Integer})
    @test IntVec <: KV{<:Integer} && IntVec <: KV{>:Int}
    kt(v::KV{T}, x::T) where {T} = (T, x)
    @test kt(IntVec([1]), 3) == (Int, 3)
    @test_throws MethodError kt(IntVec([1]), 3.0)    # a broken shared variable: Julia's error (F14)
end

@testset "F4: a member's value is a value of the trait" begin
    c = Circle(2.0)
    same(x::Shape) = x
    @test same(c) === c
    @test typeof(same(c)) === Circle
    store = Shape[]
    push!(store, c)
    @test store[1] === c
end

@trait Base2 begin
    bv(x::Base2)::Int
end
@trait Sub2 <: Base2 begin
    sv(x::Sub2)::Int
end
struct BS; end
bv(::BS) = 1
sv(::BS) = 2
@implement Sub2 BS
@testset "F5: supertraits are supertypes" begin
    @test Sub2 <: Base2 && BS <: Base2 && BS() isa Base2
    usebase(x::Base2) = bv(x)
    @test usebase(BS()) == 1
end

@testset "F6: dispatch is Julia's" begin
    pick(x::AbstractFloat) = :float
    pick(x::Shape) = :shape
    pick(x) = :any
    @test pick(Circle(1.0)) === :shape && pick(1.0) === :float && pick(1) === :any
    @test_throws MethodError area(1)
end

@testset "F7: storage" begin
    h = Holder(Circle(1.0))
    h.s = Square(2.0)
    @test h.s isa Square
    p = Problem(Circle(1.0))
    @test p isa Problem{Circle}
    @test_throws TypeError Problem{Int}
    pd = Problem(Dynamic{Shape}(Circle(1.0)))
    @test pd isa Problem{Dynamic{Shape}}
end

struct Fwd; inner::Circle; end
@implement Shape Fwd by inner
describe(::Square) = "a square"                      # the member's own method
@testset "F8: defaults and forwarding reach plain callers" begin
    @test describe(Circle(1.0)) == "a shape of area $(Float64(π))"
    @test area(Fwd(Circle(1.0))) == Float64(π)       # forwarding, from plain code
    @test describe(Fwd(Circle(1.0))) == "a shape of area $(Float64(π))"
    @test describe(Square(1.0)) == "a square"         # wins over the default
end

@trait Sized3 begin
    sz3(x::Sized3)::Int
end
struct Fam3{P}; x::P; end
sz3(w::Fam3{Int}) = 1
@implement Sized3 Fam3{P} where {P}
@testset "F10: a family's member is checked at its first use" begin
    @test Fam3(1.0) isa Sized3
    @test Base.invokelatest(sz3, Fam3(1)) == 1
    @test_throws ImplementError Base.invokelatest(sz3, Fam3(1.0))
    @test_throws ImplementError Base.invokelatest(sz3, Fam3(2.0))
    @test Fam3(1.0) isa Sized3                        # memberships only grow
end

@trait Indexable{T} begin
    T = eltype(Self)
    ilen(x::Indexable)::Int
    iget(x::Indexable{T}, i::Int)::T
end
@implement Indexable{T} AbstractVector{T} where {T} begin
    ilen(x) = length(x)
    iget(x, i) = x[i]
end
@trait GTable begin
    gn(t::GTable)::Int
    gcol(t::GTable, i::Int)::Vector{Float64}
end
@implement GTable Indexable{Vector{Float64}} begin
    gn(r) = ilen(r)
    gcol(r, i) = iget(r, i)
end
@testset "F11: a generic implementation is a set in a set" begin
    v = [[1.0, 2.0], [3.0]]
    @test v isa Indexable{Vector{Float64}} && v isa GTable
    @test gn(v) == 2 && gcol(v, 2) == [3.0]
    @test !([1, 2] isa GTable)
end

@testset "F14: errors" begin
    @test_throws MethodError area("x")               # not a member: Julia's error
    struct NotOne; end
    e = try @eval(@implement Shape NotOne); nothing catch err; err end
    @test e isa ImplementError
    kw(; s::Shape) = s
    @test_throws TypeError kw(s = 1)
end
