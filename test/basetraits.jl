# BaseTraits (traits §10; lowering §10; W-114): Base's types as members by Base's abstract types,
# element types by variance, `asvector`, `retain!`, `Solvable`, `LinearOp`, `BoundedText`.
using TraitWorld, Test
using LinearAlgebra

mean2(xs::All{Iterable{Float64}, HasLength}) = (s = 0.0; for x in xs; s += x; end; s / length(xs))

@trait Shape begin
    area(s::Shape)::Float64
end
struct Circle; r::Float64; end
struct Square; a::Float64; end
area(c::Circle) = 3.0 * c.r^2
area(s::Square) = s.a^2
@implement Shape Circle
@implement Shape Square
total(shapes::Iterable{<:Shape}) = (s = 0.0; for x in shapes; s += area(x); end; s)

firstof(c::Indexable{T}) where {T} = c[firstindex(c)]
lookup(d::Keyed{String, Int}, k::String) = get(d, k, nothing)       # the value, or nothing

struct Diag2 <: Any
    d::Vector{Float64}
end
Base.size(A::Diag2) = (length(A.d), length(A.d))
Base.eltype(::Type{Diag2}) = Float64                       # the equation T = eltype(Self)
LinearAlgebra.mul!(y::AbstractVector{Float64}, A::Diag2, x::AbstractVector{Float64}) = (y .= A.d .* x; y)
@implement LinearOp{Float64} Diag2 begin                # a member with its own mul!
    apply!(y, A, x) = mul!(y, A, x)
end
apply(A::LinearOp{Float64}, x::Vector{Float64}) = apply!(similar(x), A, x)

solveit(F::Solvable{Float64}, b::AbstractVector{Float64}) = ldiv!(similar(b), F, b)
total_len(xs::Iterable{Char}) = (n = 0; for c in xs; n += 1; end; n)
grow!(xs::Resizable{Int}) = push!(xs, 7)

width(x::BoundedText) = textbound(x)

@testset "BaseTraits: Base's members" begin
    @test [1.0, 2.0, 6.0] isa All{Iterable{Float64}, HasLength}
    @test mean2([1.0, 2.0, 6.0]) == 3.0
    @test !(1.0 isa Iterable)                         # a Number iterates in Base but is not Iterable
    @test Dict("a" => 1) isa Iterable{Pair{String, Int}} && Dict("a" => 1) isa Keyed{String, Int}
    @test lookup(Dict("a" => 1), "a") == 1 && lookup(Dict("a" => 1), "b") === nothing
    @test Set([1, 2]) isa All{Iterable{Int}, HasLength} && total_len("héllo") == 5
    @test collect(keys(IdDict{Any, Any}(1 => 2))) == [1]           # Base's own method wins for a member
    @test !("abc" isa HasLength)                       # a string's length is not constant time
    @test BitVector([true]) isa All{MutableIndexable{Bool}, Resizable{Bool}}
    @test grow!([1]) == [1, 7]
    @test Set([1, 2]) isa All{Iterable{Int}, HasLength}
    @test collect(keys(IdDict{Any, Any}(1 => 2))) == [1]           # Base's own method for a KeySet wins
    @test view([1, 2, 3], 2:3) isa MutableIndexable{Int}      # a view of a writable vector
    @test !(view(1:3, 2:3) isa MutableIndexable)               # a view of a range is not
    @test (1:3) isa Indexable{Int} && !((1:3) isa MutableIndexable)
    @test firstof(view([5, 6, 7], 2:3)) == 6
    @test [1] isa All{MutableIndexable{Int}, Resizable{Int}}
end

@testset "BaseTraits: element types" begin
    @test total([Circle(1.0), Circle(2.0)]) == 15.0           # a Vector{Circle}
    @test total(Shape[Circle(1.0), Square(2.0)]) == 7.0       # a Vector{Shape}
    @test total(Dynamic{Shape}[Dynamic{Shape}(Square(1.0))]) == 1.0
    @test_throws MethodError total(Any[Circle(1.0)])          # a Vector{Any} is not an Iterable{<:Shape}
    @test total(convert(Vector{Shape}, Any[Circle(1.0)])) == 3.0
end

@testset "BaseTraits: algorithms" begin
    v = [1, 2, 3, 4, 5]
    @test retain!(iseven, v) === v && v == [2, 4]
    w = [3.0, -1.0, 2.0]
    retain!(x -> x > 0, w)
    @test w == [3.0, 2.0]
    a = asvector(view([5, 6, 7], 2:3))
    @test a isa AbstractVector{Int} && a == [6, 7] && a[1] == 6
end

@testset "BaseTraits: linear algebra" begin
    A = [4.0 1.0; 1.0 3.0]
    @test A isa LinearOp{Float64}
    @test apply(A, [1.0, 1.0]) == A * [1.0, 1.0]
    @test apply(Diag2([2.0, 3.0]), [1.0, 1.0]) == [2.0, 3.0]  # a matrix-free member
    F = lu(A)
    @test F isa Solvable{Float64}
    @test solveit(F, [1.0, 2.0]) ≈ A \ [1.0, 2.0]
    @test solveit(F, view([0.0, 1.0, 2.0], 2:3)) ≈ A \ [1.0, 2.0]   # a view
    @test solveit(Diagonal([2.0, 4.0]), [1.0, 1.0]) == [0.5, 0.25]  # what `factorize` returns
    @test !(eigen(A) isa Solvable)                                 # a factorization that does not solve
end

@testset "BaseTraits: BoundedText" begin
    @test textbound(Int64) == 20 && textbound(UInt8) == 3 && textbound(Int8) == 4 && textbound(Bool) == 5
    @test textbound(Rational{Int64}) == 42 && textbound(String) === nothing
    @test width(typemin(Int64)) >= length(string(typemin(Int64)))
    @test width(-7) >= 2 && width(big(10)^30) >= 31 && width(3//4) >= 4
    @test width(12) >= length(string(12))
    @test width(1.5) >= length(string(1.5)) && width(1.5f0) >= length(string(1.5f0))
    @test width("abc") == 3 && width(:sym) == 3 && width('x') >= 1
    @test width(true) >= length(string(true))
end

# an operation that is an existing function whose only method there takes any receiver (`show(io, x)`):
# the trait's method, more specific, would hide it, so the membership is refused (open issue 150)
@trait Showy begin
    Base.show(io::IO, x::Showy)::Nothing
end
struct Plain1 end
@testset "BaseTraits: a fallback the trait's method would hide" begin
    e = try @eval(@implement Showy Plain1); nothing catch err; err end
    @test e isa ImplementError && occursin("takes any receiver", sprint(showerror, e))
end

# HasProperty{N, R}: a type joins at each name (traits §3.2, §10.1; compiler §4.6, §7.1; C-32, T-103)
struct Props1
    a::Int
    b::String
end
struct Props2
    store::Vector{Float64}
end
Base.getproperty(p::Props2, s::Symbol) = s === :ps ? getfield(p, :store) : getfield(p, s)
struct Props3; x::Int; end
Base.getproperty(p::Props3, s::Symbol) = s === :q ? "q" : getfield(p, s)
@implement HasProperty{:a, Int} Props1
@implement HasProperty{:b, String} Props1
@implement HasProperty{:ps, Vector{Float64}} Props2
propkind(x::HasProperty{:a}) = :a
propkind(x::HasProperty{:ps}) = :ps
readps(@nospecialize(x::HasProperty{:ps, Vector{Float64}})) = x.ps
@trait PView{P} <: HasProperty{:ps, Vector{P}} begin
    tag(v::PView)::Symbol
end
tag(::Props2) = :p2
@implement PView{Float64} Props2
readview(@nospecialize(v::PView{Float64})) = v.ps
@testset "BaseTraits: HasProperty at several names" begin
    @test Props1 <: HasProperty{:a, Int} && Props1 <: HasProperty{:b, String}
    @test !(Props1 <: HasProperty{:ps}) && !(Props1 <: HasProperty{:a, String})
    @test Props1 <: All{HasProperty{:a, Int}, HasProperty{:b, String}}
    # a second instance at a name already held is refused
    e = try @eval(@implement HasProperty{:a, Float64} Props1); nothing catch err; err end
    @test e !== nothing
    @test Props1 <: HasProperty{:a, Int} && !(Props1 <: HasProperty{:a, Float64})
    # the same instance again is a redeclaration, and keeps the other name
    @eval @implement HasProperty{:a, Int} Props1
    @test Props1 <: HasProperty{:a, Int} && Props1 <: HasProperty{:b, String}
    # dispatch picks by the name
    @test propkind(Props1(1, "x")) === :a && propkind(Props2([1.0])) === :ps
    # x.N on a value known by its trait has the declared type; through a supertrait too
    @test Base.infer_return_type(readps, (HasProperty{:ps, Vector{Float64}},)) == Vector{Float64}
    @test readps(Props2([2.0])) == [2.0]
    @test Base.infer_return_type(readview, (PView{Float64},)) == Vector{Float64}
    @test readview(Props2([3.0])) == [3.0]
    # the member's own getproperty is checked at the constant name
    e = try @eval(@implement HasProperty{:q, Int} Props3); nothing catch err; err end
    @test e isa ImplementError && occursin("infers String", sprint(showerror, e))
    @eval @implement HasProperty{:q, String} Props3
    @test Props3 <: HasProperty{:q, String}
    # only an input names a field
    @test_throws Exception @eval @trait BadField{N, R} begin
        @const N::R
    end
end

# Two traits' operations of one function tie at a common member with no method of its own (traits §6.3).
# The library's pairs, each with its reason; a new pair fails here.
@testset "the traits' operations: pairs with no joint method" begin
    amb = Test.detect_ambiguities(TraitWorld; recursive = true)
    recv(m) = string(nameof(Base.unwrap_unionall(Base.unwrap_unionall(m.sig).parameters[2])))
    pairs = unique!(sort!([string(a.name, ": ", join(sort!([recv(a), recv(b)]), ", ")) for (a, b) in amb]))
    # `getindex` by position and by key: no one answer is right for every type in both, so each
    # common member defines its own (as `Dict` does)
    @test pairs == ["getindex: Indexable, Keyed"]
end
