# The library core (W-106): the forms of traits §3–§6, §7.7, §8 and their checks.
using TraitWorld, Test

## parameters (traits §3.2)
@trait KVec{T} begin
    T = eltype(Self)
    klen(v::KVec)::Int
    kget(v::KVec{T}, i::Int)::T
end
struct Ramp; n::Int; end
Base.eltype(::Type{Ramp}) = Float64
klen(r::Ramp) = r.n
kget(r::Ramp, i::Int) = Float64(i)
@implement KVec Ramp

@trait Integrator{U, P} begin
    u::U
    @const p::P
    t::Float64
end
mutable struct Integ
    u::Vector{Float64}
    const p::Tuple{Int,Int}
    t::Float64
end
@implement Integrator Integ

@trait ArrayLike{T, N} begin
    alen(a::ArrayLike)::Int
end
struct MyVec; data::Vector{Float32}; end
alen(v::MyVec) = length(v.data)
@implement ArrayLike{Float32, 1} MyVec

@testset "parameters" begin
    @test Ramp(3) isa KVec{Float64}
    @test !(Ramp(3) isa KVec{Int})
    @test Ramp(3) isa KVec{<:Real}
    @test Ramp <: KVec
    @test Integ([1.0], (1, 2), 0.0) isa Integrator{Vector{Float64}, Tuple{Int,Int}}
    @test MyVec(Float32[1]) isa ArrayLike{Float32, 1}
    @test kget(Ramp(3), 2) === 2.0
    f(v::KVec{T}) where {T} = T
    @test f(Ramp(1)) === Float64
end

## refusals at the declaration (traits §5.10)
struct NoLen end
Base.eltype(::Type{NoLen}) = Int
struct WideKget; end
Base.eltype(::Type{WideKget}) = Int
klen(::WideKget) = 1
kget(::WideKget, i::Int) = i > 0 ? i : 1.0
struct BadT; end
Base.eltype(::Type{BadT}) = Int
klen(::BadT) = 1
kget(::BadT, i::Int) = i

@testset "refusals" begin
    e = try @eval(@implement KVec NoLen); nothing catch err; err end
    @test e isa ImplementError
    @test occursin("klen", sprint(showerror, e)) && occursin("kget", sprint(showerror, e))
    @test !(NoLen() isa KVec)
    e = try @eval(@implement KVec WideKget); nothing catch err; err end
    @test e isa ImplementError && occursin("wider", sprint(showerror, e))
    e = try @eval(@implement KVec{Float64} BadT); nothing catch err; err end   # stated against the equation
    @test e isa ImplementError && occursin("equation", sprint(showerror, e))
    e = try @eval(@implement ArrayLike MyVec); nothing catch err; err end       # undetermined parameters
    @test e isa ImplementError && occursin("not determined", sprint(showerror, e))
end

mutable struct FrozenInteg
    u::Vector{Float64}
    p::Tuple{Int,Int}
    const t::Float64
end
struct ImmInteg
    u::Vector{Float64}
    p::Tuple{Int,Int}
    t::Float64
end
@testset "fields" begin
    e = try @eval(@implement Integrator FrozenInteg); nothing catch err; err end
    @test e isa ImplementError && occursin("const", sprint(showerror, e))
    e = try @eval(@implement Integrator ImmInteg); nothing catch err; err end
    @test e isa ImplementError && occursin("immutable", sprint(showerror, e))
    i = Integ([1.0], (1, 2), 0.0)
    g(x::Integrator) = (x.t += 1.0; x.u[1])
    @test g(i) == 1.0 && i.t == 1.0
end

## a block of methods, forwarding (traits §5.4, §5.5)
@trait ColTable begin
    ncols(t::ColTable)::Int
    col(t::ColTable, i::Int)::Vector{Float64}
    firstcol(t::ColTable)::Vector{Float64} = col(t, 1)
end
@implement ColTable Vector{Vector{Float64}} begin
    ncols(t) = length(t)
    col(t, i) = t[i]
end
struct Halves
    name::String
    right::Vector{Vector{Float64}}
end
@implement ColTable Halves by right
colmean(t::ColTable, i::Int) = (c = col(t, i); sum(c) / length(c))

@testset "block and forwarding" begin
    v = [[1.0, 2.0], [3.0, 5.0]]
    @test v isa ColTable
    @test ncols(v) == 2 && firstcol(v) == [1.0, 2.0]
    h = Halves("h", v)
    @test h isa ColTable
    @test ncols(h) == 2 && col(h, 2) == [3.0, 5.0] && firstcol(h) == [1.0, 2.0]
    @test colmean(h, 2) == 4.0
    h2 = like(h, [[7.0]])
    @test h2 isa Halves && h2.name == "h" && ncols(h2) == 1
    @test withfields(h; name = "k").name == "k"
    struct Chain; inner::Halves; end
    e = try @eval(@implement ColTable Chain by inner); nothing catch err; err end
    @test e isa ImplementError && occursin("chain", sprint(showerror, e))
end

## supertraits (traits §4.5)
@trait DCol begin
    dlen(c::DCol)::Int
end
@trait DGrow{T} <: DCol begin
    T = eltype(Self)
    dpush!(c::DGrow, x::Float64)::Nothing
end
mutable struct Buf; xs::Vector{Float64}; end
Base.eltype(::Type{Buf}) = Float64
dlen(b::Buf) = length(b.xs)
dpush!(b::Buf, x::Float64) = (push!(b.xs, x); nothing)
@implement DGrow Buf
struct OnlyGrow; end
Base.eltype(::Type{OnlyGrow}) = Float64
dpush!(::OnlyGrow, ::Float64) = nothing

@testset "supertraits" begin
    @test DGrow <: DCol
    @test Buf(Float64[]) isa DCol && Buf(Float64[]) isa DGrow{Float64}
    e = try @eval(@implement DGrow OnlyGrow); nothing catch err; err end
    @test e isa ImplementError && occursin("dlen", sprint(showerror, e))
end

## Dynamic (traits §7.7, §8.3)
@testset "Dynamic" begin
    d = Dynamic{ColTable}([[1.0, 2.0]])
    @test d isa ColTable && ncols(d) == 1 && firstcol(d) == [1.0, 2.0]
    @test colmean(d, 1) == 1.5
    @test_throws ArgumentError Dynamic{KVec}(Ramp(2))           # the parameters required
    dk = Dynamic{KVec{Float64}}(Ramp(2))
    @test dk isa KVec{Float64} && kget(dk, 2) === 2.0 && klen(dk) == 2
    @test_throws TypeError Dynamic{ColTable}(Ramp(2))
    @test Dynamic{ColTable}(d) == d && unwrap(Dynamic{ColTable}(d)) === unwrap(d)
    v = [[1.0]]
    @test Dynamic{ColTable}(v) == Dynamic{ColTable}(v) && hash(Dynamic{ColTable}(v)) == hash(Dynamic{ColTable}(v))
    @test Dynamic{ColTable}(v) != Dynamic{ColTable}([[1.0]])
    dg = Dynamic{DGrow{Float64}}(Buf([1.0]))
    @test dg isa DCol && dlen(dg) == 1 && dpush!(dg, 2.0) === nothing && dlen(dg) == 2
    di = Dynamic{Integrator{Vector{Float64}, Tuple{Int,Int}}}(Integ([1.0], (1, 2), 0.0))
    @test di.u == [1.0] && (di.t = 2.0; di.t == 2.0)
    @test_throws ArgumentError (di.p = (3, 4))
    @test like(d, [[5.0]]) isa Dynamic{ColTable}
    hs = Dynamic{ColTable}[Dynamic{ColTable}(v), Dynamic{ColTable}(Halves("x", v))]
    @test sum(ncols, hs) == 2
end

## families (traits §5.8) and members checked at their first use (lowering §4)
@trait Fam begin
    fsize(x::Fam)::Int
end
struct Box{P}; x::P; end
fsize(b::Box) = 1
@implement Fam Box{P} where {P}

@testset "families" begin
    @test Box(1) isa Fam && Box("a") isa Fam
    @test fsize(Box(2.0)) == 1
    @test TraitWorld.check_first_use(Box{Int}, Fam) === nothing
end

## dispatch (traits §6)
describe2(v::Vector{Float64}) = "a vector"
describe2(m::AbstractMatrix) = "a matrix"
describe2(t::ColTable) = "a table with $(ncols(t)) columns"
describe2(x) = "something else"
@testset "dispatch" begin
    @test describe2([[1.0]]) == "a table with 1 columns"
    @test describe2(Halves("a", [[1.0]])) == "a table with 1 columns"
    @test describe2([1.0]) == "a vector"
    @test describe2(1) == "something else"
end

## a family's member that fails the contract, checked at its first use (F10; lowering §4)
@trait Sized2 begin
    sz(x::Sized2)::Int
end
struct W2{P}; x::P; end
sz(w::W2{Int}) = 1
@implement Sized2 W2{P} where {P}
@testset "first use" begin
    @test W2(1.0) isa Sized2                       # memberships only grow: isa stays true
    @test sz(W2(1)) == 1                           # its own method: no use through the trait
    # at dispatch (the hook's half in the compile queue is not built: lowering L-52)
    e = try Base.invokelatest(sz, W2(1.0)); nothing catch err; err end
    @test e isa ImplementError && occursin("sz", sprint(showerror, e))
    e2 = try Base.invokelatest(sz, W2(2.0)); nothing catch err; err end
    @test e2 === e                                 # the kept failure, raised at every use
end

## a family variable bounded by a Union: one membership per type (lowering §3)
@trait BoundedText begin
    btext(x::BoundedText)::String
end
btext(x::Integer) = string(x)
@implement BoundedText I where {I <: Union{Int8, Int16}}
@testset "Union-bounded family" begin
    @test Int8(1) isa BoundedText && Int16(1) isa BoundedText && !(Int32(1) isa BoundedText)
    @test length(Int8.name.memberships) == 1 && length(Int16.name.memberships) == 1
end

## intersections All{X, Y} (traits §3.6), where the build has them (W-107)
if isdefined(Core, :All)
    @trait IShape begin
        iarea(s::IShape)::Float64
    end
    @trait IPlaced begin
        iorigin(p::IPlaced)::Tuple{Float64, Float64}
    end
    struct IDisc
        r::Float64
    end
    iarea(d::IDisc) = pi * d.r^2
    iorigin(::IDisc) = (0.0, 0.0)
    struct IDot end
    iorigin(::IDot) = (1.0, 1.0)
    @implement (IShape, IPlaced) IDisc
    @implement IPlaced IDot
    const ShapeAt = All{IShape, IPlaced}                    # a bundle: a name for the intersection
    idescribe(x::ShapeAt) = (iarea(x), iorigin(x))
    idescribe(x::IPlaced) = iorigin(x)
    @testset "intersections" begin
        @test All === Core.All
        @test IDisc <: ShapeAt && !(IDot <: ShapeAt)
        @test ShapeAt === All{IPlaced, IShape}
        @test idescribe(IDisc(1.0)) == (float(pi), (0.0, 0.0))
        @test idescribe(IDot()) == (1.0, 1.0)
        d = Dynamic{ShapeAt}(IDisc(2.0))
        @test d isa IShape && d isa IPlaced && d isa ShapeAt
        @test Base.invokelatest(idescribe, d)[1] ≈ 4pi
        @test_throws TypeError Dynamic{ShapeAt}(IDot())
    end
end
