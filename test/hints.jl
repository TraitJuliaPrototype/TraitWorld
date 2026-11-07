# The hints on Julia's MethodError where a trait is involved (traits §11.4; W-114).
using TraitWorld, Test

@trait ColTable begin
    col(t::ColTable, i::Int)::Vector{Float64}
end
@trait StateVector{T} begin
    T = eltype(Self)
    slen(v::StateVector)::Int
end
slen(v::Vector) = length(v)
@implement StateVector Vector{Float32}
@implement StateVector Vector{Float64}

struct Circle; r::Float64; end
struct Tab; c::Vector{Float64}; end
col(t::Tab, i::Int) = t.c
@implement ColTable Tab

colmean(t::ColTable, i::Int) = sum(col(t, i)) / length(col(t, i))
step!(v::StateVector{Float64}) = v
axpy(a::StateVector{T}, b::StateVector{T}) where {T} = a

msg(f) = try f(); "" catch e; sprint(showerror, e) end

@trait Aa
@trait Bb
amb(x::Aa) = 1
amb(x::Bb) = 2
struct Both end
@implement Aa Both
@implement Bb Both            # warns: amb is ambiguous for Both (traits §6.3)

@testset "hints" begin
    m = msg(() -> colmean(Circle(1.0), 1))
    @test occursin("`Circle` is not a member of `ColTable`", m) && occursin("@implement ColTable Circle", m)
    @test occursin("its declared members: Tab", m)
    m = msg(() -> step!(Float32[1]))
    @test occursin("is a member of `StateVector{Float32}`; the method takes `StateVector{Float64}`", m)
    m = msg(() -> axpy([1.0], Float32[1]))
    @test occursin("`T` is `Float64` for `a` and `Float32` for `b`", m)
    m = msg(() -> col(Tab([1.0]), "x"))
    @test occursin("`col` is declared `col(t::ColTable, i::Int)::Vector{Float64}`", m)
    m = msg(() -> amb(Both()))
    @test occursin("amb(::All{", m) && occursin("Aa", m) && occursin("Bb", m)   # Julia's own: the joint method
end
