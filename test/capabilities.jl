# A kept value seen at a bound through every trait its object conforms to; a kept function at another
# signature checked there; a Callable whose argument types follow a trait bound (traits reference §5.8,
# §6.5; W-81). Runs inside runtests.jl.
using Test, TraitWorld

toplevel(quote
    @trait_module module CapT
    using TraitWorld
    export CCol, CPooled, cn, ccodes, ckind, CShape, carea, ccount
    @trait CCol begin
        cn(c::CCol)::Int
    end
    @trait CPooled begin
        ccodes(c::CPooled)::Vector{Int}
    end
    @trait CShape begin
        carea(s::CShape)::Float64
    end
    ckind(c::CCol) = :plain
    ckind(c::(CCol, CPooled)) = :pooled
    ccount(f::Callable{Tuple{T}, Bool}, xs::Iterable{T}) where {T} = (n = 0; for x in xs; f(x) && (n += 1); end; n)
    sigf(f::Callable{Tuple{Float64}, Float64}, x::Float64) = f(x)
    sigs(f::Callable{Tuple{String}, Int}, s::String) = f(s)
    end
    struct CPlainCol; v::Vector{Float64}; end
    struct CPoolCol; c::Vector{Int}; end
    struct CCircle; r::Float64; end
    @implement CapT.CCol CPlainCol begin cn(c) = length(c.v) end
    @implement CapT.CCol CPoolCol begin cn(c) = length(c.c) end
    @implement CapT.CPooled CPoolCol begin ccodes(c) = c.c end
    @implement CapT.CShape CCircle begin carea(s) = pi * s.r^2 end
end)

@testset "a stored value's capabilities, functions at other signatures, Callables that follow" begin
    M = Main.CapT
    cols = Dynamic{M.CCol}[Dynamic{M.CCol}(Main.CPlainCol([1.0])), Dynamic{M.CCol}(Main.CPoolCol([1, 2]))]
    @test [Base.invokelatest(M.ckind, c) for c in cols] == [:plain, :pooled]   # selected by the held object
    @test_throws TraitBoundError Base.invokelatest(M.ckind, Dynamic{M.CShape}(Main.CCircle(1.0)))
    g = Dynamic{Callable{Tuple{Int}, Int}}(x -> 2x)
    @test Base.invokelatest(M.sigf, g, 1.5) == 3.0                             # a method at the new signature
    @test_throws TraitBoundError Base.invokelatest(M.sigs, g, "a")             # none with a result of that type
    @test Base.invokelatest(M.ccount, iseven, [1, 2, 3, 4]) == 2
    @test Base.invokelatest(M.ccount, x -> x > 1.5, [1.0, 2.0, 3.0]) == 2
end
