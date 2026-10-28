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
    # a `Dynamic` bound whose parameter a `where` variable fixes (traits reference §5.1)
    @trait CCells{T} begin
        T = eltype(Self)
        ccellat(c::CCells{T}, i::Int)::T
    end
    @implement CCells A where {A <: AbstractVector} begin
        ccellat(c, i) = c[i]
    end
    cfirst(c::Dynamic{CCells{T}}) where {T} = (ccellat(c, 1), T)
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
    @test Base.invokelatest(M.cfirst, [1, 2]) == (1, Int) && Base.invokelatest(M.cfirst, ["a"]) == ("a", String)
end

@testset "an open result type (traits reference §5.8)" begin
    toplevel(quote
        @trait_module module OpenRes
        using TraitWorld
        @trait Col{T} begin
            T = eltype(Self)
            nr(c::Col)::Int
            at(c::Col{T}, i::Int)::T
        end
        @implement Col A where {A <: AbstractVector} begin
            nr(c) = length(c)::Int
            at(c, i) = c[i]::eltype(c)
        end
        function byrow(f::Callable{Tuple{T}, S}, c::Col{T}) where {T, S}
            out = Vector{S}(undef, nr(c))
            for i in 1:nr(c); out[i] = f(at(c, i)); end
            return out
        end
        mapone(f::Callable{Tuple{Float64}, S}, x::Float64) where {S} = f(x)
        end
    end)
    M = Base.invokelatest(getglobal, Main, :OpenRes)
    g(s) = Base.invokelatest(getglobal, M, s)
    @test Base.invokelatest(g(:byrow), x -> 2x, [1, 2, 3]) == [2, 4, 6]
    r = Base.invokelatest(g(:byrow), string, [1.5, 2.5])
    @test r isa Vector{String} && r == ["1.5", "2.5"]
    @test Base.invokelatest(g(:byrow), compiled_for(x -> x > 1), [1, 2, 3]) == [false, true, true]
    @test Base.invokelatest(g(:mapone), sqrt, 4.0) === 2.0
    @test Base.invokelatest(g(:mapone), x -> round(Int, x), 2.6) === 3
    @test_throws MethodError Base.invokelatest(g(:mapone), (x::Int) -> x, 1.0)    # no method at the declared argument types
end

@testset "a family implemented with methods by the owner of its members, for another module's trait (traits §4.7, §10.1)" begin
    toplevel(quote
        @trait_module module FamOwnerCore
        using TraitWorld
        export Pts, npts, px
        @trait Pts begin
            npts(p::Pts)::Int
            px(p::Pts, i::Int)::Float64
        end
        total(p::Pts) = sum(px(p, i) for i in 1:npts(p))
        end
        module FamOwnerUser                                  # owns `Pt`, so the family of vectors of `Pt`
        using TraitWorld
        using ..FamOwnerCore
        struct Pt; x::Float64; end
        @implement FamOwnerCore.Pts V where {V <: AbstractVector{Pt}} begin
            npts(p) = length(p)
            px(p, i) = p[i].x
        end
        end
    end)
    C = Base.invokelatest(getglobal, Main, :FamOwnerCore); U = Base.invokelatest(getglobal, Main, :FamOwnerUser)
    pt = Base.invokelatest(getglobal, U, :Pt)
    @test Base.invokelatest(getglobal(C, :total), [pt(1.0), pt(2.5)]) == 3.5
end

@testset "a bounded function inside another macro, and `@nospecialize` on its ordinary arguments (found by SciML's move 3)" begin
    toplevel(quote
        @trait_module module MacroWrapped
        using TraitWorld
        export Alg, run1, run2, run3
        @trait Alg begin
            order(a::Alg)::Int
        end
        struct A1 end
        @implement Alg A1 begin
            order(a) = 4
        end
        "a docstring above another macro"
        Base.@nospecializeinfer function run1(@nospecialize(prob), a::Alg)
            return order(a) + length(prob)
        end
        Base.@nospecializeinfer run2(a::Alg, @nospecialize(x::AbstractVector)) = order(a) + sum(x)
        run3(@nospecialize(p), a::Alg) = order(a) * length(p)
        end
    end)
    M = Base.invokelatest(getglobal, Main, :MacroWrapped)
    g(s) = Base.invokelatest(getglobal, M, s)
    a = Base.invokelatest(g(:A1))
    @test Base.invokelatest(g(:run1), [1, 2], a) == 6
    @test Base.invokelatest(g(:run2), a, [1.0, 2.0]) == 7.0
    @test Base.invokelatest(g(:run3), (1, 2, 3), a) == 12
    @test_throws MethodError Base.invokelatest(g(:run1), [1], :notanalg)      # the bound, not a plain annotation
end

@testset "a bounded function's declared result, seen by plain inference at its entry (found by SciML's move 4)" begin
    toplevel(quote
        @trait_module module EntryResult
        using TraitWorld
        export Ix, idx, lookup
        @trait Ix begin
            idx(i::Ix, s::Symbol)::Union{Nothing, Int}
        end
        struct Names; v::Vector{Symbol}; end
        @implement Ix Names begin
            idx(i, s) = findfirst(==(s), i.v)
        end
        lookup(i::Dynamic{Ix}, s::Symbol)::Union{Nothing, Int} = idx(i, s)
        asix(i::Ix)::Dynamic{Ix} = Dynamic{Ix}(i)                     # a kept form declared as the result
        end
    end)
    M = Base.invokelatest(getglobal, Main, :EntryResult)
    g(s) = Base.invokelatest(getglobal, M, s)
    @test Base.invokelatest(g(:lookup), Base.invokelatest(g(:Names), [:a, :b]), :b) == 2
    @test Base.invokelatest(Base.return_types, g(:lookup), (Dynamic{g(:Ix)}, Symbol)) == Any[Union{Nothing, Int}]
    # a declared `Dynamic{X}` result reaches a plain caller too (open issue 100)
    @test Base.invokelatest(g(:asix), Base.invokelatest(g(:Names), [:a])) isa Dynamic{g(:Ix)}
    @test all(==(Dynamic{g(:Ix)}), Base.invokelatest(Base.return_types, g(:asix), (Any,)))
end
