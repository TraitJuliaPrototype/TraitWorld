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
    hasmass(c::CCol) = true
    hasmass(x) = false                          # the fallback: also for a kept value of another trait (open issue 127)
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
    # a kept value whose object conforms to none of the bounds' traits reaches the fallback, as its object would
    # (traits reference §5.5, §6.5; open issue 127): here none, so `MethodError`, as for a plain `CCircle`
    @test_throws MethodError Base.invokelatest(M.ckind, Dynamic{M.CShape}(Main.CCircle(1.0)))
    @test_throws MethodError Base.invokelatest(M.ckind, Main.CCircle(1.0))
    for k in (Dynamic{M.CShape}(Main.CCircle(1.0)), Compiled{M.CShape}(Main.CCircle(1.0)), Kept{M.CShape}(Main.CCircle(1.0)))
        @test Base.invokelatest(M.hasmass, k) === false
    end
    @test Base.invokelatest(M.hasmass, Main.CCircle(1.0)) === false
    @test Base.invokelatest(M.hasmass, Dynamic{M.CCol}(Main.CPlainCol([1.0]))) === true
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
        # an ordinary vararg (lowering L-46): plain or after a bound, `@nospecialize` kept on it
        run4(a::Alg, xs...) = order(a) + length(xs)
        run5(a::Alg, @nospecialize(xs...)) = order(a) + length(xs)
        run6(a::Alg, @nospecialize(xs::Int...)) = order(a) + sum(xs; init = 0)
        plainva(@nospecialize(xs...)) = length(xs)
        end
    end)
    M = Base.invokelatest(getglobal, Main, :MacroWrapped)
    g(s) = Base.invokelatest(getglobal, M, s)
    a = Base.invokelatest(g(:A1))
    @test Base.invokelatest(g(:run1), [1, 2], a) == 6
    @test Base.invokelatest(g(:run2), a, [1.0, 2.0]) == 7.0
    @test Base.invokelatest(g(:run3), (1, 2, 3), a) == 12
    @test_throws MethodError Base.invokelatest(g(:run1), [1], :notanalg)      # the bound, not a plain annotation
    @test Base.invokelatest(g(:run4), a, 1, "x") == 6
    @test Base.invokelatest(g(:run5), a, 1, "x", :y) == 7
    @test Base.invokelatest(g(:run6), a, 1, 2) == 7
    @test Base.invokelatest(g(:plainva), 1, 2) == 2
    @test all(m -> m.nospecialize & 2 != 0, methods(g(:run5)))                 # the vararg, on the entry and the worker
    @test all(m -> m.nospecialize & 1 != 0, methods(g(:plainva)))
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

@testset "a bound that opens its value: Opened{X} (traits §6.4, open issue 98)" begin
    toplevel(quote
        @trait_module module OpenedBound
        using TraitWorld
        export OSh, oarea, OSq, OCirc, total_open, total_plain
        @trait OSh begin
            oarea(s::OSh)::Float64
        end
        struct OSq; a::Float64; end
        struct OCirc; r::Float64; end
        @implement OSh OSq begin oarea(s) = s.a^2 end
        @implement OSh OCirc begin oarea(s) = 3.0 * s.r^2 end
        total_open(s::Opened{OSh})::Float64 = oarea(s) + oarea(s)       # the callee opens its value
        total_plain(s::OSh)::Float64 = oarea(s) + oarea(s)              # a Dynamic value stays Dynamic
        end
    end)
    M = Base.invokelatest(getglobal, Main, :OpenedBound)
    g(s) = Base.invokelatest(getglobal, M, s)
    OSh, OSq, OCirc = g(:OSh), g(:OSq), g(:OCirc)
    topen, tplain = g(:total_open), g(:total_plain)
    shapes = Dynamic{OSh}[Dynamic{OSh}(OSq(2.0)), Dynamic{OSh}(OCirc(1.0))]
    @test Base.invokelatest(topen, shapes[1]) == 8.0 && Base.invokelatest(topen, shapes[2]) == 6.0
    @test Base.invokelatest(topen, OSq(3.0)) == 18.0                                   # a plain value
    @test Base.invokelatest(topen, compiled_for(OSq(3.0))) == 18.0                     # a caller's cast as well
    @test Base.invokelatest(topen, with_dynamic(OSq(3.0))) == 18.0
    @test Base.invokelatest(tplain, shapes[1]) == 8.0
    # the Dynamic value ran code compiled for its key: a worker specialization names the square's type
    specs(f) = [string(mi.specTypes) for m in methods(f) for mi in Base.specializations(m) if mi isa Core.MethodInstance]
    @test any(s -> occursin("OSq", s), specs(topen))
    @test !any(s -> occursin("OSq", s) && !occursin("CompiledFor", s), specs(tplain))  # Dynamic: the erased key
    # casts of cast marks: the same attribute unchanged, the later cast wins (traits §6.4)
    x = OSq(1.0)
    @test compiled_for(compiled_for(x)) === compiled_for(x)
    @test with_dynamic(with_dynamic(x)) === with_dynamic(x)
    @test compiled_for(with_dynamic(x)) === compiled_for(x)
    @test with_dynamic(compiled_for(x)) === with_dynamic(x)
end

@testset "rewrap: a changed function keeps its attribute (traits §6.4)" begin
    f(x) = 2x
    h = rewrap(g -> (y -> g(y) + 1), compiled_for(f))
    @test h isa TraitWorld.CompiledFor && getfield(h, :x)(3) == 7
    h = rewrap(g -> (y -> g(y) + 1), with_dynamic(f))
    @test h isa TraitWorld.WithDynamic && getfield(h, :x)(3) == 7
    @test rewrap(g -> (y -> g(y) + 1), f)(3) == 7                       # a plain value: g(f)
    S = Callable{Tuple{Int}, Int}
    for (k, attr) in ((Kept{S}(compiled_for(f)), TraitWorld.CompiledFor), (Kept{S}(with_dynamic(f)), TraitWorld.WithDynamic),
                      (Dynamic{S}(f), TraitWorld.WithDynamic), (Compiled{S}(f), TraitWorld.CompiledFor))
        h = rewrap(g -> (y -> g(y) + 1), k)
        @test h isa attr && getfield(h, :x)(3) == 7                                # the user's function, changed
    end
end
