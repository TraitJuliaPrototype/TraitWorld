# Results like the input (note "Results like the input"): constructor operations return
# `Self`, a function declared `::Like{t}` returns a value of the caller's type built by the
# conformance's inverse (the new value for a type that implements the operations, the user's
# object with fields replaced otherwise), `withfields` replaces declared fields, a Dynamic in
# gives a Dynamic out, and a sibling implementing type rebuilds the user's type at another
# parameter (a solver's state in Float32 from one in Float64).
# Runs inside runtests.jl, or alone: julia --project=. test/like.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module LikeLib
    using TraitWorld
    
    @trait ColTable{R} begin
        ncols(r::R)::Int
        col(r::R, i::Int)::Vector{Float64}
        withcols(r::R, cs::Vector{Vector{Float64}})::R      # a constructor operation
    end
    @implement ColTable{Vector{Vector{Float64}}} begin
        ncols(r) = length(r)
        col(r, i) = r[i]
        withcols(r, cs) = cs
    end

    colmap(f::Callable{Tuple{Float64}, Float64}, t::ColTable)::Like{t} =
        withcols(t, [map(f, col(t, i)) for i in 1:ncols(t)])
    function earlyout(t::ColTable, keep::Bool)::Like{t}     # `return` inside a Like body
        keep && return withcols(t, [col(t, i) for i in 1:ncols(t)])
        withcols(t, Vector{Float64}[])
    end
    doubled(t::ColTable) = ncols(t) * 2
    keeptable(t::ColTable) = Dynamic{ColTable}(t)

    @trait SVec{T, R} begin
        T = eltype(R)
        nel(r::R)::Int
        getel(r::R, i::Int)::T
    end
    @implement SVec{T, Vector{T}} where {T <: Real} begin
        nel(r) = length(r)
        getel(r, i) = r[i]
    end
    tof32(s::SVec)::Like{s} = Float32[getel(s, i) for i in 1:nel(s)]   # a sibling implementing type

    @trait LRec{U} begin                     # fields only: results like the input replace fields
        @const u::U
        @const label::String
    end
    shifted(r::LRec{Vector{Float64}})::Like{r} = withfields(r; u = r.u .+ 1.0)
    end

    @trait_module module LikeBad
    using TraitWorld
    using ..LikeLib: ColTable
    export leak
    leak(t::ColTable) = t                                      # no Like: a trait object to ordinary code
    end
end)

toplevel(quote
    struct LMeas; cols::Vector{Vector{Float64}}; label::String; end
    mutable struct LMeasM; cols::Vector{Vector{Float64}}; label::String; end
    @implement LikeLib.ColTable LMeas by cols                   # forwarding: rebuilt with the field replaced
    @implement LikeLib.ColTable LMeasM by cols                   # forwarding: rebuilt with the field replaced

    struct LOwn; cs::Vector{Vector{Float64}}; end               # implements the operations itself
    @implement LikeLib.ColTable LOwn begin
        ncols(r) = length(r.cs)
        col(r, i) = r.cs[i]
        withcols(r, cs) = LOwn(cs)
    end
    struct LBox; u::Vector{Float64}; label::String; end
    @implement LikeLib.LRec LBox

    struct LSeries{T}; data::Vector{T}; end
    @implement LikeLib.SVec LSeries{Float64} by data           # forwarding, one conformance per parameter value
    @implement LikeLib.SVec LSeries{Float32} by data           # (forwarding for the whole family: not yet)
end)

@testset "Results like the input" begin
    L = Main.LikeLib
    m = Main.LMeas([[1.0, 2.0], [3.0]], "run 1")
    r = L.colmap(x -> 2x, m)
    @test r isa Main.LMeas && r.cols == [[2.0, 4.0], [6.0]] && r.label == "run 1"
    @test m.cols == [[1.0, 2.0], [3.0]]                        # the input is untouched
    v = L.colmap(x -> x + 1, [[1.0]])                          # its own representation: the identity
    @test v == [[2.0]] && v isa Vector{Vector{Float64}}
    @test L.earlyout(m, true).cols == m.cols && isempty(L.earlyout(m, false).cols)
    @test L.doubled(m) == 4
    r2 = L.colmap(x -> 2x, Main.LOwn([[1.0]]))                 # the type implements the operations: the new value
    @test r2 isa Main.LOwn && r2.cs == [[2.0]]
    b = L.shifted(Main.LBox([1.0, 2.0], "b"))                  # withfields: the user's object with `u` replaced
    @test b isa Main.LBox && b.u == [2.0, 3.0] && b.label == "b"
    e = try toplevel(quote                                      # a computed projection is refused at the conformance
        struct LRamp; n::Int; end
        @implement LikeLib.ColTable LRamp project(r) = [collect(1.0:r.n)]
    end); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    @test e isa ImplementError && occursin("computes a value", sprint(showerror, e))
    d = L.keeptable(m)                                         # an immutable type, kept whole
    dr = L.colmap(x -> -x, d)                                  # a Dynamic in, a Dynamic out
    @test L.colmap(x -> -x, L.keeptable(Main.LMeasM([[1.0, 2.0], [3.0]], "run 1"))) isa Dynamic{L.ColTable}   # and a mutable one
    @test dr isa Dynamic{L.ColTable} && L.col(dr, 1) == [-1.0, -2.0]
    dw = L.withcols(d, [[9.0]])                                # a constructor operation on a Dynamic
    @test dw isa Dynamic{L.ColTable} && L.ncols(dw) == 1 && L.col(dw, 1) == [9.0]
    s32 = L.tof32(Main.LSeries([1.0, 2.5]))                     # Series{Float64} in, Series{Float32} out
    @test s32 isa Main.LSeries{Float32} && s32.data == Float32[1.0, 2.5]
    @test L.tof32([1.0, 2.0]) isa Vector{Float32}
    @test_throws TraitUseError Main.LikeBad.leak(m)
    @test isempty(check_definitions(L))
end

@testset "a result like the input, typed for a caller that knows the type" begin
    ft(x::Main.LSeries{Float64}) = Main.LikeLib.tof32(x)
    fm(x::Main.LMeas) = Main.LikeLib.earlyout(x, true)
    fo(x::Main.LOwn) = Main.LikeLib.earlyout(x, true)
    fb(x::Main.LBox) = Main.LikeLib.shifted(x)
    @test ft(Main.LSeries([1.0, 2.5])).data == Float32[1.0, 2.5]
    @test Base.return_types(ft, (Main.LSeries{Float64},)) == [Main.LSeries{Float32}]
    @test fm(Main.LMeas([[-1.0]], "a")).cols == [[-1.0]]
    @test Base.return_types(fm, (Main.LMeas,)) == [Main.LMeas]
    @test fo(Main.LOwn([[-2.0]])).cs == [[-2.0]]
    @test Base.return_types(fo, (Main.LOwn,)) == [Main.LOwn]
    @test fb(Main.LBox([1.0], "b")).u == [2.0]
    @test Base.return_types(fb, (Main.LBox,)) == [Main.LBox]
end
