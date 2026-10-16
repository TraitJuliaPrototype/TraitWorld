# Results like the input (note "Results like the input"): constructor operations return the
# representation, a function declared `::Like{t}` returns a value of the caller's type built
# by the conformance's inverse (identity, field copy, written `unproject`), a Dynamic in gives
# a Dynamic out, and a sibling representation rebuilds the user's type at another parameter
# (a solver's state in Float32 from one in Float64).
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
    tof32(s::SVec)::Like{s} = Float32[getel(s, i) for i in 1:nel(s)]   # a sibling representation
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
    @implement LikeLib.ColTable LMeas project(m) = m.cols            # a field projection: copied with the field replaced

    struct LRamp; n::Int; end                                   # computed, without an inverse
    @implement LikeLib.ColTable LRamp project(r) = [collect(1.0:r.n)]

    struct LRamp2; n::Int; end                                  # computed, with an inverse
    @implement LikeLib.ColTable LRamp2 begin
        project(r) = [collect(1.0:r.n)]
        unproject(r, cs) = LRamp2(length(cs[1]))
    end

    struct LSeries{T}; data::Vector{T}; end
    @implement LikeLib.SVec LSeries{Float64} project(s) = s.data   # field projections, one per parameter value
    @implement LikeLib.SVec LSeries{Float32} project(s) = s.data   # (a projection for the whole family: not yet)
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
    @test_throws TraitBoundError L.colmap(x -> x, Main.LRamp(3))   # no inverse: refused, naming the conformance
    e = try L.colmap(x -> x, Main.LRamp(3)); nothing catch err; err end
    @test occursin("unproject", sprint(showerror, e))
    r2 = L.colmap(x -> x, Main.LRamp2(3))
    @test r2 isa Main.LRamp2 && r2.n == 3
    d = L.keeptable(m)
    dr = L.colmap(x -> -x, d)                                  # a Dynamic in, a Dynamic out
    @test dr isa Dynamic{L.ColTable} && L.col(dr, 1) == [-1.0, -2.0]
    dw = L.withcols(d, [[9.0]])                                # a constructor operation on a Dynamic
    @test dw isa Dynamic{L.ColTable} && L.ncols(dw) == 1 && L.col(dw, 1) == [9.0]
    s32 = L.tof32(Main.LSeries([1.0, 2.5]))                     # Series{Float64} in, Series{Float32} out
    @test s32 isa Main.LSeries{Float32} && s32.data == Float32[1.0, 2.5]
    @test L.tof32([1.0, 2.0]) isa Vector{Float32}
    @test_throws TraitUseError Main.LikeBad.leak(m)
    @test isempty(check_definitions(L))
end
