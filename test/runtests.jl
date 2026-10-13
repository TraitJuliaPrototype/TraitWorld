using Test, TraitWorld

"Evaluate the statements of `ex` at top level in Main (modules and structs allowed)."
toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex)

"Evaluate `ex` like `toplevel` and return the exception it throws (unwrapping LoadError), or `nothing`."
function thrown(ex)
    try
        toplevel(ex)
        return nothing
    catch e
        while e isa LoadError
            e = e.error
        end
        return e
    end
end

# --- the note's example -----------------------------------------------------------
@trait_module module Columns
using TraitWorld
export ColTable, ncols, col, value, colmean, colrange, meandiff, total, describe, colmap, colsum
@trait ColTable{R} begin
    ncols(r::R)::Int
    col(r::R, i::Int)::Vector{Float64}
    value(r::R, i::Int, j::Int)::Float64 = col(r, i)[j]
end
@implement ColTable{Vector{Vector{Float64}}} begin
    ncols(r) = length(r)
    col(r, i) = r[i]
end
@implement ColTable{Matrix{Float64}} begin
    ncols(r) = size(r, 2)
    col(r, i) = r[:, i]
end
colmean(t::ColTable, i::Int) = (c = col(t, i); sum(c) / length(c))
colrange(t::ColTable, i::Int) = (c = col(t, i); maximum(c) - minimum(c))
meandiff(a::ColTable, b::ColTable, i::Int) = colmean(a, i) - colmean(b, i)
total(t::ColTable, len::Int) = sum(value(t, i, j) for i in 1:ncols(t), j in 1:len)
describe(v::Vector{Float64}) = "a vector"
describe(m::AbstractMatrix) = "a matrix"
describe(t::ColTable) = "a table with $(ncols(t)) columns"
describe(x) = "something else"
colmap(f::Callable{Tuple{Float64},Float64}, t::ColTable, i::Int) = map(f, col(t, i))
colsum(@specialize(f::Callable{Tuple{Float64},Float64}), t::ColTable, i::Int) = sum(f, col(t, i))
end
using .Columns

struct Measurements; series::Vector{Vector{Float64}}; end
@implement ColTable Measurements project(t) = t.series
struct Ramp; base::Vector{Float64}; n::Int; end
@implement ColTable{Ramp} begin
    ncols(r) = r.n
    col(r, i) = r.base .* i
end
struct Reversed; cols::Vector{Vector{Float64}}; end
@implement ColTable Reversed dynamic begin
    project(t) = t.cols
    ncols(r) = length(r)
    col(r, i) = r[end - i + 1]
end

@testset "M1: the note's example" begin
    m, r = Measurements([[1.0, 2.0], [3.0, 5.0]]), Ramp([1.0, 2.0], 2)
    @test colmean(m, 1) == 1.5
    @test colmean(r, 1) == 1.5
    @test colmean(Reversed([[1.0, 2.0], [3.0, 5.0]]), 1) == 4.0
    @test meandiff(m, r, 1) == 0.0
    @test colmean([[1.0, 3.0]], 1) == 2.0                    # a representation is its own projection
    @test colrange([1.0 5.0; 3.0 2.0], 1) == 2.0
    # a default reaches the dynamic operations, never the representation's implementation
    @test value(TObj((TraitWorld.View{ColTable}(TraitWorld.proj_witness(ColTable, Reversed,
                     TraitWorld._proj(ColTable, Reversed)), [[1.0], [2.0]]),)), 1, 1) == 2.0
    @test total(Reversed([[1.0, 2.0], [10.0, 20.0]]), 2) == total([[1.0, 2.0], [10.0, 20.0]], 2)
    @test_throws MethodError colmean(42, 1)                  # no projection: as in plain Julia
end

@testset "M1: rule 3 and escapes, reported with their lines" begin
    toplevel(quote
        @trait_module module Rows
        using TraitWorld
        export RowTable, firstrow
        @trait RowTable{R} begin
            nrows(r::R)::Int
            row(r::R, i::Int)::Vector{Float64}
        end
        @implement RowTable{Matrix{Float64}} begin
            nrows(r) = size(r, 1)
            row(r, i) = r[i, :]
        end
        firstrow(t::RowTable) = row(t, 1)
        end
        using .Rows
        @trait_module module Bad
        using TraitWorld, ..Columns, ..Rows
        bad_rule3(t::ColTable) = firstrow(t)
        bad_ordinary(t::ColTable) = sum(t)
        bad_field(t::ColTable) = t.views
        bad_typeof(t::ColTable) = typeof(t)
        helper(t::ColTable) = colmean(t, 1) + bad_ordinary(t)
        good(t::(ColTable, RowTable)) = (colmean(t, 1), firstrow(t))
        end
    end)
    m = Measurements([[1.0, 2.0]])
    msg(f) = try f(m); "" catch e; sprint(showerror, e) end
    @test occursin("rule 3", msg(Main.Bad.bad_rule3)) && occursin("runtests.jl", msg(Main.Bad.bad_rule3))
    @test occursin("`sum`, an ordinary function", msg(Main.Bad.bad_ordinary))
    @test occursin("t.field", msg(Main.Bad.bad_field))
    @test occursin("typeof(t)", msg(Main.Bad.bad_typeof))
    @test occursin("`sum`", msg(Main.Bad.helper))        # found through the worker it calls
    toplevel(quote
        struct Both; cols::Vector{Vector{Float64}}; mat::Matrix{Float64}; end
        @implement ColTable Both project(t) = t.cols
        @implement Main.Rows.RowTable Both project(t) = t.mat
    end)
    @test Main.Bad.good(Main.Both([[1.0, 3.0]], [1.0 2.0; 3.0 4.0])) == (2.0, [1.0, 2.0])
end

@testset "M1: ownership (rule 5) and layering (rule 1)" begin
    # implementing a foreign trait for a foreign representation
    e = thrown(:(@implement ColTable{Vector{Int}} begin ncols(r) = 1; col(r, i) = [1.0] end))
    @test e isa ImplementError       # the session owns neither the trait nor Vector{Int}
    e = thrown(quote
        module Stranger
        using TraitWorld, ..Columns
        @implement ColTable{Vector{Float32}} begin ncols(r) = 1; col(r, i) = [1.0] end
        end
    end)
    @test e isa ImplementError && occursin("rule 5", sprint(showerror, e))
    # an existing function implemented for a foreign type: rejected before anything is defined
    e = thrown(quote
        @trait_module module SizeTrait
        using TraitWorld
        @trait Sized{R} begin Base.size(r::R)::Tuple{Int,Int} end
        @implement Sized{Vector{Float32}} begin size(r) = (length(r), 1) end
        end
    end)
    @test e isa ImplementError
    @test which(size, (Vector{Float32},)).module === Base
    # a piratical method in a trait module
    e = thrown(quote
        @trait_module module PirateMod
        using TraitWorld
        Base.sum(x::Vector{Int8}) = 0
        end
    end)
    @test e isa OwnershipError
    # a Union with a foreign type is no way around rule 5
    e = thrown(quote
        @trait_module module UnionMod
        using TraitWorld
        struct Mine end
        Base.length(x::Union{Mine,Int8}) = 0
        end
    end)
    @test e isa OwnershipError
    # layering: a trait module imports an ordinary module
    toplevel(:(module Plain; f() = 1; end))
    e = thrown(quote
        @trait_module module BadLayer
        using TraitWorld, ..Plain
        end
    end)
    @test e isa LayeringError
end

@testset "M1: implementations are checked when defined" begin
    e = thrown(quote
        struct WrongRet; n::Int; end
        @implement ColTable{WrongRet} begin
            ncols(r) = r.n
            col(r, i) = [1, 2]            # Vector{Int}, declared Vector{Float64}
        end
    end)
    @test e isa ImplementError && occursin("declared", sprint(showerror, e))
    e = thrown(quote
        struct Abstr; x::Real; end
        @implement ColTable{Abstr} begin ncols(r) = 1; col(r, i) = [1.0] end
    end)
    @test e isa ImplementError && occursin("deeply concrete", sprint(showerror, e))
    e = thrown(quote
        struct NoInfer; x::Vector{Vector{Float64}}; end
        @implement ColTable NoInfer project(t) = rand() > 2 ? t.x : nothing
    end)
    @test e isa ImplementError
    e = thrown(:(@implement ColTable{Vector{Vector{Int}}} begin ncols(r) = 1 end))
    @test e isa ErrorException && occursin("needs the operation `col`", e.msg)
end

@testset "dispatch: types first, then traits; fallback" begin
    @test describe([1.0]) == "a vector"
    @test describe([1.0 2.0]) == "a matrix"            # Matrix{Float64} is a ColTable, but the type method comes first
    @test describe([[1.0], [2.0]]) == "a table with 2 columns"
    @test describe(Measurements([[1.0]])) == "a table with 1 columns"
    @test describe(42) == "something else"
end

@testset "Callable" begin
    @test colmap(x -> 2x, [[1.0, 2.0]], 1) == [2.0, 4.0]          # erased
    @test colsum(abs2, [[1.0, 2.0]], 1) == 5.0                     # Base's function: always specialized
    @test colsum(x -> x + 1, [[1.0, 2.0]], 1) == 5.0               # @specialize
    @test_throws TypeError colmap(x -> 1, [[1.0, 2.0]], 1)       # a result of another type: an error, not widening
    e = TraitWorld.enter_callable(Tuple{Float64}, Float64, false, x -> x)
    @test e.f isa TraitWorld.Erased
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, false, sin).f === sin
end

@testset "closures capturing a trait object are checked" begin
    toplevel(quote
        @trait_module module Clo
        using TraitWorld, ..Columns
        ok(t::ColTable) = sum(x -> x * ncols(t), col(t, 1))
        bad(t::ColTable) = map(i -> sum(t), 1:2)
        end
    end)
    @test Main.Clo.ok([[1.0, 2.0]]) == 3.0
    @test_throws TraitUseError Main.Clo.bad([[1.0, 2.0]])
end

# --- M2: capability traits over Base's functions, families, generic implementations ---------
@trait_module module Caps
using TraitWorld
export HasLength, Iterable, Indexable
@trait HasLength{R} begin
    Base.length(r::R)::Int
end
@trait Iterable{R} begin
    Base.iterate(r::R)::Union{Nothing,Tuple{eltype(R),Any}}
    Base.iterate(r::R, s)::Union{Nothing,Tuple{eltype(R),Any}}
end
@trait Indexable{R} <: HasLength begin
    Base.getindex(r::R, i::Int)::eltype(R)
end
@implement HasLength{A} where {A <: AbstractArray}
@implement Iterable{A} where {A <: AbstractArray}
@implement Indexable{A} where {A <: AbstractVector}
@implement HasLength{T} where {T <: Tuple}
@implement Indexable{T} where {T <: Tuple}
end
using .Caps
@trait_module module Gen
using TraitWorld, ..Caps
export GTable, gcol, gn, gfirst, gmean, gsum
@trait GTable{R} begin
    gn(r::R)::Int
    gcol(r::R, i::Int)::Vector{Float64}
    gfirst(r::R)::Vector{Float64} = gcol(r, 1)
end
@implement GTable{R} where {R: Indexable, eltype(R) == Vector{Float64}} begin
    gn(r) = length(r)
    gcol(r, i) = r[i]
end
@implement GTable{Matrix{Float64}} begin
    gn(r) = size(r, 2)
    gcol(r, i) = r[:, i]
end
gmean(t::GTable) = sum(gfirst(t)) / length(gfirst(t))
gsum(t::Iterable) = (s = 0.0; for x in t; s += x; end; s)      # `for` over a trait object: iterate is an operation
first_of(t::Indexable) = t[1]
end
using .Gen
struct Wrapped; v::Vector{Vector{Float64}}; end
@implement HasLength{Wrapped} begin length(r) = length(r.v) end
@implement Indexable{Wrapped} begin getindex(r, i) = r.v[i] end
Base.eltype(::Type{Wrapped}) = Vector{Float64}
struct Broken <: AbstractVector{Float64}; n::Int; end
Base.size(b::Broken) = (b.n,)

@testset "M2: Base capability traits and generic implementations" begin
    W = TraitWorld.witness
    @test W(GTable, Matrix{Float64}) isa TraitWorld.Impl                      # specific beats generic
    @test W(GTable, Vector{Vector{Float64}}) isa TraitWorld.Generic
    @test W(GTable, Tuple{Vector{Float64},Vector{Float64}}) isa TraitWorld.Generic
    @test W(GTable, Wrapped) isa TraitWorld.Generic                         # a user's Indexable becomes a GTable
    @test W(GTable, Vector{Int}) === nothing                                 # the predicate on eltype
    @test W(Indexable, Int) === nothing && hasmethod(getindex, Tuple{Int,Int})   # accidental conformance refused
    @test gmean([[1.0, 3.0]]) == 2.0
    @test gmean(([2.0, 4.0], [0.0])) == 3.0
    @test gmean(Wrapped([[5.0, 7.0]])) == 6.0
    @test gmean([1.0 9.0; 3.0 9.0]) == 2.0
    @test gsum([1.0, 2.0, 3.5]) == 6.5                                      # Iterable with two arities of iterate
    @test_throws MethodError gmean(42)
    # a subtype that breaks AbstractVector's contract: a warning, and the same error as plain Julia
    e_plain = try Broken(2)[1] catch e; e end
    e_trait = (@test_logs (:warn, r"does not conform") match_mode=:any (try Gen.first_of(Broken(2)) catch e; e end))
    @test typeof(e_plain) === typeof(e_trait) && sprint(showerror, e_plain) == sprint(showerror, e_trait)
    @test isempty(TraitWorld.conformance_problems(Iterable, Vector{Float64}, (:iterate,)))
    @test !isempty(TraitWorld.conformance_problems(Indexable, Broken, (:getindex,)))
end

# --- M3: several bounds, several views; joint projections; rule 4 --------------------------------
@trait_module module Views
using TraitWorld, ..Columns, ..Rows
export Table2, overview, overview2, ColStore, setcol!, normalize!
@trait Table2{R} <: (ColTable, RowTable)
overview(t::(ColTable, RowTable)) = (colmean(t, 1), firstrow(t))
overview2(t::Table2) = (colmean(t, 1), firstrow(t))
@trait ColStore{R} begin
    @mutating setcol!(r::R, i::Int, v::Vector{Float64})::Nothing
end
@implement ColStore{Vector{Vector{Float64}}} begin setcol!(r, i, v) = (r[i] = v; nothing) end
normalize!(t::(ColTable, ColStore), i::Int) = (c = col(t, i); setcol!(t, i, c ./ sum(c)); nothing)
end
using .Views
const PROJ = Ref(0)
struct Sep3; cols::Vector{Vector{Float64}}; rows::Matrix{Float64}; end
@implement ColTable Sep3 project(t) = (PROJ[] += 1; t.cols)
@implement Main.Rows.RowTable Sep3 project(t) = (PROJ[] += 1; t.rows)
struct Joint3; m::Matrix{Float64}; end
@implement (ColTable, Main.Rows.RowTable) Joint3 project(t) = (PROJ[] += 1; t.m)
struct Live3; cols::Vector{Vector{Float64}}; end
@implement (ColTable, ColStore) Live3 project(t) = t.cols

@testset "M3: views and joint projections" begin
    m = [1.0 2.0; 3.0 4.0]
    PROJ[] = 0; @test overview(Sep3([[1.0, 3.0], [2.0, 4.0]], m)) == (2.0, [1.0, 2.0]); @test PROJ[] == 2
    PROJ[] = 0; @test overview(Joint3(m)) == (2.0, [1.0, 2.0]); @test PROJ[] == 1
    @test overview2(Joint3(m)) == overview(m)
    x = Live3([[1.0, 3.0]]); normalize!(x, 1); @test x.cols[1] == [0.25, 0.75]
    toplevel(:(struct Frozen3; cols::Vector{Vector{Float64}}; end))
    e = thrown(:(@implement ColStore Frozen3 copies project(t) = deepcopy(t.cols)))
    @test e isa ImplementError && occursin("rule 4", sprint(showerror, e))
    @test thrown(:(@implement ColTable Frozen3 copies project(t) = deepcopy(t.cols))) === nothing
end
