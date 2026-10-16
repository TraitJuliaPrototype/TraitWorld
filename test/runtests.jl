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
colsum(f::Callable{Tuple{Float64},Float64,CompiledCall}, t::ColTable, i::Int) = sum(f, col(t, i))
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

@testset "M1: rule 2 and escapes, reported with their lines" begin
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
    @test occursin("rule 2", msg(Main.Bad.bad_rule3)) && occursin("runtests.jl", msg(Main.Bad.bad_rule3))
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

@testset "M1: ownership (rule 3) and layering (rule 1)" begin
    # implementing a foreign trait for a foreign representation
    e = thrown(:(@implement ColTable{Vector{Int}} begin ncols(r) = 1; col(r, i) = [1.0] end))
    @test e isa ImplementError       # the session owns neither the trait nor Vector{Int}
    e = thrown(quote
        module Stranger
        using TraitWorld, ..Columns
        @implement ColTable{Vector{Float32}} begin ncols(r) = 1; col(r, i) = [1.0] end
        end
    end)
    @test e isa ImplementError && occursin("rule 3", sprint(showerror, e))
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
    # a Union with a foreign type is no way around rule 3
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
    @test colsum(x -> x + 1, [[1.0, 2.0]], 1) == 5.0               # the bound's default: CompiledCall
    @test_throws TypeError colmap(x -> 1, [[1.0, 2.0]], 1)       # a result of another type: an error, not widening
    e = TraitWorld.enter_callable(Tuple{Float64}, Float64, nothing, x -> x)
    @test e.f isa TraitWorld.Erased
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, nothing, sin).f === sin
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

# --- M3: several bounds, several views; joint projections; rule 2 --------------------------------
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
    @test e isa ImplementError && occursin("rule 2", sprint(showerror, e))
    @test thrown(:(@implement ColTable Frozen3 copies project(t) = deepcopy(t.cols))) === nothing
end

# --- M4: dispatch, types first, then traits ----------------------------------------------------
@testset "M4: dispatch" begin
    # unrelated bounds on one position without a method for both: rejected when the module is defined
    e = thrown(quote
        @trait_module module Unresolved
        using TraitWorld, ..Columns, ..Rows
        f(t::ColTable) = 1
        f(t::RowTable) = 2
        end
    end)
    @test e isa TraitBoundError && occursin("no method has both", e.msg)
    @test thrown(quote
        @trait_module module Resolved
        using TraitWorld, ..Columns, ..Rows
        f(t::ColTable) = 1
        f(t::RowTable) = 2
        f(t::(ColTable, RowTable)) = 3
        end
    end) === nothing
    @test Main.Resolved.f([[1.0]]) == 1                 # ColTable only
    @test Main.Resolved.f([1.0 2.0]) == 3               # both: the method with both bounds
    # a subtrait beats its supertrait
    toplevel(quote
        @trait_module module SubSuper
        using TraitWorld, ..Caps
        g(t::HasLength) = "length"
        g(t::Indexable) = "indexable"
        end
    end)
    @test Main.SubSuper.g([1.0]) == "indexable"
    toplevel(quote
        struct OnlyLen; n::Int; end
        @implement Main.Caps.HasLength{OnlyLen} begin length(r) = r.n end
    end)
    @test Main.SubSuper.g(Main.OnlyLen(3)) == "length"
    # an entry and a type method that differ in another position: reported at definition
    e = thrown(quote
        @trait_module module AmbEntry
        using TraitWorld, ..Columns
        h(t::ColTable, x::Int) = 1
        h(v::AbstractVector, x::Integer) = 2
        end
    end)
    @test e isa TraitBoundError && occursin("ambiguous", e.msg)
end

# differential test: adopting a trait method keeps every call that worked before
module Before
describe(v::Vector{Float64}) = "a vector"
describe(m::AbstractMatrix) = "a matrix"
describe(x) = "something else"
end
@testset "M4: adopting a trait method keeps existing calls" begin
    corpus = Any[[1.0], [1.0 2.0; 3.0 4.0], [[1.0], [2.0]], 42, "text", (1, 2), Measurements([[1.0]]),
                 Ramp([1.0], 1), 1:3, Dict(1 => 2), [1, 2], nothing, :sym]
    changed = 0
    for x in corpus
        before = Before.describe(x)
        after = describe(x)
        if before == after
            continue
        end
        # only calls that reached the untyped fallback may change, and only for values with a projection
        @test before == "something else"
        @test TraitWorld.proj_lookup(ColTable, typeof(x)) !== nothing
        changed += 1
    end
    @test changed == 3              # [[1.0], [2.0]], Measurements, Ramp
end

@testset "M5: Callable at two signatures" begin
    toplevel(quote
        @trait_module module TwoSig
        using TraitWorld
        both(f::(Callable{Tuple{Float64},Float64}, Callable{Tuple{Int},Int}), x::Float64, n::Int) = (f(x), f(n))
        other(f::(Callable{Tuple{Float64},Float64}, Callable{Tuple{Int},Int}), s::String) = f(s)
        end
    end)
    @test Main.TwoSig.both(x -> x + one(x), 1.5, 2) == (2.5, 3)            # erased once per signature
    @test Main.TwoSig.both(abs, -1.5, -2) == (1.5, 2)                      # Base's function: itself
    @test_throws MethodError Main.TwoSig.other(x -> x, "s")               # a signature nobody declared
end

# --- M6: layering beyond imports; the piracy audit -------------------------------------------
module Plain2; f(x) = x + 1.0; end
@trait_module module Weights
using TraitWorld, ..Columns
export weight, weighted, guarded
weight(x::Real) = 1.0
weighted(t::ColTable, i::Int) = sum(x -> weight(x) * x, col(t, i))
sneak(t::ColTable) = Main.Plain2.f(colmean(t, 1))
guarded(t::ColTable, i::Int) = try weighted(t, i) catch; -1.0 end
end
using .Weights
@testset "M6: rule 1 on typed code; the piracy audit" begin
    e = try Weights.sneak([[1.0]]) catch err; err end
    @test e isa TraitUseError && occursin("outside the trait world (rule 1)", sprint(showerror, e))
    m = [1.0 2.0; 3.0 4.0]
    @test weighted(m, 1) == 4.0
    toplevel(:(module Pirate2; using ..Weights; Weights.weight(x::Float64) = 2.0; end))
    TraitWorld.mode!(:error)
    @test_throws PiracyError weighted(m, 1)
    TraitWorld.mode!(:recompile)
    @test weighted(m, 1) == 8.0                                  # the opt-out: plain Julia
    TraitWorld.mode!(:warn)
    @test (@test_logs (:warn, r"PiracyError") match_mode=:any weighted(m, 1)) == 8.0
    @test TraitWorld._rethrow_piracy(:(try f() catch; 0 end)).args[3].args[1].head === :&&   # catch rethrows PiracyError
end

# --- M7: concrete mode, verify_main ---------------------------------------------------------
@error_on_abstract @trait_module module Hot
using TraitWorld, ..Columns
hot(t::ColTable, k::Float64) = (s = 0.0; for x in col(t, 1); s += x * k; end; s)
end
@trait_module module Hot2
using TraitWorld, ..Columns
@warn_on_abstract cold(t::ColTable, k::Vector{Any}) = (s = 0.0; for x in col(t, 1); s += x * k[1]; end; s)
fine(t::ColTable, k::Vector{Any}) = (s = 0.0; for x in col(t, 1); s += x * k[1]; end; s)
end
@testset "M7: concrete mode" begin
    @test Hot.hot([[1.0, 2.0]], 2.0) == 6.0                                    # concrete: runs
    @test (@test_logs (:warn, r"abstract element type") match_mode=:any Hot2.cold([[1.0, 2.0]], Any[2.0])) == 6.0
    @test (@test_logs Hot2.fine([[1.0, 2.0]], Any[2.0])) == 6.0                 # not annotated: silent
    toplevel(quote
        @error_on_abstract @trait_module module Hot3
        using TraitWorld, ..Columns
        g(t::ColTable, k::Vector{Any}) = (s = 0.0; for x in col(t, 1); s += x * k[1]; end; s)
        end
    end)
    @test_throws AbstractTypeError Main.Hot3.g([[1.0, 2.0]], Any[2.0])
end

module VMain
using ..Columns
using Main: Measurements, Ramp
function main(args::Vector{String})
    t = isempty(args) ? Ramp([1.0, 2.0], 2) : Measurements([[1.0, 2.0]])
    return colmean(t, 1)::Float64 + total(t, 2)::Float64
end
end
@testset "M7: verify_main" begin
    VMain.main(String[]); VMain.main(["m"])
    r = verify_main(VMain.main, (Vector{String},))
    @test isclosed(r)
    @test count(p -> p.first === :enter, r.targets) == 2         # a builder for each user type the program can pass
    @test count(p -> p.first === :worker, r.targets) == 4        # colmean and total at two representations
    @test isempty(r.problems) && isempty(r.findings)
end

# --- the review's findings, one test each -----------------------------------------------------
userf2(x) = 2x
struct MyRep2; m::Matrix{Float64}; end
struct Wrapped2; m::Matrix{Float64}; end
@implement ColTable{MyRep2} Wrapped2 begin               # projection with operations for its own representation
    project(t) = MyRep2(t.m)
    ncols(r) = size(r.m, 2)
    col(r, i) = r.m[:, i]
end
@testset "review: correctness" begin
    # 1. a worker called with an abstract argument is checked too
    toplevel(quote
        @trait_module module RHelp
        using TraitWorld, ..Caps
        helper2(t::Iterable, x) = sum(t) + x
        outer2(t::Iterable, b::Bool) = helper2(t, b ? 1 : 2.0)
        end
    end)
    @test_throws TraitUseError Main.RHelp.outer2([1.0, 2.0], true)
    # 2. a trait object never escapes by return value
    toplevel(quote
        @trait_module module Leak
        using TraitWorld, ..Columns
        leak(t::ColTable) = t
        leak_cond(t::ColTable, b::Bool) = b ? t : 0
        end
    end)
    @test_throws TraitUseError Main.Leak.leak([[1.0]])
    @test_throws TraitUseError Main.Leak.leak_cond([[1.0]], false)
    # 3. a fallback of another shape still answers what plain Julia answers
    toplevel(quote
        @trait_module module FB
        using TraitWorld, ..Columns
        g(t::ColTable, x::Int) = 1
        g(x, y) = 2
        end
    end)
    @test Main.FB.g([[1.0]], 1) == 1
    @test Main.FB.g(42, 1) == 2 && Main.FB.g(42, "a") == 2
    # 4. a method with an unbounded where-variable becomes the fallback, never replaces the entry
    toplevel(quote
        @trait_module module WH
        using TraitWorld, ..Columns
        h(t::ColTable) = "trait"
        h(x::T) where {T} = "where"
        h2(t::ColTable) = "trait"
        h2(x::T) where {T <: Real} = "real"
        end
    end)
    @test Main.WH.h([[1.0]]) == "trait" && Main.WH.h(42) == "where"
    @test Main.WH.h2([[1.0]]) == "trait" && Main.WH.h2(42) == "real"
    # 5. defaults may use supertrait operations
    toplevel(quote
        @trait_module module SupDef
        using TraitWorld, ..Caps
        @trait Indexable2{R} <: HasLength begin
            Base.getindex(r::R, i::Int)::eltype(R)
            lastel(r::R)::eltype(R) = r[length(r)]
        end
        @implement Indexable2{A} where {A <: AbstractVector}
        last_of(t::Indexable2) = lastel(t)
        end
    end)
    @test Main.SupDef.last_of([1.0, 5.0]) == 5.0
    # 6. existing methods (a family, or without a block) with a trait default
    toplevel(quote
        @trait_module module FamDef
        using TraitWorld
        @trait WithDef{R} begin
            Base.length(r::R)::Int
            dbl(r::R)::Int = 2 * length(r)
        end
        @implement WithDef{A} where {A <: AbstractVector}
        @implement WithDef{Tuple{Int,Int}}
        twice_len(t::WithDef) = dbl(t)
        end
    end)
    @test Main.FamDef.twice_len([1, 2, 3]) == 6 && Main.FamDef.twice_len((1, 2)) == 4
    # 7. the projection-with-operations form
    @test colmean(Wrapped2([1.0 2.0; 3.0 4.0]), 1) == 2.0
    # 8. a lower-bounded type variable confers no ownership
    e = thrown(quote
        @trait_module module LBPirate
        using TraitWorld, ..Columns
        struct Mine end
        Columns.ncols(x::T) where {T >: Mine} = -1
        end
    end)
    @test e isa OwnershipError
    for m in methods(Columns.ncols)
        occursin("LBPirate", string(m.module)) && Base.delete_method(m)
    end
    # 11. entries that differ in which position is bounded are no ambiguity at definition
    @test thrown(quote
        @trait_module module TwoPos
        using TraitWorld, ..Columns
        f(t::ColTable, x::Int) = 1
        f(x::Int, t::ColTable) = 2
        end
    end) === nothing
    @test Main.TwoPos.f([[1.0]], 1) == 1 && Main.TwoPos.f(1, [[1.0]]) == 2
    # 12. a Base wrapper around a function from above is from above
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, nothing, Base.Fix1(*, 2.0)).f isa Base.Fix1
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, nothing, Base.Fix1(userf2, 2.0)).f isa TraitWorld.Erased
end

@testset "review: catch rethrows PiracyError; a closed world in a session" begin
    toplevel(quote
        @trait_module module Catcher
        using TraitWorld, ..Columns, ..Weights
        safe(t::ColTable) = try Weights.weighted([[1.0, 2.0]], 1) catch; -1.0 end
        end
    end)
    TraitWorld.mode!(:error)
    @test_throws PiracyError Main.Catcher.safe([[1.0]])
    TraitWorld.mode!(:warn)
    r = verify_main(VMain.main, (Vector{String},); close = true)
    @test TraitWorld.CLOSED_WORLD[]
    @test VMain.main(String[]) == VMain.main(String[]) && VMain.main(["m"]) isa Float64
    TraitWorld.open_world!()
    @test !TraitWorld.CLOSED_WORLD[]
end

@testset "review: unrelated bounds added by another module" begin
    e = thrown(quote
        @trait_module module RowsX
        using TraitWorld, ..Columns
        @trait RowX{R} begin rx(r::R)::Int end
        @implement RowX{Matrix{Float64}} begin rx(r) = 1 end
        Columns.colmean(t::RowX, i::Int) = 0.0
        end
    end)
    @test e isa TraitBoundError
    for m in methods(Columns.colmean)
        occursin("RowsX", string(m.module)) && Base.delete_method(m)
    end
end

# --- poc3 M1: keyword, default and variable arguments -------------------------------------------
@trait_module module KW
using TraitWorld, ..Columns
export colz, colmean_or, cm_all, ncols_sum, describe_kw
"a bounded keyword that defaults to the trait object itself, and a typed keyword with a constant default"
colz(t::ColTable, i::Int; baseline::ColTable = t, tol::Float64 = eps()) =
    (col(t, i) .- colmean(baseline, i)) ./ max(colrange(baseline, i), tol)
"a positional default: two exported methods"
colmean_or(t::ColTable, i::Int = 1) = colmean(t, i)
"a keyword whose default calls an operation, and an untyped keyword"
cm_all(t::ColTable; cols = 1:ncols(t), scale = 1.0) = [colmean(t, i) * scale for i in cols]
"a vararg of trait objects"
ncols_sum(ts::ColTable...) = sum(ncols(t) for t in ts; init = 0)
describe_kw(t::ColTable; long::Bool = false) = long ? "a table with $(ncols(t)) columns" : "a table"
describe_kw(x; long::Bool = false) = "not a table"
end
using .KW
@testset "poc3 M1: keyword, default and variable arguments" begin
    v = [[1.0, 3.0], [2.0, 6.0]]
    m = Measurements(v)
    @test colz(m, 1) == [-0.5, 0.5]
    @test colz(m, 1; baseline = Ramp([2.0, 4.0], 2)) == colz(m, 1; baseline = [[2.0, 4.0]])   # projected at the entry
    @test colz(m, 1; tol = 10.0) == [-0.1, 0.1]
    @test_throws TypeError colz(m, 1; tol = 1)                      # declared Float64, as in plain Julia
    @test_throws TraitBoundError colz(m, 1; baseline = 42)         # no projection: refused at the entry
    @test colmean_or(m) == 2.0 && colmean_or(m, 2) == 4.0
    @test cm_all(m) == [2.0, 4.0] && cm_all(m; cols = 2:2, scale = 2.0) == [8.0]
    @test ncols_sum(m, Ramp([1.0], 3), v) == 7
    @test ncols_sum() == 0
    @test describe_kw(m; long = true) == "a table with 2 columns" && describe_kw(42; long = true) == "not a table"
    @test_throws MethodError ncols_sum(m, 42)
end

# --- poc3 M2: Callable modes ---------------------------------------------------------------------
@trait_module module CM
using TraitWorld, ..Columns
export cmap, csum, cboth
cmap(f::Callable{Tuple{Float64},Float64}, t::ColTable, i::Int) = map(f, col(t, i))                   # default: dynamic
csum(f::Callable{Tuple{Float64},Float64,CompiledCall}, t::ColTable, i::Int) = sum(f, col(t, i))      # default: compiled
cboth(f::(Callable{Tuple{Float64},Float64}, Callable{Tuple{Int},Int}), x::Float64, n::Int) = (f(x), f(n))
end
using .CM
userdbl(x) = 2x
@testset "poc3 M2: Callable modes" begin
    v = [[1.0, 2.0]]
    @test cmap(userdbl, v, 1) == [2.0, 4.0] && csum(userdbl, v, 1) == 6.0
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, nothing, userdbl).f isa TraitWorld.Erased
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, CompiledCall, userdbl).f === userdbl
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, DynamicCall, compiled_call(userdbl)).f === userdbl   # the value wins
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, CompiledCall, dynamic_call(userdbl)).f isa TraitWorld.Erased
    @test TraitWorld.enter_callable(Tuple{Float64}, Float64, nothing, Callable{Tuple{Float64},Float64,DynamicCall}(userdbl)).f isa TraitWorld.Erased
    @test_throws TraitBoundError TraitWorld.enter_callable(Tuple{Float64}, Float64, nothing, Callable{Tuple{Int},Int,DynamicCall}(userdbl))
    @test cmap(compiled_call(userdbl), v, 1) == [2.0, 4.0] && csum(dynamic_call(userdbl), v, 1) == 6.0
    @test csum(abs2, v, 1) == 5.0                                  # Base's function: a compiled call whatever the default
    @test cboth(dynamic_call(x -> x + one(x)), 1.5, 2) == (2.5, 3)
    @test_throws LoadError Core.eval(Main, :(@trait_module module OldSpec
        using TraitWorld, ..Columns
        f(@specialize(g::Callable{Tuple{Float64},Float64}), t::ColTable) = g(1.0)
    end))
end

# --- poc3 M4: the one-line conformance -----------------------------------------------------------
@testset "poc3 M4: the one-line conformance" begin
    toplevel(quote
        struct Meas1; data::Vector{Vector{Float64}}; end          # the field named data
        @implement ColTable Meas1
        struct Meas2; n::Int; cols::Vector{Vector{Float64}}; end  # the one conforming field
        @implement ColTable Meas2
        struct Ramp1; base::Vector{Float64}; n::Int; end         # methods: its own representation
        Columns.ncols(r::Ramp1) = r.n
        Columns.col(r::Ramp1, i::Int) = r.base .* i
        @implement ColTable Ramp1
        struct Nested; data::Meas1; end                           # a field whose type conforms by projection: composed
        @implement ColTable Nested
        struct Grid1; data::Matrix{Float64}; end                  # one projection for two traits
        @implement (ColTable, Main.Rows.RowTable) Grid1
    end)
    @test colmean(Main.Meas1([[1.0, 3.0]]), 1) == 2.0
    @test colmean(Main.Meas2(1, [[1.0, 3.0]]), 1) == 2.0
    @test colmean(Main.Ramp1([1.0, 3.0], 2), 2) == 4.0
    @test TraitWorld.implementation(ColTable, Main.Ramp1) isa TraitWorld.ImplRec
    @test colmean(Main.Nested(Main.Meas1([[1.0, 3.0]])), 1) == 2.0
    @test overview(Main.Grid1([1.0 2.0; 3.0 4.0])) == (2.0, [1.0, 2.0])
    e = thrown(quote struct TwoF; a::Vector{Vector{Float64}}; b::Vector{Vector{Float64}}; end; @implement ColTable TwoF end)
    @test e isa ImplementError && occursin("several fields", e.msg) && occursin("a, b", e.msg)
    e = thrown(quote struct Abs1; data::AbstractVector{Vector{Float64}}; end; @implement GTable Abs1 end)   # conforms through a family
    @test e isa ImplementError && occursin("field `data`", e.msg) && occursin("not deeply concrete", e.msg)
    e = thrown(quote struct Abs2; data::AbstractVector; end; @implement ColTable Abs2 end)                   # conforms to nothing
    @test e isa ImplementError && occursin("no field of", e.msg)
    e = thrown(quote struct Part1; n::Int; end; Columns.ncols(r::Part1) = r.n; @implement ColTable Part1 end)
    @test e isa ImplementError && occursin("not for col", e.msg)
    e = thrown(quote struct NoF; x::Int; end; @implement ColTable NoF end)
    @test e isa ImplementError && occursin("no field of", e.msg)
end

# --- poc3 M3: calls upward, declared calls, handles ---------------------------------------
module FakeOutside                       # an ordinary package standing in for Makie
mutable struct Fig; pts::Vector{Tuple{Float64,Float64}}; title::String; end
newfig() = Fig(Tuple{Float64,Float64}[], "")
addpoints!(f::Fig, xs, ys; title = "") = (append!(f.pts, zip(xs, ys)); f.title = title; nothing)
npoints(f::Fig) = length(f.pts)
title(f::Fig) = f.title
end
module FakeInterface
using TraitWorld, ..FakeOutside
@trait_module module Plots
using TraitWorld
export Figure, PointSeries, xs, ys, figure, scatter!, npts, ftitle, bad, leak
@handle Figure
@trait PointSeries{R} begin
    xs(r::R)::Vector{Float64}
    ys(r::R)::Vector{Float64}
end
@implement PointSeries{Matrix{Float64}} begin
    xs(r) = r[:, 1]
    ys(r) = r[:, 2]
end
figure() = @call FakeOutside.newfig()::Figure
scatter!(f::Figure, t::PointSeries; title::String = "") = @call FakeOutside.addpoints!(f, xs(t), ys(t); title)::Nothing
npts(f::Figure) = @call FakeOutside.npoints(f)::Int
ftitle(f::Figure) = @call FakeOutside.title(f)::String
bad(t::PointSeries, f::Figure) = (f.ref; xs(t))
leak(t::PointSeries, f::Figure) = @call FakeOutside.addpoints!(f, t, t)::Nothing
end
using .Plots
export Figure, PointSeries, xs, ys, figure, scatter!, npts, ftitle, bad, leak
end
@trait_module module UsesPlots
using TraitWorld, ..FakeInterface
export plot_it
plot_it(t::PointSeries) = (f = figure(); scatter!(f, t; title = "two points"); (npts(f), ftitle(f)))
end
@testset "poc3 M3: calls upward, declared calls, handles" begin
    m = [1.0 2.0; 3.0 4.0]
    @test UsesPlots.plot_it(m) == (2, "two points")
    f = FakeInterface.figure()
    @test f isa FakeInterface.Figure && f.ref isa FakeOutside.Fig          # a handle is a value to ordinary code
    FakeInterface.scatter!(f, m); @test FakeInterface.npts(f) == 2
    e = try FakeInterface.bad(m, f) catch err; err end
    @test e isa TraitUseError && occursin("handle is opaque", sprint(showerror, e))
    e = try FakeInterface.leak(m, f) catch err; err end
    @test e isa TraitUseError && occursin("never go up", sprint(showerror, e))
    @test length(TraitWorld.declared_calls(FakeInterface)) == 5
    @test TraitWorld.is_declarer(FakeInterface) && FakeInterface in TraitWorld.declarers()   # the ordinary module around the trait module holds them
    e = thrown(quote
        @trait_module module NoIface
        using TraitWorld, ..FakeOutside
        end
    end)
    @test e isa LayeringError                                           # the wrapped package itself stays outside
    e = thrown(quote
        @trait_module module BadCall
        using TraitWorld
        g() = @call Main.FakeOutside.newfig()::Int
        end
    end)
    @test e isa ErrorException && occursin("needs an ordinary module around the trait module", e.msg)
end

# --- poc3 M8: verify_main with keyword entries and declared calls ------------------------------
module VKW
using ..KW, ..UsesPlots
using Main: Measurements
function main(args::Vector{String})
    t = Measurements([[1.0, 2.0]])
    z = colz(t, 1; tol = 0.5)::Vector{Float64}
    n = plot_it([1.0 2.0; 3.0 4.0])::Tuple{Int,String}
    return sum(z) + n[1]
end
end
@testset "poc3 M8: verify_main, keyword entries and declared calls" begin
    VKW.main(String[])
    r = verify_main(VKW.main, (Vector{String},))
    @test isclosed(r)
    @test count(p -> p.first === :declared, r.targets) == 4           # figure, addpoints!, npoints, title
    @test count(p -> p.first === :worker, r.targets) >= 2             # colz's keyword worker, plot_it's worker
    @test any(p -> p.first === :declared && p.second <: Tuple{typeof(FakeOutside.newfig)}, r.targets)
end

# --- poc3 M6: sealing (last: refuse mode deletes the pirates of the session) ------------------------
@testset "poc3 M6: sealing" begin
    @test "Julia" in TraitWorld.SEALED && "Columns" in TraitWorld.SEALED     # a trait module seals itself
    toplevel(:(module BasePirate; Base.sum(x::Vector{Int16}) = Int16(0); end))
    found = TraitWorld.find_pirates!()
    @test any(p -> p.definer == "BasePirate" && "Julia" in p.needs, found)
    @test any(p -> p.definer == "Pirate2", found)                           # Weights.weight(::Float64): Weights is sealed
    @test_throws PiracyError TraitWorld.check_no_piracy()
    # warn mode keeps the pirate and reports it once (a full scan, as after a new seal)
    TraitWorld._RESCAN[] = true
    @test (@test_logs (:warn, r"BasePirate defines") match_mode=:any TraitWorld._check_loads!()) === nothing
    @test which(sum, (Vector{Int16},)).module === Main.BasePirate
    # refuse mode deletes a pirate that loads afterwards, and reports it
    TraitWorld.find_pirates!()                                              # the cursor past everything so far
    TraitWorld.piracy_mode!(:refuse)
    toplevel(:(module BasePirate2; Base.sum(x::Vector{Int32}) = Int32(0); end))
    @test which(sum, (Vector{Int32},)).module === Main.BasePirate2
    @test_logs (:error, r"BasePirate2 defines") match_mode=:any TraitWorld._check_loads!()
    @test which(sum, (Vector{Int32},)).module === Base
    # a tolerated package is never touched
    push!(TraitWorld.TOLERATED, "Tolerated1")
    toplevel(:(module Tolerated1; Base.sum(x::Vector{UInt16}) = UInt16(0); end))
    @test TraitWorld._check_loads!() === nothing
    @test which(sum, (Vector{UInt16},)).module === Main.Tolerated1
    TraitWorld.piracy_mode!(:warn)
    # a call method of a sealed callable type: not bound to any name, found in the global method table
    toplevel(:(module FixPirate; (f::Base.Fix1{typeof(sum)})(x::Vector{Int8}) = Int8(0); end))
    @test any(p -> p.definer == "FixPirate", TraitWorld.find_pirates!())
    # a loaded package that is no extension is remembered as such (the scan asks once per method)
    @test TraitWorld._extension_parent(TraitWorld) === nothing && TraitWorld in TraitWorld._NOT_EXTENSIONS
end

# --- trait wrappers: a split core, its named implementation, one it does not name --------------
module CoreX; struct V; x::Vector{Float64}; end; end
module ImplX; using ..CoreX; Base.length(v::CoreX.V) = length(v.x); end
module ImplY; using ..CoreX; Base.size(v::CoreX.V) = (length(v.x),); end
@testset "trait wrappers" begin
    lx = first(methods(length, (CoreX.V,))); sy = first(methods(size, (CoreX.V,)))
    @test !TraitWorld.owned_method(lx) && !TraitWorld.is_trait_world(CoreX)    # unwrapped: ImplX owns neither
    toplevel(:(module CoreXWrapper; using TraitWorld, ..CoreX, ..ImplX; @trait_wrapper CoreX ImplX; end))
    @test TraitWorld.wrapper_of(CoreX) === Main.CoreXWrapper && "CoreX" in TraitWorld.SEALED && "ImplX" in TraitWorld.SEALED
    @test TraitWorld.owned_method(lx) && !TraitWorld.owned_method(sy)        # the named implementation is a delegate
    found = TraitWorld.find_pirates!()                                       # a new seal: a full scan
    @test any(p -> p.definer == "ImplY", found) && !any(p -> p.definer == "ImplX", found)
    @test TraitWorld.is_trait_world(CoreX) && TraitWorld.is_trait_world(ImplX)
    toplevel(:(@trait_module module UsesCoreX; using TraitWorld, ..CoreX; end))      # a wrapped package may be imported
    @test isdefined(Main, :UsesCoreX)
    # at most one wrapper per package: a second decides nothing
    @test_logs (:error, r"second trait wrapper") match_mode=:any toplevel(:(module CoreXWrapper2; using TraitWorld, ..CoreX; @trait_wrapper CoreX; end))
    @test TraitWorld.wrapper_of(CoreX) === Main.CoreXWrapper
end

# --- poc3 M5: the Base wrapper, the door check -----------------------------------------------------
module PlainGlobals; x = 1; end
@trait_module module Doors
using TraitWorld, ..Columns
bad_eval(t::ColTable) = (eval(:(1 + 1)); ncols(t))
bad_tls(t::ColTable) = (task_local_storage(); ncols(t))
bad_module(t::ColTable) = Main.PlainGlobals.x + ncols(t)
counter = 0
bad_global(t::ColTable) = counter + ncols(t)
warns(t::ColTable) = (@warn "a table"; ncols(t))
prints(t::ColTable) = (println(ncols(t)); ncols(t))
clean(t::ColTable) = (c = col(t, 1); sum(c) / length(c) + sqrt(abs(minimum(c))) + length(string(ncols(t))))
deep(t::ColTable) = length(string(col(t, 1)[1])) + ncols(t)
barrier_eval(t::ColTable) = (f = Base.inferencebarrier(Base.eval); f(Main, :(1 + 1)); ncols(t))
end
@testset "poc3 M5: the door check" begin
    v = [[1.0, 2.0]]
    msg(f) = try f(v); "" catch e; sprint(showerror, e) end
    @test occursin("inward door", msg(Doors.bad_eval)) && occursin("eval", msg(Doors.bad_eval))
    @test occursin("inward door", msg(Doors.bad_tls))
    @test occursin("inward door", msg(Doors.bad_module)) || occursin("global", msg(Doors.bad_module))
    @test occursin("global", msg(Doors.bad_global)) && occursin("counter", msg(Doors.bad_global))
    @test (@test_logs (:warn, "a table") Doors.warns(v)) == 1                   # an outward door: accepted
    @test Doors.prints(v) == 1
    @test Doors.clean(v) == 1.5 + 1.0 + 1
    W = TraitWorld.WORKER_DOORS
    key(f) = first(k for k in keys(W) if k.parameters[1] === typeof(f))
    @test !isempty(W[key(Doors.warns)].outward) && !isempty(W[key(Doors.prints)].outward)
    @test isempty(W[key(Doors.clean)].outward)
    # the walk's budget: its end is reported whatever the concrete level
    old = TraitWorld.DOOR_BUDGET[]
    TraitWorld.DOOR_BUDGET[] = 3
    empty!(TraitWorld._DOOR_FACTS)
    @test (@test_logs (:warn, r"stopped at its budget") match_mode=:any Doors.deep(v)) == 4
    @test W[key(Doors.deep)].truncated
    TraitWorld.DOOR_BUDGET[] = old
    # a door behind a dynamic call: the design checks the target when it compiles; stock Julia does not
    @test_broken occursin("inward door", msg(Doors.barrier_eval))
    # the same door through a declared call is accepted
    toplevel(quote
        module TLSInterface
        using TraitWorld
        @trait_module module T
        using TraitWorld
        export tls
        tls() = @call Base.task_local_storage(:tw_probe)::Int
        end
        using .T: tls
        end
    end)
    task_local_storage(:tw_probe, 7)
    @test Main.TLSInterface.tls() == 7
end

@testset "view caches: keys and recording" begin
    vc = TraitWorld
    # a signature's view: the packages it names; Julia's own modules are in every view
    @test vc._vc_packages(Tuple{typeof(sum),Vector{Int}}) == Module[]
    v = [1.0, 2.0]
    T = typeof(TObj((TraitWorld.View{TraitWorld._PC.PCT}(TraitWorld.Impl{(:pd,)}(), v),)))
    @test vc._vc_packages(Tuple{typeof(TraitWorld._PC.pcsum),T}) == [TraitWorld]
    # a type of the session (a module under Main) has no package to hold its cache
    @test vc._vc_packages(Tuple{typeof(Columns.colmean),Measurements}) === nothing
    # the call an entry makes for a worker
    NT = NamedTuple{(:a,),Tuple{Int}}
    @test vc._vc_entry_sig(Tuple{typeof(Core.kwcall),NT,typeof(sum),Int}) == Tuple{typeof(TraitWorld.checked_kwcall),NT,typeof(sum),Int}
    @test vc._vc_entry_sig(Tuple{typeof(sum),Int}) == Tuple{typeof(TraitWorld.checked_call),typeof(sum),Int}
    # a first call notes its worker; one a loaded view cache checked is neither checked nor noted again
    toplevel(quote
        struct VCNew; n::Int; end            # its own representation: workers new to the session
        @implement Columns.ColTable{VCNew} begin
            ncols(r) = r.n
            col(r, i) = fill(Float64(i), 2)
        end
    end)
    if vc._VC_ON[]
        empty!(vc._VC_NEW)
        @test Columns.colrange(Main.VCNew(2), 1) == 0.0
        @test length(vc._VC_NEW) == 1 && vc._VC_NEW[1].parameters[1] === typeof(Columns.colrange)
        sig = vc._VC_NEW[1]
        empty!(vc._VC_NEW)
        # nothing to write for types of the session
        withenv("JULIA_TW_VIEWCACHE_DIR" => mktempdir()) do
            @test viewcache_flush() == String[]
            @test isempty(readdir(vc.viewcache_dir()))
        end
        # registered as checked, as a view cache's __init__ does: not checked, not noted
        sig2 = Tuple{typeof(Columns.colmean),sig.parameters[2:end]...}
        vc._vc_register(Any[sig2])
        @test Columns.colmean(Main.VCNew(2), 2) == 2.0
        @test isempty(vc._VC_NEW)
        delete!(vc._VC_CHECKED, sig2)
    end
end

@testset "definition checking at archetypes" begin
    toplevel(quote
        @trait_module module BadDef
        using TraitWorld, ..Columns, ..Rows
        def_ordinary(t::ColTable) = sum(t)
        def_typeof(t::ColTable) = typeof(t)
        def_rule3(t::ColTable) = firstrow(t)
        def_good(t::(ColTable, RowTable)) = (colmean(t, 1), firstrow(t))
        def_clean(t::ColTable, i::Int) = colmean(t, i) * ncols(t)
        def_fn(f::Callable{Tuple{Float64},Float64}, t::ColTable) = map(f, col(t, 1))
        end
    end)
    # found before any representation reaches these functions
    e = try check_definitions(Main.BadDef); nothing catch err; err end
    @test e isa TraitUseError
    ps = join(e.problems, "\n")
    @test occursin("def_ordinary", ps) && occursin("`sum`, an ordinary function", ps)
    @test occursin("def_typeof", ps) && occursin("typeof(t)", ps)
    @test occursin("def_rule3", ps) && occursin("rule 2", ps)
    @test !occursin("def_good", ps) && !occursin("def_clean", ps)
    checked = Set(m.name for m in TraitWorld._DEF_CHECKED)
    @test :def_good in checked && :def_clean in checked
    @test !(:def_fn in checked)                     # a function from above: checked per signature
    @test isempty(check_definitions(Main.Columns))
    # workers of methods checked at definition run without their per-signature check, and compute the same
    @test Main.BadDef.def_clean(Measurements([[1.0, 3.0]]), 1) == 2.0
    @test Main.BadDef.def_clean(Ramp([1.0, 2.0], 2), 2) == 6.0
end
