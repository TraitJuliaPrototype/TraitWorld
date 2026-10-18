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
    @test occursin("`t.views`", msg(Main.Bad.bad_field))
    @test occursin("typeof(t)", msg(Main.Bad.bad_typeof))
    @test occursin("`sum`", msg(Main.Bad.helper))        # found through the worker it calls
    toplevel(quote
        struct Both; cols::Vector{Vector{Float64}}; mat::Matrix{Float64}; end
        @implement ColTable Both project(t) = t.cols
        @implement Main.Rows.RowTable Both project(t) = t.mat
    end)
    @test Main.Bad.good(Main.Both([[1.0, 3.0]], [1.0 2.0; 3.0 4.0])) == (2.0, [1.0, 2.0])
end

@testset "M1: ownership (rule 3); a trait module may import ordinary code" begin
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
    # wrapping by facts: a trait module may import and use any Julia code
    toplevel(:(module Plain; f() = 1; end))
    e = thrown(quote
        @trait_module module UsesPlain
        using TraitWorld, ..Plain
        g() = Plain.f() + 1
        end
    end)
    @test e === nothing && Main.UsesPlain.g() == 2
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
    @test e === nothing                  # a field the trait does not declare is not part of the key (decision 1)
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
struct Sep3; cols::Vector{Vector{Float64}}; rows::Matrix{Float64}; end
@implement ColTable Sep3 by cols                      # each trait forwarded to its own field
@implement Main.Rows.RowTable Sep3 by rows
struct Joint3; m::Matrix{Float64}; end
@implement (ColTable, Main.Rows.RowTable) Joint3 by m # both forwarded to one field
struct Live3; cols::Vector{Vector{Float64}}; end
@implement (ColTable, ColStore) Live3 by cols

@testset "M3: views and joint projections" begin
    m = [1.0 2.0; 3.0 4.0]
    @test overview(Sep3([[1.0, 3.0], [2.0, 4.0]], m)) == (2.0, [1.0, 2.0])
    @test overview(Joint3(m)) == (2.0, [1.0, 2.0])
    @test overview2(Joint3(m)) == overview(m)
    x = Live3([[1.0, 3.0]]); normalize!(x, 1); @test x.cols[1] == [0.25, 0.75]
    toplevel(:(struct Frozen3; cols::Vector{Vector{Float64}}; end))
    # copying and computed projections are not part of the design (note "Types that only convert")
    e = thrown(:(@implement ColStore Frozen3 copies project(t) = deepcopy(t.cols)))
    @test e isa ImplementError && occursin("copying", sprint(showerror, e))
    e = thrown(:(@implement ColTable Frozen3 project(t) = deepcopy(t.cols)))
    @test e isa ImplementError && occursin("computes a value", sprint(showerror, e))
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

# --- M6: calls into ordinary code; a winning pirate -------------------------------------------
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
@testset "M6: calls into ordinary code; a winning pirate is followed" begin
    @test Weights.sneak([[1.0]]) == 2.0                              # an ordinary package's function: called as in plain Julia
    m = [1.0 2.0; 3.0 4.0]
    @test weighted(m, 1) == 4.0
    toplevel(:(module Pirate2; using ..Weights; Weights.weight(x::Float64) = 2.0; end))
    # wrapping by facts: a winning pirate is followed as plain Julia follows it (G1)
    @test weighted(m, 1) == 8.0
    @test !TraitWorld.owned_method(only(methods(Weights.weight, (Float64,))))   # still a pirate under rule 3
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
    # entries are ordinary inlined methods (keys-plan §6): for types the program knows, every trait call is static
    @test count(p -> p.first in (:enter, :worker), r.targets) == 0
    @test isempty(r.problems)
end

# --- the review's findings, one test each -----------------------------------------------------
userf2(x) = 2x
struct MyRep2; m::Matrix{Float64}; end
struct Wrapped2; r::MyRep2; end
@implement ColTable{MyRep2} Wrapped2 begin               # forwarding with the operations for the field's type
    project(t) = t.r
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
    # 7. the forwarding-with-operations form
    @test colmean(Wrapped2(MyRep2([1.0 2.0; 3.0 4.0])), 1) == 2.0
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

@testset "review: a pirate behind a catch; a closed world in a session" begin
    toplevel(quote
        @trait_module module Catcher
        using TraitWorld, ..Columns, ..Weights
        safe(t::ColTable) = try Weights.weighted([[1.0, 2.0]], 1) catch; -1.0 end
        end
    end)
    # wrapping by facts follows the pirate (G1), as plain Julia does
    @test Main.Catcher.safe([[1.0]]) == 2.0 * 1.0 + 2.0 * 2.0
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
        struct Grid1; data::Matrix{Float64}; end                  # one projection for two traits
        @implement (ColTable, Main.Rows.RowTable) Grid1
    end)
    @test colmean(Main.Meas1([[1.0, 3.0]]), 1) == 2.0
    @test colmean(Main.Meas2(1, [[1.0, 3.0]]), 1) == 2.0
    @test colmean(Main.Ramp1([1.0, 3.0], 2), 2) == 4.0
    @test TraitWorld.implementation(ColTable, Main.Ramp1) isa TraitWorld.ImplRec
    # forwarding does not chain: a field whose type itself forwards is not an implementing type
    e = thrown(quote struct Nested; data::Meas1; end; @implement ColTable Nested end)
    @test e isa ImplementError
    @test overview(Main.Grid1([1.0 2.0; 3.0 4.0])) == (2.0, [1.0, 2.0])
    e = thrown(quote struct TwoF; a::Vector{Vector{Float64}}; b::Vector{Vector{Float64}}; end; @implement ColTable TwoF end)
    @test e isa ImplementError && occursin("several fields", e.msg) && occursin("a, b", e.msg)
    e = thrown(quote struct Abs1; data::AbstractVector{Vector{Float64}}; end; @implement GTable Abs1 end)   # an abstract key: allowed (decision 1)
    @test e === nothing && gmean(Main.Abs1([[1.0, 3.0]])) == 2.0
    e = thrown(quote struct Abs2; data::AbstractVector; end; @implement ColTable Abs2 end)                   # conforms to nothing
    @test e isa ImplementError && occursin("no field of", e.msg)
    e = thrown(quote struct Part1; n::Int; end; Columns.ncols(r::Part1) = r.n; @implement ColTable Part1 end)
    @test e isa ImplementError && occursin("not for col", e.msg)
    e = thrown(quote struct NoF; x::Int; end; @implement ColTable NoF end)
    @test e isa ImplementError && occursin("no field of", e.msg)
end

# --- poc3 M8: verify_main with keyword entries ------------------------------------------------
module VKW
using ..KW
using Main: Measurements
function main(args::Vector{String})
    t = Measurements([[1.0, 2.0]])
    z = colz(t, 1; tol = 0.5)::Vector{Float64}
    return sum(z)
end
end
@testset "poc3 M8: verify_main, keyword entries" begin
    VKW.main(String[])
    r = verify_main(VKW.main, (Vector{String},))
    @test isclosed(r)
    @test count(p -> p.first === :worker, r.targets) == 0             # every trait call static: entries are ordinary methods
end

# --- ownership outside trait modules: a split core and an implementation package ----------------
module CoreX; struct V; x::Vector{Float64}; end; end
module ImplX; using ..CoreX; Base.length(v::CoreX.V) = length(v.x); end
@testset "ownership of methods outside trait modules (rule 3 lookups)" begin
    lx = first(methods(length, (CoreX.V,)))
    @test !TraitWorld.owned_method(lx) && !TraitWorld.is_trait_world(CoreX)    # ImplX owns neither the function nor the type
    toplevel(:(module BasePirate; Base.sum(x::Vector{Int16}) = Int16(0); end))
    @test !TraitWorld.owned_method(only(methods(sum, (Vector{Int16},))))     # Julia owns both
    @test TraitWorld.owned_method(first(methods(CoreX.V)))                   # a type's constructor: its own
    # a loaded package that is no extension is remembered as such (a scan asks once per method)
    @test TraitWorld._extension_parent(TraitWorld) === nothing && TraitWorld in TraitWorld._NOT_EXTENSIONS
    # package roots of types, for a strict mode
    @test TraitWorld._required_roots(Vector{CoreX.V}) == [CoreX]
    @test isempty(TraitWorld._required_roots(Vector{Int}))
end

# --- wrapping by facts: trait-world code calls any Julia code -------------------------------------
module PlainGlobals; x = 1; end
@trait_module module AnyCode
using TraitWorld, ..Columns
uses_eval(t::ColTable) = (eval(:(1 + 1)); ncols(t))
uses_tls(t::ColTable) = (task_local_storage(); ncols(t))
other_global(t::ColTable) = Main.PlainGlobals.x + ncols(t)
counter = 0
own_global(t::ColTable) = counter + ncols(t)
warns(t::ColTable) = (@warn "a table"; ncols(t))
prints(t::ColTable) = (println(ncols(t)); ncols(t))
clean(t::ColTable) = (c = col(t, 1); sum(c) / length(c) + sqrt(abs(minimum(c))) + length(string(ncols(t))))
end
@testset "wrapping by facts: trait-world code calls any Julia code" begin
    v = [[1.0, 2.0]]
    # what plain Julia computes: no door check, no global check, no layering rule
    @test AnyCode.uses_eval(v) == 1 && AnyCode.uses_tls(v) == 1
    @test AnyCode.other_global(v) == 2 && AnyCode.own_global(v) == 1
    @test (@test_logs (:warn, "a table") AnyCode.warns(v)) == 1
    @test AnyCode.prints(v) == 1
    @test AnyCode.clean(v) == 1.5 + 1.0 + 1
end

@testset "return types read from CodeInstances: a predicate's conditional is no constant" begin
    pred(x) = x === nothing
    mi = Base.method_instance(pred, Tuple{Union{Nothing, Bool}})
    ci = Base.Compiler.typeinf_ext_toplevel(Base.Compiler.NativeInterpreter(), mi, Base.Compiler.SOURCE_MODE_NOT_REQUIRED)
    @test TraitWorld._ci_return_type(ci) === Bool
    one(x) = 1
    ci1 = Base.Compiler.typeinf_ext_toplevel(Base.Compiler.NativeInterpreter(), Base.method_instance(one, Tuple{Int}), Base.Compiler.SOURCE_MODE_NOT_REQUIRED)
    @test TraitWorld._ci_return_type(ci1) === Int
end

@testset "facts at tuples with unions of concrete elements (iteration with missing values)" begin
    ii = typeof(Base.indexed_iterate)
    # `item, state = iterate(v, s)` over a Vector{Union{Missing, Int}}: two concrete facts
    s = Tuple{ii, Tuple{Union{Missing, Int}, Int}, Int}
    @test TraitWorld._fact_sig(s)
    @test Set(TraitWorld._fact_splits(s)) == Set([Tuple{ii, Tuple{Missing, Int}, Int}, Tuple{ii, Tuple{Int, Int}, Int}])
    @test TraitWorld._fact_splits(Tuple{ii, Tuple{Int, Int}, Int}) == [Tuple{ii, Tuple{Int, Int}, Int}]
    # not finite sets of concrete signatures: abstract elements, varargs, more splits than union splitting allows
    @test !TraitWorld._fact_sig(Tuple{ii, Tuple{Integer, Int}, Int})
    @test !TraitWorld._fact_sig(Tuple{ii, Tuple{Vararg{Int}}, Int})
    @test !TraitWorld._fact_sig(Tuple{ii, Tuple{Union{Missing, Int}, Union{Missing, Float64}, Union{Nothing, Int}}, Int})
    # top-level unions are left to union splitting
    @test !TraitWorld._fact_sig(Tuple{typeof(sin), Union{Int, Float64}})
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
include("dynamic.jl")
include("fields.jl")
include("params.jl")
include("like.jl")
include("printing.jl")
include("keys_syntax.jl")
include("runtime.jl")
include("strict.jl")
include("verify_dynamic.jl")
