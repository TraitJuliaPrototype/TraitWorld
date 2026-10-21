# Concrete parameters and Self (traits reference §11.1, §11.2): a trait names the parts of an
# implementation that must be concrete, or that warn; a bounded function names the parts of its
# arguments' implementations it requires concrete. The old spellings are refused with the new ones.
# Runs inside runtests.jl, or alone: julia --project=. test/concreteness.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))
inner_err(e) = (while e isa LoadError; e = e.error; end; e)
caught(f) = try f(); nothing catch e; inner_err(e) end

toplevel(quote
    @trait_module module Conc
    using TraitWorld
    export CV, cfirst, CW, wfirst, CP, pval, total, totalw, selfonly, usecv, usecw
    @trait CV{T} begin
        @enforce_concrete_only T Self
        T = eltype(Self)
        cfirst(v::CV{T})::T
    end
    @implement CV A where {A <: AbstractVector} begin
        cfirst(v) = v[1]
    end
    @trait CW{T} begin
        @warn_on_abstract T
        T = eltype(Self)
        wfirst(v::CW{T})::T
    end
    @implement CW A where {A <: Vector} begin
        wfirst(v) = v[1]
    end
    @trait CP{U, P} begin                  # parameters from fields; only P required
        @enforce_concrete_only P
        u::U
        @const p::P
        pval(x::CP)::Int
    end
    @trait KV{T} begin                     # no requirement of its own: a function's
        T = eltype(Self)
        kfirst(v::KV{T})::T
    end
    @implement KV A where {A <: Vector} begin
        kfirst(v) = v[1]
    end
    usecv(v::CV) = cfirst(v)
    usecw(v::CW) = wfirst(v)
    @enforce_concrete_only T total(v::KV{T}) where {T} = kfirst(v)
    @warn_on_abstract T totalw(v::KV{T}) where {T} = kfirst(v)
    @enforce_concrete_only v selfonly(v::KV) = kfirst(v)
    end
end)
using .Conc

mutable struct PBox{U, P}; u::U; const p::P; end
Conc.pval(x::PBox) = 1

@testset "concrete parameters and Self, per trait" begin
    @test TraitWorld.trait_concreteness(Conc.CV) === ((:T, :error), (:Self, :error))
    # a family member: refused at its first use where a named part is abstract
    f(v::Vector{Float64}) = Conc.usecv(v)
    @test f([2.0]) === 2.0
    e = caught(() -> Conc.usecv(Any[1.0]))                           # T = Any
    @test e isa ImplementError && occursin("parameter T is Any", sprint(showerror, e))
    e = caught(() -> Conc.usecv(view([1.0, 2.0], 1:2)))              # Self is a SubArray: concrete; T = Float64
    @test e === nothing
    # a small union counts as concrete (at most four concrete members: its splits are facts)
    @test Conc.usecv(Union{Missing, Float64}[2.0, missing]) === 2.0
    e = caught(() -> Conc.usecv(Union{Int8, Int16, Int32, Int64, Int128}[1]))   # five members
    @test e isa ImplementError && occursin("is not concrete", sprint(showerror, e))
    @test !TraitWorld.key_concrete(Union{Missing, Real}) && TraitWorld.key_concrete(Vector{Union{Nothing, Int}})
    # a warning, the implementation kept
    @test (@test_logs (:warn, r"parameter T is Real") match_mode = :any Conc.usecw(Real[1.5])) == 1.5
    # parameters from fields: P must be concrete, U may be abstract
    toplevel(:(@implement Conc.CP PBox{Real, Int}))
    e = caught(() -> toplevel(:(@implement Conc.CP PBox{Int, Real})))
    @test e isa ImplementError && occursin("parameter P is Real", sprint(showerror, e))
    @test TraitWorld.implementation(Conc.CP, PBox{Int, Real}) === nothing    # refused: nothing defined
    # names are checked at the trait's declaration
    e = caught(() -> toplevel(:(@trait Bad1{T} begin @enforce_concrete_only S; b1(x::Bad1)::Int; end)))
    @test e isa ErrorException && occursin("neither a parameter", e.msg)
    e = caught(() -> toplevel(:(@trait Bad2 begin @concrete_only; b2(x::Bad2)::Int; end)))
    @test e isa ErrorException && occursin("@enforce_concrete_only", e.msg)
end

@testset "concrete parameters of the bounds, per function" begin
    g(v::Vector{Float64}) = Conc.total(v)
    @test g([3.0]) === 3.0
    @test Conc.total([3.0]) === 3.0
    e = caught(() -> Conc.total(Any[3.0]))
    @test e isa TraitBoundError && occursin("`T` is Any", sprint(showerror, e))
    @test (@test_logs (:warn, r"`T` is Real") match_mode = :any Conc.totalw(Real[2])) == 2
    @test Conc.selfonly([1]) === 1
    e = caught(() -> Conc.selfonly(Vector{Real}([1])))
    @test e isa TraitBoundError && occursin("Self is Vector{Real}", sprint(showerror, e))
    @test Conc.selfonly(with_dynamic([1])) === 1                       # a Dynamic's Self is unknown by choice
    # a name that is neither a bounded argument nor a where variable of a bound
    e = caught(() -> toplevel(quote
        @trait_module module ConcBad
        using TraitWorld
        using ..Conc: KV
        @enforce_concrete_only w h(v::KV) = 1
        end
    end))
    @test e isa ErrorException && occursin("neither a bounded argument", e.msg)
    # the old spellings name the new ones
    e = caught(() -> toplevel(:(@error_on_abstract @trait_module module Old1 end)))
    @test occursin("@enforce_fully_typed", sprint(showerror, e))
end
