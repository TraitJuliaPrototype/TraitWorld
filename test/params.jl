# Trait parameters, associated types (note "Declaring a trait": Parameters; "Parametric
# user types": families with associated types), shaped like the solver's state vector:
# StateVector{T, R} with T = eltype(R), a family conformance for Vector{T}, a user's joint
# family Series{T}, a bound that fixes T, Dynamic values of a parametric trait.
# Runs inside runtests.jl, or alone: julia --project=. test/params.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module ParamLib
    using TraitWorld
    export StateVector, nel, getel, total, fixedsum, keepf, ArrayLike, alen, firstof

    @trait StateVector{T, R} begin
        T = eltype(R)                      # a defining equation: the associated type at the representation
        nel(r::R)::Int
        getel(r::R, i::Int)::T             # the declared result names the parameter
    end
    @implement StateVector{T, Vector{T}} where {T <: Real} begin   # a family conformance, with methods
        nel(r) = length(r)
        getel(r, i) = r[i]
    end

    total(s::StateVector) = (acc = zero(getel(s, 1)); for i in 1:nel(s); acc += getel(s, i); end; acc)
    fixedsum(s::StateVector{Float64}) = total(s) + 0.0     # a bound that fixes T: checked at its archetype
    keepf(s::StateVector{Float64}) = Dynamic{StateVector{Float64}}(s)

    @trait ArrayLike{T, N, R} begin        # no equations: a conformance states the parameters
        alen(r::R)::Int
        firstof(r::R)::T
    end
    end
    using .ParamLib

    @trait_module module ParamBad
    using TraitWorld, ..ParamLib
    export badsize
    badsize(s::StateVector{Float64}) = size(s)              # not an operation: found at the definition
    end
    using .ParamBad
end)

toplevel(quote
    struct Series{T}; data::Vector{T}; end
    ParamLib.nel(s::Series) = length(s.data)
    ParamLib.getel(s::Series, i::Int) = s.data[i]
    @implement StateVector{T} Series{T} where {T}           # the joint form: T tied to the type's parameter

    struct MyVec; v::Vector{Float32}; end
    ParamLib.alen(m::MyVec) = length(m.v)
    ParamLib.firstof(m::MyVec) = m.v[1]
    @implement ArrayLike{Float32, 1} MyVec                  # the parameters stated by the conformance
end)

@testset "Trait parameters (associated types)" begin
    P = Main.ParamLib
    SV = P.StateVector
    @test TraitWorld.param(SV, Val(:T), Vector{Int}) === Int
    @test TraitWorld.param(SV, Val(:T), Main.Series{Float32}) === Float32
    @test TraitWorld._instance(SV, Vector{Float64}) === SV{Float64, Vector{Float64}}
    @test P.total([1.0, 2.0]) == 3.0
    @test P.total([1, 2, 3]) === 6
    @test P.total(Main.Series(Float32[1, 2])) === 3.0f0
    @test P.fixedsum([1.0, 2.0]) == 3.0
    @test P.fixedsum(Main.Series([1.0, 4.0])) == 5.0
    @test_throws TraitBoundError P.fixedsum([1, 2])            # the bound fixes T = Float64: refused at the entry
    d = P.keepf([2.0, 3.0])
    @test d isa Dynamic{SV{Float64}}
    @test P.nel(d) == 2 && P.getel(d, 2) == 3.0
    @test P.total(d) == 5.0                                     # a Dynamic opened at a bound
    @test TraitWorld.param(P.ArrayLike, Val(:T), Main.MyVec) === Float32
    @test TraitWorld.param(P.ArrayLike, Val(:N), Main.MyVec) === 1
    @test P.firstof(Main.MyVec(Float32[7])) === 7.0f0
    # definition checking: a fixed parameter is checked once; open ones are checked per signature
    e = try check_definitions(Main.ParamBad); nothing catch err; err end
    @test e isa TraitUseError && occursin("size", join(e.problems))
    @test isempty(check_definitions(Main.ParamLib))
    checked = Set(m.name for m in TraitWorld._DEF_CHECKED if parentmodule(m) === Main.ParamLib)
    @test :fixedsum in checked && !(:total in checked)
end

# An equation always holds: a stated parameter is checked against the trait's equation, never replaces it
@testset "a stated parameter agrees with the trait's equation" begin
    e = try toplevel(quote
        struct SVa; data::Vector{Float64}; end
        Base.eltype(::Type{SVa}) = Float64
        ParamLib.nel(s::SVa) = length(s.data)
        ParamLib.getel(s::SVa, i::Int) = s.data[i]
        @implement StateVector{Float64} SVa              # the equation gives Float64 too: accepted
    end); nothing catch err; err end
    @test e === nothing
    @test TraitWorld.param(Main.ParamLib.StateVector, Val(:T), Main.SVa) === Float64
    e = try toplevel(quote
        struct SVb; data::Vector{Float64}; end
        Base.eltype(::Type{SVb}) = Float64
        ParamLib.nel(s::SVb) = length(s.data)
        ParamLib.getel(s::SVb, i::Int) = s.data[i]
        @implement StateVector{Float32} SVb              # the equation gives Float64: refused
    end); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    @test e isa ImplementError && occursin("an equation always holds", sprint(showerror, e))
    @test TraitWorld.param(Main.ParamLib.StateVector, Val(:T), Main.SVb) === Float64   # the equation stands
end
