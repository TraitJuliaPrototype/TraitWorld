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

# A family with a block whose target is a parametric type expression, `S{P} where {P} begin … end`,
# and the joint family with a block, `X{P} S{P} where {P} begin … end` (traits §4.7; T-5, E-156 P1a)
toplevel(quote
    module PFamTypes
    struct S{T}; x::T; end
    struct Ser{T}; data::Vector{T}; end
    end
    @trait_module module PFamBlock
    using TraitWorld
    using ..PFamTypes
    export Fam, fval, usef, SV, sget, uses
    @trait Fam begin
        fval(s::Fam)::Float64
    end
    @trait SV{T} begin
        sget(s::SV{T}, i::Int)::T
    end
    usef(s::Fam) = fval(s)
    uses(s::SV{T}) where {T} = (T, sget(s, 1))
    @implement Fam PFamTypes.S{T} where {T} begin
        fval(s) = Float64(s.x)
    end
    @implement SV{T} PFamTypes.Ser{T} where {T} begin
        sget(s, i) = s.data[i]
    end
    end
end)
@testset "families with a block over a parametric type expression" begin
    P = Main.PFamBlock
    @test P.usef(Main.PFamTypes.S(2)) === 2.0
    @test P.usef(Main.PFamTypes.S(0.5f0)) === 0.5
    @test P.uses(Main.PFamTypes.Ser([1.5])) === (Float64, 1.5)
    @test P.uses(Main.PFamTypes.Ser(Int8[3])) === (Int8, Int8(3))
    typed_uses(s::Main.PFamTypes.Ser{Float32}) = P.uses(s)
    @test typed_uses(Main.PFamTypes.Ser(Float32[2])) === (Float32, 2.0f0)
end

# the same declared by the type's owner outside the trait's module; a third package is refused (rule 3)
toplevel(quote
    module PFamOwner
    using TraitWorld, ..PFamBlock
    struct S2{T}; x::T; end
    struct Ser2{T}; data::Vector{T}; end
    @implement PFamBlock.Fam S2{T} where {T} begin
        fval(s) = 2.0 * s.x
    end
    @implement PFamBlock.SV{T} Ser2{T} where {T} begin
        sget(s, i) = s.data[i]
    end
    end
end)
@testset "families with a block, by the type's owner" begin
    P = Main.PFamBlock
    @test P.usef(Main.PFamOwner.S2(2)) === 4.0
    @test P.uses(Main.PFamOwner.Ser2([2.5])) === (Float64, 2.5)
    e = try toplevel(quote
        module PFamThird
        using TraitWorld, ..PFamBlock, ..PFamTypes
        struct Mine; end
        @implement PFamBlock.SV{T} PFamTypes.Ser{T} where {T} begin    # neither the trait's nor the type's owner
            sget(s, i) = s.data[i]
        end
        end
    end); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    @test e isa ImplementError && occursin("rule 3", sprint(showerror, e))
end

# A kept form fixes the trait's parameters (traits reference §7.1, T-70, W-48): a value whose type
# implements the trait only at other parameters is refused when the kept value is made
@testset "kept forms check the fixed parameters" begin
    toplevel(quote
        @trait_module module KPar
        using TraitWorld
        export KShape, karea
        @trait KShape{P} begin
            karea(s::KShape{P}, p::P)::Float64
        end
        struct KSq end
        karea(s::KSq, p::Vector{Float64}) = p[1]^2
        @implement KShape{Vector{Float64}} KSq
        end
    end)
    M = Base.invokelatest(getglobal, Main, :KPar)
    S, Sq = Base.invokelatest(getglobal, M, :KShape), Base.invokelatest(getglobal, M, :KSq)
    for K in (Kept, Dynamic, Compiled)
        @test_throws TraitBoundError Base.invokelatest(K{S{Int}}, Base.invokelatest(Sq))
        k = Base.invokelatest(K{S{Vector{Float64}}}, Base.invokelatest(Sq))
        @test Base.invokelatest(Base.invokelatest(getglobal, M, :karea), k, [3.0]) == 9.0
    end
end

# Inside a trait module a trait's name with parameters as a container's element type means
# `Kept{X{…}}`, in a function body too (traits reference §7.2, T-69, W-48)
@testset "a parametric trait's name as an element type" begin
    toplevel(quote
        @trait_module module TArr
        using TraitWorld
        export AShape
        @trait AShape{P} begin
            aarea(s::AShape{P}, p::P)::Float64
        end
        struct ASq end
        aarea(s::ASq, p::Float64) = p^2
        @implement AShape{Float64} ASq
        const_param() = AShape{Float64}[]
        where_param(::Type{P}) where {P} = AShape{P}[]
        vec_param() = Vector{AShape{Float64}}()
        end
    end)
    M = Base.invokelatest(getglobal, Main, :TArr)
    S = Base.invokelatest(getglobal, M, :AShape)
    for f in (:const_param, :vec_param)
        v = Base.invokelatest(Base.invokelatest(getglobal, M, f))
        @test eltype(v) == Kept{S{Float64}}
        push!(v, Base.invokelatest(Base.invokelatest(getglobal, M, :ASq)))
        @test length(v) == 1
    end
    @test eltype(Base.invokelatest(Base.invokelatest(getglobal, M, :where_param), Float64)) == Kept{S{Float64}}
end
