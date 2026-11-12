# Ownership and pirates (traits §12.1, §12.2; W-114): a membership is declared by the trait's owner or
# the type's owner, or by a joint owner either names; a scope that declares `no_pirates` refuses a
# pirate at its definition. Each module directly under `Main` is an owner of its own.
using TraitWorld, Test

@eval Main module OwnTrait
using TraitWorld
@trait Greets begin
    greet(x::Greets)::String
end
end
@eval Main module OwnType
using TraitWorld
@joint_owners OwnJoint
struct P end
struct Q end
end
@eval Main module OwnThird
using TraitWorld
import ..OwnTrait, ..OwnType
OwnTrait.greet(::OwnType.P) = "hi"
end
@eval Main module OwnJoint
using TraitWorld
import ..OwnTrait, ..OwnType
OwnTrait.greet(::OwnType.Q) = "hello"
end
@eval Main module PirateScope
using TraitWorld
@trait_module
struct Mine end
end

@testset "ownership" begin
    @test TraitWorld.owner(Main.OwnType) === Main.OwnType
    @test TraitWorld.owner(Base) === :Julia && TraitWorld.owner(TraitWorld.CC) === :Julia
    # a third package's membership of a foreign trait for a foreign type is a pirate's (traits §12.1):
    # refused under strict mode, followed with a warning otherwise
    TraitWorld.strict!(true)
    @test_throws OwnershipError Core.eval(Main.OwnThird, :(@implement OwnTrait.Greets OwnType.P))
    TraitWorld.strict!(false)
    @test !Base.invokelatest(<:, Main.OwnType.P, Main.OwnTrait.Greets)
    @test_logs (:warn, r"a pirate's membership") Core.eval(Main.OwnThird, :(@implement OwnTrait.Greets OwnType.P))
    @test Base.invokelatest(<:, Main.OwnType.P, Main.OwnTrait.Greets)
    # the type's owner may
    Core.eval(Main.OwnType, :(import ..OwnTrait; @implement OwnTrait.Greets P))
    @test Main.OwnType.P() isa Main.OwnTrait.Greets
    # a joint owner the type's owner names may
    Core.eval(Main.OwnJoint, :(@implement OwnTrait.Greets OwnType.Q))
    @test Main.OwnType.Q() isa Main.OwnTrait.Greets
end

@testset "pirates" begin
    # refused at the definition in a scope that declares no_pirates; the method does not exist
    n = length(methods(length))
    @test_throws OwnershipError Core.eval(Main.PirateScope, :(Base.length(x::Int) = 1))
    @test length(methods(length)) == n
    # a Union with an own type is no way around it
    @test_throws OwnershipError Core.eval(Main.PirateScope, :(Base.length(x::Union{Mine, Int}) = 1))
    # an own type's method is no pirate
    Core.eval(Main.PirateScope, :(Base.length(::Mine) = 7))
    @test length(Main.PirateScope.Mine()) == 7
    @test !TraitWorld.owned_method(which(Main.OwnTrait.greet, (Main.OwnType.P,)))
    # `Core.implements` holds the runtime's methods, one per membership (W-141): a program defines none,
    # and declares nothing by trying
    @test_throws ErrorException Core.eval(Main.PirateScope,
        :(Core.implements(::Type{$(Main.OwnTrait.Greets)}, ::Type{Rational{Int}}) = nothing))
    @test !(Rational{Int} <: Main.OwnTrait.Greets)
end
