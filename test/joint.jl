# Joint owners (traits reference §10.1): a package names the packages that own its functions and types
# with it; their methods of its functions on its types are no pirates, in a trait module and for
# strict mode. Only the owner declares; not symmetric, not transitive.
# Runs inside runtests.jl, or alone: julia --project=. test/joint.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))
inner_err(e) = (while e isa LoadError; e = e.error; end; e)
caught(f) = try f(); nothing catch e; inner_err(e) end

toplevel(quote
    module JCore                          # the owner: a core package with an interface
    using TraitWorld
    @joint_owners JImpl JMid
    abstract type AbstractProb end
    struct Prob <: AbstractProb; x::Float64; end
    struct Box; v::Int; end
    function solve end
    end
    module JMid                           # a joint owner of JCore, which names joint owners of its own
    using TraitWorld
    @joint_owners JFar
    struct Thing; v::Int; end
    end
    module JFar end
    module JStranger end
end)

@testset "joint owners" begin
    @test TraitWorld._joint_names(JCore) == (:JImpl, :JMid)
    # a joint owner, as a trait module: the owner's function on the owner's types, a Base function on its types
    @test caught(() -> toplevel(quote
        @trait_module module JImpl
        using TraitWorld
        using ..JCore
        JCore.solve(p::JCore.AbstractProb) = 2 * p.x
        Base.isempty(b::JCore.Box) = b.v == 0
        end
    end)) === nothing
    @test JCore.solve(JCore.Prob(1.5)) == 3.0 && isempty(JCore.Box(0))
    @test TraitWorld.owned_method(which(JCore.solve, (JCore.Prob,)))
    @test TraitWorld._stakeholder(JImpl, Tuple{typeof(JCore.solve), JCore.Prob})
    # a package the owner did not name: a pirate, refused
    e = caught(() -> toplevel(quote
        @trait_module module JOther
        using TraitWorld
        using ..JCore
        JCore.solve(p::JCore.Prob) = 0.0
        end
    end))
    @test e isa OwnershipError
    @test !TraitWorld._stakeholder(JStranger, Tuple{typeof(JCore.solve), JCore.Prob})
    # not symmetric: the owner does not own its joint owner's types
    @test !TraitWorld.owns(JCore, JImpl)
    # not transitive: JFar is JMid's joint owner, not JCore's
    @test TraitWorld.owns(JFar, JMid) && !TraitWorld.owns(JFar, JCore)
    # only the owner's own module declares
    e = caught(() -> toplevel(:(module JOuter; using TraitWorld; module Inner; using TraitWorld; @joint_owners X; end; end)))
    @test e isa ErrorException && occursin("only a package's own module", e.msg)
    e = caught(() -> toplevel(:(module JBad; using TraitWorld; @joint_owners "X"; end)))
    @test e isa ErrorException && occursin("name the packages", e.msg)
end
