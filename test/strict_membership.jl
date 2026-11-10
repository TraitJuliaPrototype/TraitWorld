# Strict mode refuses a membership that makes methods ambiguous (traits §6.3, §12.3; compiler §4.3): the
# membership raises ImplementError and does not exist; the counter does not advance; with a joint method
# the same membership is declared. Without strict mode it is declared with the report's warning.
using TraitWorld, Test

function thrown(ex)
    try
        Core.eval(@__MODULE__, ex)
        return nothing
    catch e
        while e isa LoadError; e = e.error; end
        return e
    end
end
latest(f, args...) = Base.invokelatest(f, args...)
member(S, X) = Base.invokelatest(() -> S <: X)
cands(X) = ccall(:jl_candidates_of, Any, (Any,), X)

@trait XS
@trait YS
f(::XS) = :x
f(::YS) = :y
struct SA end
@implement YS SA
struct SB end
@implement YS SB
g() = f(SB())

@trait XR
@trait YR
k(::XR) = :x
k(::YR) = :y
struct SR end
@implement YR SR

@trait XP
@trait YP
p(::XP) = :x
p(::YP) = :y
struct FamP{T}; x::T; end
@implement YP FamP{T} where {T}

@testset "strict mode at a membership" begin
    @test latest(g) === :y                                  # SB called before its second membership
    TraitWorld.strict!(true)
    try
        w = Base.get_world_counter()
        e = thrown(:(@implement XS SA))
        @test e isa ImplementError && occursin("ambiguous", sprint(showerror, e))
        @test occursin("All{", sprint(showerror, e))       # the joint method that would resolve it
        @test Base.get_world_counter() == w                 # a refused membership advances no world
        @test !member(SA, XS) && member(SA, YS)
        c = cands(XS)
        @test c === nothing || !(SA in c)
        @test latest(f, SA()) === :y
        # called before: the search reads no dispatch cache
        @test thrown(:(@implement XS SB)) isa ImplementError
        @test latest(g) === :y && !member(SB, XS)
        # a pattern member
        @test thrown(:(@implement XP FamP{T} where {T})) isa ImplementError
        @test !member(FamP{Int}, XP)
        # a joint method resolves it: the same membership is declared (the refused entry is in no world)
        @eval f(::All{XS, YS}) = :xy
        @test thrown(:(@implement XS SA)) === nothing
        @test member(SA, XS) && latest(f, SA()) === :xy
    finally
        TraitWorld.strict!(false)
    end
end

@testset "a redeclaration refused keeps the membership" begin
    @test thrown(:(@implement XR SR)) === nothing           # without strict mode: declared, with the report's warning
    @test member(SR, XR)
    TraitWorld.strict!(true)
    try
        @test thrown(:(@implement XR SR)) isa ImplementError
        @test member(SR, XR) && member(SR, YR)              # the old entry still in force
    finally
        TraitWorld.strict!(false)
    end
end
