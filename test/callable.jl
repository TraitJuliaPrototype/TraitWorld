# Callable (traits §9; lowering §9; W-113): membership by a function's own methods, dispatch by
# signature, the result checked on return, `Dynamic{Callable{A, S}}`'s call, the default `Dynamic`.
using TraitWorld, Test

colmap(f::Callable{Tuple{Float64}, Float64}, v::Vector{Float64}) = [f(x) for x in v]
apply(f::Callable{Tuple{Int}, Int}, x) = "an integer map"
apply(f::Callable{Tuple{String}, <:AbstractString}, x) = "a string map"
kind(f::Callable{Tuple{Float64}, Float64}) = keep(f) isa Dynamic ? :dynamic : :compiled
# the check is at a call through the value as declared; a closure that captures it (a comprehension)
# knows it by its own type, as `map` does
first_of(f::Callable{Tuple{Float64}, Float64}, v::Vector{Float64}) = f(v[1])

@testset "Callable" begin
    @test colmap(x -> 2x, [1.0, 2.0]) == [2.0, 4.0]
    @test apply(abs, 1) == "an integer map"
    @test apply(uppercase, "a") == "a string map"
    @test abs isa Callable{Tuple{Int}, Int} && !(uppercase isa Callable{Tuple{Int}, Int})
    # the result checked on return
    @test_throws TypeError first_of(x -> "s", [1.0])
    @test first_of(x -> 2x, [1.0]) == 2.0
    # Callable's default is Dynamic, but not for a function Julia defines
    @test kind(x -> 2x) === :dynamic
    @test kind(abs2) === :compiled
    # Dynamic{Callable{A, S}}: a member of Callable{A, S}, its call checked at both ends
    d = Dynamic{Callable{Tuple{Float64}, Float64}}(x -> 3x)
    @test d isa Callable{Tuple{Float64}, Float64}
    @test d(2.0) == 6.0
    @test colmap(d, [1.0]) == [3.0]
    @test_throws MethodError d(1)                           # not at A
    bad = Dynamic{Callable{Tuple{Float64}, Float64}}(x -> "s")
    @test_throws TypeError bad(1.0)                         # not an S
end
