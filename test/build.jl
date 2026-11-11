# `make_executable` and `make_library` (traits §16): what they take and refuse before a build. The
# builds themselves run in `experiments/unification/w139/make.jl` (E-364): each is a process of its own.
using TraitWorld, Test

@testset "make_executable, make_library: the checks before a build" begin
    @test_throws ArgumentError make_executable(args -> 0, "x")                  # an anonymous function
    nomain(x::Int) = 0
    @test_throws ArgumentError make_executable(nomain, "x")                     # no method at Vector{String}
    @test_throws ArgumentError make_library([sin => (Float64, (Vector{Float64},))], "x")   # not C's
    @test_throws ArgumentError make_library([], "x")
    @test TraitWorld._c_compatible(Cint) && TraitWorld._c_compatible(Ptr{Cvoid}) && TraitWorld._c_compatible(Cstring)
    @test !TraitWorld._c_compatible(String) && !TraitWorld._c_compatible(Any)
    @test isfile(TraitWorld._juliac_buildscript())
end
