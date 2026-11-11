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

@testset "a function written at the prompt: the session's definitions" begin
    inputs = ["using TraitWorld",
              "struct P; x::Float64; end",
              "x = 3",                                   # an assignment to a global: not replayed
              "f(p::P) = p.x + 1; println(f(P(1.0)))",   # a definition, then a call
              "function main(args::Vector{String})\n    println(Core.stdout, f(P(2.0)))\n    return 0\nend",
              "const K = 2",
              "@trait T begin\n    op(t::T)::Int\nend",
              "make_executable(main, \"out\")",
              "Base.@inline g(x) = x",
              "h = y -> y"]
    # (a statement taken from a line of several is printed from its expression: compared as parsed)
    same(a, b) = length(a) == length(b) && all(Base.remove_linenums!(Meta.parse(x)) == Base.remove_linenums!(Meta.parse(y)) for (x, y) in zip(a, b))
    defs, skipped = TraitWorld._definitions(inputs)
    @test same(defs, ["using TraitWorld", "struct P; x::Float64; end", "f(p::P) = p.x + 1",
                   "function main(args::Vector{String})\n    println(Core.stdout, f(P(2.0)))\n    return 0\nend",
                   "const K = 2", "@trait T begin\n    op(t::T)::Int\nend", "Base.@inline g(x) = x"])
    @test skipped == 4
    # what `main` depends on: `f` and `P`; not `K`, the trait `T` or `g`
    need, left = TraitWorld._needed_definitions(inputs, :main)
    @test same(need, ["using TraitWorld", "struct P; x::Float64; end", "f(p::P) = p.x + 1",
                      "function main(args::Vector{String})\n    println(Core.stdout, f(P(2.0)))\n    return 0\nend"])
    # a trait, its operation and the membership of a type reached; an unrelated type's membership is left out
    ins = ["@trait S begin\n    area(s::S)::Float64\nend", "struct A; end", "struct B; end",
           "@implement S A begin\n    area(a) = 1.0\nend", "@implement S B begin\n    area(b) = 2.0\nend",
           "main(args::Vector{String}) = (println(Core.stdout, area(A())); 0)"]
    need, left = TraitWorld._needed_definitions(ins, :main)
    @test need == [ins[1], ins[2], ins[4], ins[6]] && left == 2
    # with no prompt and no file, the build has nothing to load
    Core.eval(Main, Meta.parse("__tw_noprompt_main(args::Vector{String}) = 0"))
    @test_throws ArgumentError make_executable(Main.__tw_noprompt_main, "x")
end
