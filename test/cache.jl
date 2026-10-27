# The cache across sessions (src/cache.jl): a session records at exit, the builder makes the parts, and the next
# session loads them and compiles nothing for a call shape the first session compiled.
# Runs inside runtests.jl, or alone: julia --project=. test/cache.jl
using Test, TraitWorld

@testset "the cache across sessions" begin
    if !isdefined(Base.Compiler, :FACTS_OWNER)
        @info "the cache: no facts owner in this runtime (stock Julia); skipped"
    else
        dir = mktempdir()
        # a call shape TraitWorld's workload does not run: `pcmap` with `sin`
        script = """
            using TraitWorld
            Base.cumulative_compile_timing(true)
            t = Base.cumulative_compile_time_ns()[1]
            r = TraitWorld._PC.pcmap(sin, [0.5, 2.0])
            c = (Base.cumulative_compile_time_ns()[1] - t) / 1e6
            println("R ", r == sin(0.5), " ", get(TraitWorld._CACHE_STATS, :loaded, 0.0), " ", c)
            """
        env = copy(ENV)
        env["JULIA_TW_CACHE"] = "1"; env["JULIA_TW_CACHE_BUILD"] = "sync"; env["JULIA_TW_CACHE_DIR"] = dir
        jl = filter(a -> !startswith(a, "--check-bounds") && !startswith(a, "--code-coverage"), Base.julia_cmd().exec)
        cmd = setenv(`$jl --startup-file=no --project=$(dirname(@__DIR__)) -e $script`, env)
        run1 = split(only(filter(startswith("R "), readlines(cmd))))
        run2 = split(only(filter(startswith("R "), readlines(cmd))))
        @test run1[2] == "true" && run2[2] == "true"
        @test parse(Float64, run1[3]) == 0                        # no cache yet
        @test parse(Float64, run2[3]) >= 1                        # the parts the first session's builder made
        @test parse(Float64, run2[4]) < parse(Float64, run1[4]) / 4   # the call shape's code came from them
        k = only(readdir(dir; join = true))
        @test isfile(joinpath(k, "index.txt")) && !isempty(readdir(joinpath(k, "parts")))
        @test isempty(readdir(joinpath(k, "records")))           # merged by the builder
        @test !isfile(joinpath(k, "build.lock"))
        rm(dir; recursive = true, force = true)
    end
end
