# Open issue 123: compiling ahead for an implementation while a package image is built reads TraitWorld's
# records of the entry positions, not every binding of every loaded module, so a dependency's deprecated
# bindings print nothing under `--depwarn=yes` (Pkg.test's setting; TraitMakie's PlotCore printed Cairo's).
# Runs inside runtests.jl, or alone: julia --project=. test/depwarn.jl
using Test, TraitWorld
mktempdir() do dir
    pkgs = joinpath(dir, "pkgs"); depot = joinpath(dir, "depot")
    for (name, src) in (
        ("DepOld", """
            module DepOld
            export newname
            newname(x) = x
            Base.@deprecate_binding oldname newname
            end
            """),
        ("ImplDep", """
            module ImplDep
            using TraitWorld
            @trait_module module Inner
            using TraitWorld
            using DepOld: DepOld
            export Sized, width, wider
            @trait Sized begin
                width(s::Sized)::Int
            end
            struct Surf; w::Int; end
            @implement Sized Surf begin
                width(s) = s.w
            end
            wider(s::Sized, k::Int) = width(s) + k
            end
            end
            """))
        mkpath(joinpath(pkgs, name, "src"))
        write(joinpath(pkgs, name, "src", "$name.jl"), src)
    end
    tw = dirname(Base.active_project())
    env = copy(ENV)
    env["JULIA_LOAD_PATH"] = join([pkgs, tw, "@stdlib"], Sys.iswindows() ? ";" : ":")
    env["JULIA_DEPOT_PATH"] = join([depot, Base.DEPOT_PATH...], Sys.iswindows() ? ";" : ":")
    env["JULIA_PKG_OFFLINE"] = "true"
    delete!(env, "JULIA_PROJECT")
    cmd = `$(Base.julia_cmd()) --startup-file=no --compiled-modules=yes --depwarn=yes -e "using ImplDep; println(ImplDep.Inner.wider(ImplDep.Inner.Surf(2), 1))"`
    out = IOBuffer(); err = IOBuffer()
    ok = success(pipeline(setenv(cmd, env); stdout = out, stderr = err))
    s = String(take!(out)); e = String(take!(err))
    ok || @info "session failed" s e
    @testset "an implementation's image build reads no deprecated binding (open issue 123)" begin
        @test ok
        @test strip(s) == "3"
        @test !occursin("deprecated", e)
    end
end
