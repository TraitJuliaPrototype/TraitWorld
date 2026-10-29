# W-91: a function argument's entry (`enter_callable`) is keyed by its bound, `Callable{A, S}`, so a package
# image keeps it where `A` is a tuple type without a hash as a type value (`Tuple{Union{Missing, Float64}}`):
# the patched Julia's images keep no external code at a signature without a hash (compiler reference §2.9).
# A toy trait module whose precompile workload calls its bounded function, precompiled in a depot of its own;
# a fresh session that loads it finds the entry with machine code before any call, and does not compile it
# at the first call with a new function (the note: writeup/plans/2026-10-29-w91-callable-entries-cacheable.md).
# Runs inside runtests.jl, or alone: julia --project=. test/callable_images.jl
using Test, TraitWorld
if !TraitWorld._HAS_FOLD
    @info "Callable entries in images: not the patched Julia; skipped"
else
mktempdir() do dir
    pkgs = joinpath(dir, "pkgs"); depot = joinpath(dir, "depot")
    mkpath(joinpath(pkgs, "CallImg", "src"))
    write(joinpath(pkgs, "CallImg", "src", "CallImg.jl"), """
        module CallImg
        using TraitWorld
        @trait_module module Inner
        using TraitWorld
        export count_in
        count_in(f::Callable{Tuple{T}, Bool}, xs::Iterable{T}) where {T} = (n = 0; for x in xs; f(x) && (n += 1); end; n)
        end
        using .Inner
        # a plain caller that knows neither type, as DataFrames' `_byrow` calls `byrow`: the entry reads `T` from
        # the argument's key and enters the function at `Callable{Tuple{T}, Bool}` by a dynamic call, which the
        # workload records (no caller in the image has an edge to it)
        plain_count(@nospecialize(f), xs::AbstractVector) = Inner.count_in(f, xs)
        TraitWorld.@workload begin
            plain_count(x -> !ismissing(x) && x > 1, Union{Missing, Float64}[1.0, missing, 3.0])
        end
        end
        """)
    tw = dirname(Base.active_project())
    env = copy(ENV)
    env["JULIA_LOAD_PATH"] = join([pkgs, tw, "@stdlib"], Sys.iswindows() ? ";" : ":")
    env["JULIA_DEPOT_PATH"] = join([depot, Base.DEPOT_PATH...], Sys.iswindows() ? ";" : ":")
    env["JULIA_PKG_OFFLINE"] = "true"
    delete!(env, "JULIA_PROJECT")
    function session(code; trace = nothing)
        cmd = trace === nothing ? `$(Base.julia_cmd()) --startup-file=no --compiled-modules=yes -e $code` :
                                  `$(Base.julia_cmd()) --startup-file=no --compiled-modules=yes --trace-compile=$trace -e $code`
        out = IOBuffer(); err = IOBuffer()
        ok = success(pipeline(setenv(cmd, env); stdout = out, stderr = err))
        s = String(take!(out)); e = String(take!(err))
        ok || @info "session failed" s e
        return ok, s
    end
    ok, _ = session("using CallImg")
    @test ok
    @testset "W-91: an image keeps a Callable entry whose argument types have no hash" begin
        trace = joinpath(dir, "trace.jl")
        ok, s = session("""
            using CallImg, TraitWorld
            const TW = TraitWorld
            # the entry's instances with machine code, valid now, before any call
            function native(m, pred)
                n = 0
                for mi in Base.specializations(m)
                    pred(mi.specTypes) || continue
                    ci = isdefined(mi, :cache) ? mi.cache : nothing
                    while ci isa Core.CodeInstance
                        ci.owner === nothing && ci.max_world == typemax(UInt) && ci.invoke != C_NULL && (n += 1)
                        ci = isdefined(ci, :next) ? ci.next : nothing
                    end
                end
                n
            end
            B = TW.Callable{Tuple{Union{Missing, Float64}}, Bool}
            println("ENTRY ", native(only(methods(TW.enter_callable)), T -> T.parameters[2] === Type{B}))
            # the julia rule itself: an external instance at a signature without a hash is not kept
            println("NOHASH ", getfield(Base.unwrap_unionall(Tuple{typeof(TW._callable_result), Any, Type{Tuple{Union{Missing, Float64}}}}), :hash))
            # a new function at the prompt, through the plain caller as in the workload
            v = Union{Missing, Float64}[2.0, missing, 0.5, 4.0]
            println("COUNT ", CallImg.plain_count(x -> ismissing(x) || x > 1, v))
            """; trace)
        @test ok
        @test occursin(r"ENTRY [1-9]", s)
        @test occursin("NOHASH 0", s)
        @test occursin("COUNT 3", s)
        # the call compiled neither the entry nor its helpers (the user's new function is compiled, as it must)
        t = read(trace, String)
        @test !occursin("enter_callable", t)
        @test !occursin("_wrap_callable", t)
    end
end
end
