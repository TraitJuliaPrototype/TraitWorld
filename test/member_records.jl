# W-84: a family member fixed while a package image is built is recorded in that image, and a session that
# loads the image fixes it from the record, without its check, while the methods that serve it are the same
# (the plan: writeup/plans/2026-10-29-w84-member-checks-at-load.md). Toy packages, precompiled in a depot
# of their own in fresh processes. Needs the patched Julia's `Compiler.fold_call`.
# Runs inside runtests.jl, or alone: julia --project=. test/member_records.jl
using Test, TraitWorld
if !TraitWorld._HAS_FOLD
    @info "member records: no Compiler.fold_call in this Julia; skipped"
else
mktempdir() do dir
    pkgs = joinpath(dir, "pkgs"); depot = joinpath(dir, "depot")
    function pkg(name, src)
        mkpath(joinpath(pkgs, name, "src"))
        write(joinpath(pkgs, name, "src", name * ".jl"), src)
    end
    # the family: every `Box{T}` conforms to `MV` by its own methods
    pkg("FamA", """
        module FamA
        using TraitWorld
        @trait_module begin
        export MV, mval, msum, Box
        @trait MV begin
            mval(v::MV)::Float64
        end
        struct Box{T}; x::T; end
        mval(b::Box) = Float64(b.x)
        @implement MV B where {B <: Box}
        msum(v::MV, n::Int) = (s = 0.0; for _ in 1:n; s += mval(v); end; s)
        end
        end
        """)
    # a caller that knows the member's type: its image keeps the fold of `Box{Int}`'s builder
    pkg("UseA", """
        module UseA
        using FamA
        use(b::FamA.Box{Int}) = FamA.msum(b, 3)
        precompile(use, (FamA.Box{Int},))
        end
        """)
    # a pirate (it owns neither `mval` nor `Box`): `mval(::Box{Int})` returns a String, so the member no longer conforms
    pkg("PirateA", """
        module PirateA
        using FamA
        FamA.mval(b::FamA.Box{Int}) = string(b.x)
        end
        """)
    tw = dirname(Base.active_project())
    env = copy(ENV)
    env["JULIA_LOAD_PATH"] = join([pkgs, tw, "@stdlib"], Sys.iswindows() ? ";" : ":")
    env["JULIA_DEPOT_PATH"] = join([depot, Base.DEPOT_PATH...], Sys.iswindows() ? ";" : ":")
    env["JULIA_PKG_OFFLINE"] = "true"
    env["JULIA_TW_LOADREPORT"] = "1"
    delete!(env, "JULIA_PROJECT")
    function session(code)
        cmd = `$(Base.julia_cmd()) --startup-file=no --compiled-modules=yes -e $code`
        out = IOBuffer(); err = IOBuffer()
        ok = success(pipeline(setenv(cmd, env); stdout = out, stderr = err))
        s = String(take!(out)); e = String(take!(err))
        ok || @info "session failed" s e
        return ok, s
    end
    probe = """
        using TraitWorld
        const TW = TraitWorld
        r(k) = (v = get(TW._LR_PARTS, (:member_at_load, k), nothing); v === nothing ? 0 : Int(v[1]))
        println("FROM_RECORD ", r(:from_record), " CHECKED ", r(:check), " TOTAL ", r(:total))
        """
    # precompile the three packages (each image built in its own process)
    ok, _ = session("using FamA, UseA, PirateA")
    @test ok
    @testset "W-84: a member fixed while an image was built is fixed from its record at load" begin
        ok, s = session("""
            using UseA, FamA
            $probe
            println("USE ", UseA.use(FamA.Box(2)))
            # the record's builder is the builder the check finds
            b = TW._family_builder(FamA.MV, FamA.Box{Int})
            ms = Base._methods_by_ftype(Tuple{typeof(TW._member_record),Type{FamA.MV},Type{FamA.Box{Int}},Any}, -1, Base.get_world_counter())
            println("RECORDS ", length(ms))
            K = Base.unwrap_unionall(ms[1].method.sig).parameters[4]
            println("SAME_BUILDER ", TW._member_record(FamA.MV, FamA.Box{Int}, K.instance).builder === b)
            """)
        @test ok
        @test occursin("FROM_RECORD 1 CHECKED 0 TOTAL 0", s)
        @test occursin("USE 6.0", s)
        @test occursin("RECORDS 1", s)
        @test occursin("SAME_BUILDER true", s)
    end
    @testset "W-84: a pirate loaded before the image changes a method that served the member: checked again, refused" begin
        ok, s = session("""
            using PirateA
            using UseA, FamA
            $probe
            e = try UseA.use(FamA.Box(2)); nothing catch err; err end
            println("REFUSED ", e isa ImplementError)
            """)
        @test ok
        @test occursin("FROM_RECORD 0 CHECKED 1", s)
        @test occursin("REFUSED true", s)
    end
end
end
