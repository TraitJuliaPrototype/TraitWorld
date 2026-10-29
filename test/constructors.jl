# Open issue 131: a bounded method on a type's constructor (`NWState(int::(IntegratorView, HasSystem))`) is a
# bounded function like any other. Its entry is keyed by `Core.Typeof(f)`, `Type{S}` (lowering §8): the type's
# ordinary constructors are its fallback, with and without keywords; typed and untyped callers, a `Dynamic`
# value, trait code; two constructors' entries kept apart; compiled ahead in a package image.
# Runs inside runtests.jl, or alone: julia --project=. test/constructors.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))
isdefined(Main, :thrown) || (thrown(ex) = try toplevel(ex); nothing catch e; while e isa LoadError; e = e.error; end; e end)

toplevel(quote
    @trait_module module CtorMod
    using TraitWorld
    export CSized, cwidth, CNamed, cname, CBox, CPBox, COnly, cwrap
    @trait CSized begin
        cwidth(s::Self)::Int
    end
    @trait CNamed begin
        cname(s::Self)::String
    end
    # a struct without parameters (`typeof(CBox)` is `DataType`): its default constructors take two arguments
    struct CBox; w::Int; scale::Int; end
    CBox(s::CSized) = CBox(cwidth(s), 1)
    CBox(x; scale = 2) = CBox(length(x), scale)                      # the untyped fallback, with keywords
    # a parametric struct (`typeof(CPBox)` is `UnionAll`), with the constructor with explicit parameters only
    struct CPBox{T}
        w::T
        CPBox{T}(w::T) where {T} = new{T}(w)
    end
    CPBox(s::CSized) = CPBox{Float64}(float(cwidth(s)))
    CPBox(s::CSized, k::Int; add = 0) = CPBox{Int}(cwidth(s) * k + add)
    CPBox(w) = CPBox{typeof(w)}(w)                                    # the untyped fallbacks
    CPBox(x, k::Int; add = 0) = CPBox{Int}(length(x) * k + add)
    # another constructor with an entry of the same shape, at another trait
    struct COnly
        name::String
        COnly(name::String) = new(name)                                # typed: Julia defines no untyped `COnly(name)`
    end
    @warn_not_fully_typed COnly(n::CNamed) = COnly(cname(n))
    # trait code calls a bounded constructor
    cwrap(s::CSized) = CBox(s)
    end
end)
toplevel(quote
    struct CSurf; w::Int; end
    @implement CtorMod.CSized CSurf begin
        cwidth(s) = s.w
    end
    struct CPerson; n::String; end
    @implement CtorMod.CNamed CPerson begin
        cname(p) = p.n
    end
    ctor_typed(s::CSurf) = CtorMod.CBox(s)
    ctor_typed_p(s::CSurf) = CtorMod.CPBox(s)
end)

@testset "open issue 131: a bounded constructor" begin
    M = Main.CtorMod
    s = Main.CSurf(3)
    @testset "a struct without parameters" begin
        @test M.CBox(s) == M.CBox(3, 1)
        @test M.CBox(Dynamic{M.CSized}(s)) == M.CBox(3, 1)
        @test M.CBox([1, 2]) == M.CBox(2, 2)                            # the fallback
        @test M.CBox([1, 2]; scale = 5) == M.CBox(2, 5)                 # the fallback with keywords
        @test M.CBox(4, 5) == M.CBox(4, 5)                              # Julia's default constructor
        # a call with keywords is sorted among the methods that take keywords, as in Julia (open issue 130)
        @test_throws MethodError M.CBox(s; scale = 5)
        @test Base.invokelatest(Main.ctor_typed, s) == M.CBox(3, 1)
        @test Base.return_types(Main.ctor_typed, (Main.CSurf,)) == Any[M.CBox]
        @test Base.inferencebarrier(M.CBox)(Base.inferencebarrier(s)) == M.CBox(3, 1)
        @test M.cwrap(s) == M.CBox(3, 1)
        @test isfullytyped(TraitWorld.fully_typed(M.CBox, (Main.CSurf,)))
    end
    @testset "a parametric struct" begin
        @test M.CPBox(s) isa M.CPBox{Float64} && M.CPBox(s).w == 3.0
        @test M.CPBox(Dynamic{M.CSized}(s)).w == 3.0
        @test M.CPBox(2) isa M.CPBox{Int} && M.CPBox(2).w == 2         # the fallback
        @test M.CPBox(s, 2).w == 6
        @test M.CPBox(s, 2; add = 1).w == 7
        @test M.CPBox(Dynamic{M.CSized}(s), 2; add = 1).w == 7
        @test M.CPBox([1, 2], 2; add = 1).w == 5                         # the fallback with keywords
        @test Base.return_types(Main.ctor_typed_p, (Main.CSurf,)) == Any[M.CPBox{Float64}]
        @test Base.inferencebarrier(M.CPBox)(Base.inferencebarrier(s)).w == 3.0
    end
    @testset "each constructor its own entry" begin
        @test TraitWorld.needed(TraitWorld.EntryPos{Type{M.CBox},1,1}()) === TraitWorld.TraitList{Tuple{M.CSized}}()
        @test TraitWorld.needed(TraitWorld.EntryPos{Type{M.COnly},1,1}()) === TraitWorld.TraitList{Tuple{M.CNamed}}()
        @test TraitWorld.needed(TraitWorld.EntryPos{Type{M.CPBox},1,1}()) === TraitWorld.TraitList{Tuple{M.CSized}}()
        # fully typed mode on a constructor: checked at the first call, no warning
        @test (@test_logs min_level = Base.CoreLogging.Warn M.COnly(Main.CPerson("ann"))) == M.COnly("ann")
        @test M.COnly("bob") == M.COnly("bob")                          # Julia's default constructor
        e = try M.COnly(2) catch err; err end
        @test e isa MethodError && occursin("CNamed", sprint(showerror, e))
    end
    @testset "an untyped constructor the entry would replace is refused" begin
        e = thrown(quote
            @trait_module module CtorBad
            using TraitWorld
            @trait CBSized begin
                cbw(s::Self)::Int
            end
            struct CBad{T}; w::T; end                                    # Julia's default constructor `CBad(w::T) where {T}`
            CBad(s::CBSized) = CBad(cbw(s))
            end
        end)
        @test e isa ErrorException && occursin("the constructor of `CBad` already has an untyped method", e.msg)
        e = thrown(quote
            @trait_module module CtorBad2
            using TraitWorld
            @trait CBSized2 begin
                cbw2(s::Self)::Int
            end
            struct CBad2; w::Int; end                                    # Julia's default constructor `CBad2(w)` converts
            CBad2(s::CBSized2) = CBad2(cbw2(s))
            end
        end)
        @test e isa ErrorException && occursin("the constructor of `CBad2` already has an untyped method", e.msg)
    end
end

# compiled ahead in a package image: the worker of the bounded constructor at the implementing type's key
mktempdir() do dir
    pkgs = joinpath(dir, "pkgs"); depot = joinpath(dir, "depot")
    mkpath(joinpath(pkgs, "CtorImg", "src"))
    write(joinpath(pkgs, "CtorImg", "src", "CtorImg.jl"), """
        module CtorImg
        using TraitWorld
        @trait_module module Inner
        using TraitWorld
        export Sized, width, Box, PBox, Surf
        @trait Sized begin
            width(s::Self)::Int
        end
        struct Box
            w::Int
            Box(w::Int) = new(w)
        end
        Box(s::Sized) = Box(width(s))
        struct PBox{T}
            w::T
            PBox{T}(w::T) where {T} = new{T}(w)
        end
        PBox(s::Sized) = PBox{Int}(width(s))
        PBox(w) = PBox{typeof(w)}(w)
        struct Surf; w::Int; end
        @implement Sized Surf begin
            width(s) = s.w
        end
        end
        end
        """)
    tw = dirname(Base.active_project())
    env = copy(ENV)
    env["JULIA_LOAD_PATH"] = join([pkgs, tw, "@stdlib"], Sys.iswindows() ? ";" : ":")
    env["JULIA_DEPOT_PATH"] = join([depot, Base.DEPOT_PATH...], Sys.iswindows() ? ";" : ":")
    env["JULIA_PKG_OFFLINE"] = "true"
    delete!(env, "JULIA_PROJECT")
    code = """
        using CtorImg, TraitWorld
        const I = CtorImg.Inner
        # the workers' instances with machine code, valid now, before any call
        native(f) = sum(m -> TraitWorld._isworker(m) ? count(mi -> begin
                ci = isdefined(mi, :cache) ? mi.cache : nothing
                n = 0
                while ci isa Core.CodeInstance
                    (ci.owner === nothing || ci.owner === :facts) && ci.max_world == typemax(UInt) && ci.invoke != C_NULL && (n += 1)
                    ci = isdefined(ci, :next) ? ci.next : nothing
                end
                n > 0
            end, Base.specializations(m)) : 0, methods(f))
        println("NATIVE ", native(I.Box), " ", native(I.PBox))
        println("CALL ", I.Box(I.Surf(4)).w, " ", I.PBox(I.Surf(5)).w, " ", I.PBox(1.5).w)
        """
    cmd = `$(Base.julia_cmd()) --startup-file=no --compiled-modules=yes -e $code`
    out = IOBuffer(); err = IOBuffer()
    ok = success(pipeline(setenv(cmd, env); stdout = out, stderr = err))
    s = String(take!(out)); e = String(take!(err))
    ok || @info "session failed" s e
    @testset "open issue 131: a bounded constructor compiled ahead in a package image" begin
        @test ok
        @test occursin(r"NATIVE [1-9]\d* [1-9]", s)
        @test occursin("CALL 4 5 1.5", s)
    end
end
