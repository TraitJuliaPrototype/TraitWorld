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
end

# Lowering L-50: an ordinary constructor at the entry's signature (Julia's default ones, an untyped inner one) is
# taken out of the method table when the entry is defined, and becomes the entry's fallback, called by its method
toplevel(quote
    @trait_module module CtorCap
    using TraitWorld
    @trait KSized begin
        kw(s::Self)::Int
    end
    struct KA; w::Int; end                               # Julia's default constructor `KA(w)` converts to `Int`
    KA(s::KSized) = KA(kw(s))
    struct KB{T}; w::T; end                              # Julia's default constructor `KB(w::T) where {T}`
    KB(s::KSized) = KB{Int}(kw(s) * 10)
    kb_fallback(s::KSized) = KB(kw(s) * 10)              # trait code reaches the fallback with an `Int`
    struct KC
        w::Int
        KC(x; k = 1) = new(length(x) * k)                # an untyped inner constructor with keywords
    end
    KC(s::KSized) = KC(fill(0, kw(s)); k = 2)
    struct KD
        w::Int
        KD(x, y::Int) = new(x + y)                       # an inner constructor at the entry's signature, one argument typed
    end
    KD(s::KSized, y::Int) = KD(kw(s), y)
    struct KE; w::Int; end
    KE(s::KSized; add = 0) = KE(kw(s) + add)             # a bounded method with keywords; `KE(w)` its fallback
    kwrap(s::KSized) = KA(s)                             # trait code calls the bounded constructor
    end
end)
toplevel(quote
    struct KSurf; w::Int; end
    @implement CtorCap.KSized KSurf begin
        kw(s) = s.w
    end
    kctor_typed(s::KSurf) = CtorCap.KA(s)
    kctor_typed_b(s::KSurf) = CtorCap.KB(s)
end)

@testset "lowering L-50: the constructor at the entry's signature is its fallback" begin
    M = Main.CtorCap
    s = Main.KSurf(3)
    @testset "Julia's default constructor, a struct without parameters" begin
        @test M.KA(s) == M.KA(3)
        @test M.KA(2.0) == M.KA(2)                                     # the fallback converts, as Julia's constructor does
        @test M.KA(Int8(4)).w === 4
        @test_throws InexactError M.KA(2.5)
        @test M.KA(Dynamic{M.KSized}(s)) == M.KA(3)
        @test Base.inferencebarrier(M.KA)(Base.inferencebarrier(2.0)) == M.KA(2)
        @test Base.invokelatest(Main.kctor_typed, s) == M.KA(3)
        @test Base.return_types(Main.kctor_typed, (Main.KSurf,)) == Any[M.KA]
        @test M.kwrap(s) == M.KA(3)
        @test count(TraitWorld._is_entry, methods(M.KA)) == 1
        @test count(m -> TraitWorld._is_tagged(m), methods(M.KA)) == 1
    end
    @testset "Julia's default constructor, a parametric struct" begin
        @test M.KB(s) isa M.KB{Int} && M.KB(s).w == 30
        @test M.KB(1.5) isa M.KB{Float64} && M.KB(1.5).w == 1.5
        @test M.KB{Float64}(2) isa M.KB{Float64}
        @test M.kb_fallback(s) isa M.KB{Int} && M.kb_fallback(s).w == 30
        @test Base.return_types(Main.kctor_typed_b, (Main.KSurf,)) == Any[M.KB{Int}]
    end
    @testset "an untyped inner constructor, with keywords (open issue 130)" begin
        @test M.KC(s).w == 6
        @test M.KC([1, 2]).w == 2
        @test M.KC([1, 2]; k = 3).w == 6                              # its keyword sorter, the keyword fallback
        @test_throws MethodError M.KC(s; k = 3)                        # sorted among the methods that take keywords
    end
    @testset "an inner constructor with a typed argument" begin
        @test M.KD(s, 1).w == 4
        @test M.KD(1.0, 2).w == 3
    end
    @testset "a bounded method with keywords" begin
        @test M.KE(s).w == 3
        @test M.KE(s; add = 2).w == 5
        @test M.KE(2.0).w == 2
        @test_throws MethodError M.KE(2.0; add = 1)
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
    # lowering L-50: Julia refuses to take a method out of the method table while it writes a package image, so a
    # bounded constructor at the signature of Julia's default one is refused there (in a session it is its fallback)
    mkpath(joinpath(pkgs, "CtorImg2", "src"))
    write(joinpath(pkgs, "CtorImg2", "src", "CtorImg2.jl"), """
        module CtorImg2
        using TraitWorld
        @trait_module module Inner
        using TraitWorld
        @trait Sized2 begin
            width2(s::Self)::Int
        end
        struct Box2; w::Int; end
        Box2(s::Sized2) = Box2(width2(s))
        end
        end
        """)
    out = IOBuffer(); err = IOBuffer()
    cmd2 = `$(Base.julia_cmd()) --startup-file=no --compiled-modules=yes -e "using CtorImg2"`
    ok2 = success(pipeline(setenv(cmd2, env); stdout = out, stderr = err))
    e2 = String(take!(err))
    @testset "lowering L-50: refused while Julia writes a package image" begin
        @test !ok2
        @test occursin("lowering L-50", e2)
    end
end
