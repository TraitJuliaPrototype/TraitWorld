# The pirate's report (traits §12.2; facts §11.1; compiler §10.2; W-155, D-12): by default a pirate whose
# definition ends code compiled by facts in the deep class is reported, naming the method, its definer and
# the code ended. A stakeholder's method, and a pirate that ends no such code, are not reported;
# `report_pirates!(false)` silences it.
using TraitWorld, Test

latest(f, args...) = Base.invokelatest(f, args...)
G(m::Symbol, n::Symbol) = Base.invokelatest(getglobal, getglobal(Main, m), n)
toplevel(q) = Core.eval(Main, Expr(:toplevel, q.args...))
deep(f, T) = (mi = Base.specialize_method(only(methods(f, T)), Tuple{typeof(f), T.parameters...}, Core.svec());
              isdefined(mi, :cache) && (mi.cache.flags & 0x30) == 0x30 && mi.cache.max_world == typemax(UInt))
function reports(ex)
    n = length(TraitWorld.PIRATE_REPORTS)
    Core.eval(Main, ex)
    return TraitWorld.PIRATE_REPORTS[n+1:end]
end

toplevel(quote
    module RepSU                              # an ordinary package's function, called from trait code
    scale(x::Real) = 1.0 * x
    end
    module RepLib                             # code compiled by facts
    using TraitWorld
    @trait_module
    import ..RepSU
    rsum(xs::Vector{Float64}) = (s = 0.0; for x in xs; s += abs2(x); end; s)
    rsum32(xs::Vector{Float32}) = (s = 0.0f0; for x in xs; s += abs2(x); end; s)
    rscale(xs::Vector{Float64}) = (s = 0.0; for x in xs; s += RepSU.scale(x); end; s)
    @trait RNamed begin
        rname(x::RNamed)::String
    end
    rtag(x) = "plain"
    rtag(x::RNamed) = "named"
    struct RC end
    rname(::RC) = "c"
    rtagof(x::RC) = rtag(x)
    end
    module RepThird                           # owns nothing the code names
    using TraitWorld
    import ..RepLib
    end
end)

@testset "the pirate's report" begin
    xs = [1.0, 2.0, 3.0]
    rsum, rscale = G(:RepLib, :rsum), G(:RepLib, :rscale)
    @test TraitWorld.REPORT_PIRATES[]
    @test latest(rsum, xs) == 14.0 && latest(rscale, xs) == 6.0
    @test deep(rsum, Tuple{Vector{Float64}})                 # the code is in the deep class

    # a pirate whose definition ends that code: reported, with the method, its definer and the code
    rs = @test_logs (:warn, r"a pirate ended code compiled by facts.*abs2.*RepPirateA.*RepLib\.rsum") match_mode = :any reports(
        :(module RepPirateA; Base.abs2(x::Float64) = 2.0 * x * x; end))
    @test length(rs) == 1
    r = rs[1]
    @test r.method isa Method && r.method.name === :abs2 && r.definer === G(:Main, :RepPirateA)
    @test any(ci -> Base.Compiler.get_ci_mi(ci).def.name === :rsum, r.code)
    @test latest(rsum, xs) == 28.0                           # followed, as plain Julia follows it

    # a stakeholder's method that ends such code: not reported
    @test latest(rscale, xs) == 6.0
    @test isempty(reports(:(@eval RepSU scale(x::Float64) = 2.0 * x)))
    @test latest(rscale, xs) == 12.0

    # a pirate that ends no such code: not reported
    @test isempty(reports(:(module RepPirateB; Base.abs2(x::Int16) = x * x + one(x); end)))

    # silenced by choice
    rsum32 = G(:RepLib, :rsum32)
    @test latest(rsum32, Float32[1, 2]) == 5.0f0
    TraitWorld.report_pirates!(false)
    try
        @test isempty(reports(:(module RepPirateC; Base.abs2(x::Float32) = 2.0f0 * x * x; end)))
        @test latest(rsum32, Float32[1, 2]) == 10.0f0
    finally
        TraitWorld.report_pirates!(true)
    end

    # a pirate's membership that ends such code: reported beside its warning at the declaration
    rtagof, RC = G(:RepLib, :rtagof), G(:RepLib, :RC)
    @test latest(rtagof, RC()) == "plain"
    rs = @test_logs (:warn, r"a pirate's membership") (:warn, r"a pirate ended code compiled by facts.*membership of") match_mode = :any reports(
        :(@eval RepThird @implement RepLib.RNamed RepLib.RC))
    @test length(rs) == 1 && rs[1].method isa TraitWorld.PirateMembership
    @test any(ci -> Base.Compiler.get_ci_mi(ci).def.name === :rtagof, rs[1].code)
    @test latest(rtagof, RC()) == "named"

    # the session's later tests see Julia's abs2 again
    for T in (Float64, Int16, Float32)
        Base.delete_method(which(abs2, (T,)))
    end
    @test latest(abs2, 2.0) == 4.0
end
