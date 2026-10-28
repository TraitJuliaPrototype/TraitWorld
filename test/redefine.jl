# A bounded function defined again after its trait module is complete goes through the module's end
# for that function (traits reference §2, W-78): the worker replaced, its callers invalidated, the
# definition checked as at the module's end. Runs inside runtests.jl.
using Test, TraitWorld

toplevel(quote
    @trait_module module RedefT
    using TraitWorld
    export RVals, RSized, rvals, rn, rsq
    @trait RVals begin
        rvals(v::RVals)::Vector{Float64}
    end
    @trait RSized begin
        rn(v::RSized)::Int
    end
    @implement RVals Vector{Float64} begin
        rvals(v) = v
    end
    @implement RSized Vector{Float64} begin
        rn(v) = length(v)
    end
    rsq(v::RVals) = (s = 0.0; for x in rvals(v); s += x; end; s)   # no `abs2`: an earlier test pirates it
    ruser(v) = rsq(v) + 1.0
    end
end)

@testset "a bounded function defined again after its trait module's end" begin
    M = Main.RedefT
    v = [1.0, 2.0]
    @test Base.invokelatest(M.rsq, v) == 3.0
    @test Base.invokelatest(M.ruser, v) == 4.0
    nm = length(methods(M.rsq))
    Core.eval(M, :(rsq(v::RVals) = 2 * sum(rvals(v))))                 # an edit of the body
    @test Base.invokelatest(M.rsq, v) == 6.0
    @test Base.invokelatest(M.ruser, v) == 7.0                          # its caller compiled again
    @test length(methods(M.rsq)) == nm                                  # the worker replaced, not added
    # an edit that breaks a rule: reported at the definition (a warning at the prompt), raised at the call
    @test_logs (:warn, r"breaks a rule of the trait world") Core.eval(M, :(rsq(v::RVals) = Float64(length(identity(v)))))
    @test_throws TraitUseError Base.invokelatest(M.rsq, v)
    Core.eval(M, :(rsq(v::RVals) = 3 * sum(rvals(v))))
    @test Base.invokelatest(M.rsq, v) == 9.0
    # a new bounded function after the end, and a shape with another bound
    Core.eval(M, :(rsz(v::RSized) = rn(v)))
    @test Base.invokelatest(M.rsz, [1.0, 2.0, 3.0]) == 3
    Core.eval(M, :(rsz(v::(RSized, RVals)) = rn(v) + length(rvals(v))))
    @test Base.invokelatest(M.rsz, [1.0, 2.0, 3.0]) == 6
    # an ordinary definition stays ordinary
    Core.eval(M, :(rplain(x::Int) = x + 1))
    @test Base.invokelatest(M.rplain, 1) == 2
    @test Core._lower === TraitWorld._tw_lower
end
