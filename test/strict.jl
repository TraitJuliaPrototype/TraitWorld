# Strict mode (writeup/explorations/strict-mode.md): defining a winning pirate is an error.
# Needs the patched runtime's definition hooks; skipped on stock Julia.
# Runs inside runtests.jl, or alone: julia --project=. test/strict.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))
latest(f, args...) = Base.invokelatest(f, args...)
G(name::Symbol) = Base.invokelatest(getglobal, Main, name)        # a binding defined after the testset began
function thrown_strict(ex)
    try
        toplevel(ex); return nothing
    catch e
        while e isa LoadError; e = e.error; end
        return e
    end
end

if !TraitWorld._HAS_DEF_HOOK[]
    @info "strict mode: no definition hooks in this runtime (stock Julia); skipped"
else
toplevel(quote
    module SU                                 # an ordinary package's functions, called from trait code
    scale(x::Real) = 1.0 * x
    function lookup end                       # no method for Float64 yet
    end
    @trait_module module StrictLib
    using TraitWorld
    import ..SU
    export SBuf, sq, scaled, looked
    @trait SBuf{R} begin
        svals(r::R)::Vector{Float64}
    end
    @implement SBuf{Vector{Float64}} begin
        svals(r) = r
    end
    sq(b::SBuf) = (s = 0.0; for x in svals(b); s += abs2(x); end; s)
    scaled(b::SBuf) = (s = 0.0; for x in svals(b); s += SU.scale(x); end; s)
    looked(b::SBuf) = (s = 0.0; for x in svals(b); s += SU.lookup(x)::Float64; end; s)
    end
    using .StrictLib
end)

@testset "strict mode: defining a winning pirate is an error" begin
    v = [1.0, 2.0, 3.0]
    TraitWorld.strict!(true)
    try
        @test latest(sq, v) == 14.0
        @test latest(scaled, v) == 6.0
        @test_throws MethodError latest(looked, v)

        # a pirate that wins at a fact of trait-world code (Base owns abs2 and Float64): refused
        e = thrown_strict(:(module PirateA; Base.abs2(x::Float64) = 2.0 * x * x; end))
        @test e isa TraitWorld.PirateError
        @test !e.later                                    # found before the definition
        @test latest(sq, v) == 14.0                               # the method never existed
        @test latest(abs2, 2.0) == 4.0                            # for plain Julia either

        # a pirate that fills a gap trait-world code ran into (SU owns lookup): refused
        e = thrown_strict(:(module PirateB; Main.SU.lookup(x::Float64) = x; end))
        @test e isa TraitWorld.PirateError
        @test_throws MethodError latest(looked, v)

        # pirates that win nowhere in trait-world code are accepted
        @test thrown_strict(:(module PirateC; Base.abs2(x::Int8) = Int8(7); end)) === nothing
        @test latest(abs2, Int8(2)) == 7
        @test thrown_strict(:(module PirateD; Base.abs2(x::AbstractString) = length(x); end)) === nothing
        @test latest(sq, v) == 14.0

        # the session defining a method of SU's function for Float64 at the prompt: a pirate by the letter
        @test thrown_strict(:(SU.scale(x::Float64) = 3.0 * x)) isa TraitWorld.PirateError
        # a stakeholder's definition is followed, as plain Julia follows it (SU owns scale; Revise and
        # `@eval SU` attribute the definition to SU)
        @test thrown_strict(:(@eval SU scale(x::Float64) = 2.0 * x)) === nothing
        @test latest(scaled, v) == 12.0
        # and the owner of the function may fill the gap
        @test thrown_strict(:(@eval SU lookup(x::Float64) = 10.0 * x)) === nothing
        @test latest(looked, v) == 60.0

        # a pirate defined before the trait code is compiled is followed (plain Julia)
        toplevel(:(module PirateE; Base.abs2(x::Float32) = 3.0f0 * x * x; end))
        @test latest(abs2, 1.0f0) == 3.0f0
        toplevel(quote
            @trait_module module StrictLib2
            using TraitWorld
            export S32, sq32
            @trait S32{R} begin
                v32(r::R)::Vector{Float32}
            end
            @implement S32{Vector{Float32}} begin
                v32(r) = r
            end
            sq32(b::S32) = (s = 0.0f0; for x in v32(b); s += abs2(x); end; s)
            end
            using .StrictLib2
        end)
        @test latest(G(:sq32), Float32[1, 2]) == 15.0f0
        # and can never change it afterwards: its next winning definition is refused
        e = thrown_strict(:(@eval PirateE Base.abs2(x::Float32) = 4.0f0 * x * x))
        @test e isa TraitWorld.PirateError
        @test latest(G(:sq32), Float32[1, 2]) == 15.0f0

        # a delegate counts as a stakeholder of what it implements
        toplevel(:(module CoreT; struct T; x::Float64; end; end))
        toplevel(quote
            @trait_module module StrictLib3
            using TraitWorld
            import ..CoreT
            export TB, tot
            @trait TB{R} begin
                ts(r::R)::Vector{CoreT.T}
            end
            @implement TB{Vector{CoreT.T}} begin
                ts(r) = r
            end
            tot(b::TB) = (s = 0.0; for t in ts(b); s += Float64(t); end; s)
            end
            using .StrictLib3
        end)
        toplevel(:(module ImplT; Base.Float64(t::Main.CoreT.T) = t.x; end))     # a pirate by the letter: CoreT owns T
        @test latest(G(:tot), [latest(G(:CoreT).T, 1.0), latest(G(:CoreT).T, 2.0)]) == 3.0
        e = thrown_strict(:(@eval ImplT Base.Float64(t::Main.CoreT.T) = 2 * t.x))
        @test e isa TraitWorld.PirateError
        TraitWorld.delegate!(G(:CoreT) => G(:ImplT))
        @test thrown_strict(:(@eval ImplT Base.Float64(t::Main.CoreT.T) = 2 * t.x)) === nothing
        @test latest(G(:tot), [latest(G(:CoreT).T, 1.0), latest(G(:CoreT).T, 2.0)]) == 6.0

        @test isempty(TraitWorld._STRICT_MISSES)          # the check before the definition missed nothing
    finally
        TraitWorld.strict!(false)
    end
    # strict mode off: a winning pirate is followed, as in plain Julia
    @test thrown_strict(:(module PirateF; Base.abs2(x::Float64) = 2.0 * x * x; end)) === nothing
    @test latest(sq, [1.0, 2.0, 3.0]) == 28.0
end
end
