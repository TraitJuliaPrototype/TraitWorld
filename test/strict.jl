# Strict mode (traits §12.3; lowering §13; W-114): a pirate that would win at a call code compiled by
# facts makes is refused with PirateError and does not exist; a stakeholder's definition is followed;
# a pirate that wins nowhere in code compiled by facts is accepted. The cases of the earlier library's
# strict-mode tests (TraitWorld test/strict.jl), on traits as abstract types.
using TraitWorld, Test

function thrown(ex)
    try
        Core.eval(Main, ex)
        return nothing
    catch e
        while e isa LoadError; e = e.error; end
        return e
    end
end
latest(f, args...) = Base.invokelatest(f, args...)
G(m::Symbol, n::Symbol) = Base.invokelatest(getglobal, getglobal(Main, m), n)

toplevel(q) = Core.eval(Main, Expr(:toplevel, q.args...))
toplevel(quote
    module SU                                 # an ordinary package's functions, called from trait code
    scale(x::Real) = 1.0 * x
    function lookup end                       # no method for Float64 yet
    g(x::Integer) = 1
    end
    module CoreT
    using TraitWorld
    @joint_owners ImplT
    struct T; x::Float64; end
    end
    module AbsA
    abstract type AT end
    Base.length(::AT) = 1
    end
    module AbsB
    struct BT <: Main.AbsA.AT end
    end
    module StrictLib
    using TraitWorld
    @trait_module
    import ..SU, ..CoreT, ..AbsB
    @trait SBuf begin
        svals(r::SBuf)::Vector{Float64}
    end
    struct Buf; v::Vector{Float64}; end
    svals(b::Buf) = b.v
    @implement SBuf Buf
    sq(b::SBuf) = (s = 0.0; for x in svals(b); s += abs2(x); end; s)
    scaled(b::SBuf) = (s = 0.0; for x in svals(b); s += SU.scale(x); end; s)
    looked(b::SBuf) = (s = 0.0; for x in svals(b); s += SU.lookup(x)::Float64; end; s)
    tot(ts::Vector{CoreT.T}) = (s = 0.0; for t in ts; s += Float64(t); end; s)
    cnt(bs::Vector{AbsB.BT}) = (s = 0; for b in bs; s += length(b); end; s)
    vsum(xs::Vector{Int}) = (s = 0; for x in xs; s += SU.g(x); end; s)
    end
    module ImplT
    Base.Float64(t::Main.CoreT.T) = t.x       # a joint owner's method: CoreT names ImplT
    end
end)

@testset "strict mode" begin
    b = G(:StrictLib, :Buf)([1.0, 2.0, 3.0])
    sq, scaled, looked = G(:StrictLib, :sq), G(:StrictLib, :scaled), G(:StrictLib, :looked)
    TraitWorld.strict!(true)
    try
        @test latest(sq, b) == 14.0
        @test latest(scaled, b) == 6.0
        @test_throws MethodError latest(looked, b)

        # a pirate that wins at a fact of code compiled by facts (Julia owns abs2 and Float64): refused
        e = thrown(:(module PirateA; Base.abs2(x::Float64) = 2.0 * x * x; end))
        @test e isa PirateError && !e.later
        @test latest(sq, b) == 14.0                              # the method never existed
        @test latest(abs2, 2.0) == 4.0                           # for plain code either

        # a pirate that fills a gap the code ran into (SU owns lookup): refused
        @test thrown(:(module PirateB; Main.SU.lookup(x::Float64) = x; end)) isa PirateError
        @test_throws MethodError latest(looked, b)

        # pirates that win nowhere in code compiled by facts: accepted
        @test thrown(:(module PirateC; Base.abs2(x::Int8) = Int8(7); end)) === nothing
        @test latest(abs2, Int8(2)) == 7
        @test latest(sq, b) == 14.0

        # deleting a pirate that code compiled by facts now dispatches to is refused (compiler §10.2)
        Core.eval(Main, :(module StrictLib6; using TraitWorld; @trait_module
                          sq8(xs::Vector{Int8}) = (s = 0; for x in xs; s += abs2(x); end; s); end))
        @test latest(G(:StrictLib6, :sq8), Int8[2]) == 7
        @test_throws PirateError Base.delete_method(which(abs2, (Int8,)))
        @test latest(abs2, Int8(2)) == 7

        # the session (Main) defining SU's function for Float64 is a pirate by the letter: refused;
        # SU's own definition is a stakeholder's: followed
        @test thrown(:(SU.scale(x::Float64) = 3.0 * x)) isa PirateError
        @test thrown(:(@eval SU scale(x::Float64) = 2.0 * x)) === nothing
        @test latest(scaled, b) == 12.0
        @test thrown(:(@eval SU lookup(x::Float64) = 10.0 * x)) === nothing
        @test latest(looked, b) == 60.0

        # a joint owner is a stakeholder: CoreT names ImplT
        ts = [latest(G(:CoreT, :T), 1.0), latest(G(:CoreT, :T), 2.0)]
        @test latest(G(:StrictLib, :tot), ts) == 3.0
        @test thrown(:(@eval ImplT Base.Float64(t::Main.CoreT.T) = 2 * t.x)) === nothing
        @test latest(G(:StrictLib, :tot), ts) == 6.0
        @test thrown(:(module NotJoint; Base.Float64(t::Main.CoreT.T) = 3 * t.x; end)) isa PirateError

        # a method on its own abstract type is no pirate, also where it wins at another package's subtype
        bs = [latest(G(:AbsB, :BT)), latest(G(:AbsB, :BT))]
        @test latest(G(:StrictLib, :cnt), bs) == 2
        @test thrown(:(@eval AbsA Base.length(::AT) = 5)) === nothing
        @test latest(G(:StrictLib, :cnt), bs) == 10

        # stakeholders per arity: `g(::Int, ::MyT...)` by MyT's owner names nothing of its at `g(::Int)`
        @test latest(G(:StrictLib, :vsum), [1, 2]) == 2
        @test thrown(:(module VP; struct MyT end; Main.SU.g(x::Int, y::MyT...) = 2; end)) isa PirateError
        @test latest(G(:StrictLib, :vsum), [1, 2]) == 2

        @test isempty(TraitWorld._STRICT_MISSES)             # the walk before the definition missed nothing
    finally
        TraitWorld.strict!(false)
    end
    # strict mode off: a winning pirate is followed, as in plain Julia
    @test thrown(:(module PirateF; Base.abs2(x::Float64) = 2.0 * x * x; end)) === nothing
    @test latest(sq, b) == 28.0
    # the session's later tests see Julia's abs2 again
    Base.delete_method(which(abs2, (Float64,)))
    Base.delete_method(which(abs2, (Int8,)))
    @test latest(abs2, 2.0) == 4.0
end
