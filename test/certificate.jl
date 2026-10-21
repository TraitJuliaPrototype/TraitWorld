# The fully-typed certificate (writeup/design.md §3.4): code is fully typed when every call on a
# normal path, in it and in what it reaches, is at a fact signature; such code pays nothing for the
# facts rule. Runs inside runtests.jl, or alone.
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module Cert
    using TraitWorld
    export CTab, cn, cc, csum, cmixed, CShape, carea, ctotal
    @trait CTab begin
        cn(t::CTab)::Int
        cc(t::CTab, i::Int)::Vector{Float64}
    end
    @implement CTab Vector{Vector{Float64}} begin
        cn(t) = length(t)
        cc(t, i) = t[i]
    end
    csum(t::CTab) = (s = 0.0; for i in 1:cn(t); s += sum(cc(t, i)); end; s)            # fully typed
    cmixed(t::CTab, w::Vector{Any}) = (s = 0.0; for i in 1:cn(t); s += w[i] * sum(cc(t, i)); end; s)   # w[i] is Any
    @trait CShape{R} begin
        carea(r::R)::Float64
    end
    struct CSq; a::Float64; end
    @implement CShape{CSq} begin carea(s) = s.a^2 end
    ctotal(v::Vector{Dynamic{CShape}}) = (s = 0.0; for d in v; s += carea(d); end; s)  # declared dynamic sites
    end
    @enforce_fully_typed @trait_module module CertStrict
    using TraitWorld, ..Cert
    strictmixed(t::CTab, w::Vector{Any}) = (s = 0.0; for i in 1:cn(t); s += w[i] * sum(cc(t, i)); end; s)
    end
end)

@testset "the fully-typed certificate" begin
    t = [[1.0, 2.0], [3.0, 4.0]]
    @test Cert.csum(t) == 10.0
    r = fully_typed(Cert.csum, (Vector{Vector{Float64}},))
    @test isfullytyped(r)
    @test occursin("fully typed", sprint(show, MIME"text/plain"(), r))
    r2 = fully_typed(Cert.cmixed, (Vector{Vector{Float64}}, Vector{Any}))
    @test !isfullytyped(r2)
    msg = sprint(show, MIME"text/plain"(), r2)
    @test occursin("not fully typed", msg) && occursin("run-time site", msg) && occursin("concrete types", msg)
    v = Dynamic{Cert.CShape}[Dynamic{Cert.CShape}(Cert.CSq(2.0))]
    @test Cert.ctotal(v) == 4.0
    r3 = fully_typed(Cert.ctotal, (Vector{Dynamic{Cert.CShape}},))
    @test isfullytyped(r3) && r3.dynamic >= 1           # an operation on a Dynamic value is declared
    # concrete mode's error level refuses code that is not fully typed (or uses abstract values)
    e = try CertStrict.strictmixed(t, Any[1.0, 2.0]); nothing catch err; err end
    @test e isa NotFullyTypedError || e isa AbstractTypeError
end
