# The diagnostics for slowdowns (W-85): `callpath`, `factscode`, `loadreport`.
# Runs inside runtests.jl, or alone.
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module DiagT
    using TraitWorld
    export Rate, HasLimit, rate, limit, step1, step2, steps, Ra, Rb
    @trait Rate begin
        rate(r::Rate)::Float64
    end
    @trait HasLimit begin
        limit(r::HasLimit)::Float64
    end
    struct Ra; r::Float64; end
    struct Rb; r::Float64; l::Float64; end
    @implement Rate Ra begin rate(x) = x.r end
    @implement Rate Rb begin rate(x) = x.r end
    @implement HasLimit Rb begin limit(x) = x.l end
    step1(x::Rate) = 2 * rate(x)
    step2(x::Rate) = rate(x)
    step2(x::(Rate, HasLimit)) = min(rate(x), limit(x))
    function steps(xs::Vector{Dynamic{Rate}})
        s = 0.0
        for x in xs
            s += rate(x)
        end
        return s
    end
    end
end)

@testset "diagnostics: callpath" begin
    D = Main.DiagT
    c = TraitWorld.callpath(D.step1, D.Ra(1.5))
    @test length(c.positions) == 1
    p = c.positions[1]
    @test startswith(p.form, "plain")
    @test occursin("Compiled at its key", p.typed)
    @test occursin("Dynamic", p.untyped)
    @test !p.decided_at_run_time
    @test c.worker isa Method && c.worker.name === :step1
    @test isfinite(c.typed_ns) && isfinite(c.untyped_ns)
    @test isempty(filter(s -> isempty(s.note), c.caller_sites))      # a typed call: nothing left to run time
    s = sprint(show, MIME"text/plain"(), c)
    @test occursin("argument 1: plain", s) && occursin("per call", s)
    # a Dynamic value, two bounds: the trait object, and so the worker, is decided when the call runs
    d = TraitWorld.callpath(D.step2, Dynamic{D.Rate}(D.Rb(1.0, 0.5)); time = false)
    q = d.positions[1]
    @test q.decided_at_run_time
    @test occursin("erased key", q.typed)
    @test any(x -> occursin("HasLimit", x) && occursin("declared", x), q.impls)
    @test any(s -> isempty(s.note) && s.kind === :dispatch, d.caller_sites)
    @test d.worker isa Method && occursin("HasLimit", TraitWorld._worker_text(d.worker))
    e = TraitWorld.callpath(D.step2, Dynamic{D.Rate}(D.Ra(1.0)); time = false)
    @test any(x -> occursin("HasLimit", x) && occursin("none", x), e.positions[1].impls)
    # a compiled_for value from an untyped caller: the table of declared implementations
    f = TraitWorld.callpath(D.step1, compiled_for(D.Ra(1.0)); time = false)
    @test occursin("table of declared implementations", f.positions[1].untyped)
    # a plain function: no bounded position
    g = TraitWorld.callpath(+, 1, 2; time = false)
    @test isempty(g.positions)
end

@testset "diagnostics: factscode" begin
    D = Main.DiagT
    fc = TraitWorld.factscode(D.steps, (Vector{Dynamic{D.Rate}},))
    @test !isempty(fc.bodies)
    @test fc.bodies[1].owner === :facts
    @test any(s -> s.kind in (:split_table, :dispatch, :pointer), fc.sites)        # an operation on a Dynamic value
    s = sprint(show, MIME"text/plain"(), TraitWorld.factscode(D.steps, (Vector{Dynamic{D.Rate}},); ir = true))
    @test occursin("run-time site", s) && occursin("▶", s)
    w = TraitWorld.factscode(TraitWorld.callpath(D.step1, D.Ra(1.0); time = false))
    @test isempty(filter(s -> isempty(s.note), w.sites))                           # the worker at its key: all static
    @test isempty(TraitWorld.factscode(+, (Int, Int)).sites)
end

@testset "diagnostics: loadreport" begin
    TraitWorld.loadreport_switch!(true)
    try
        toplevel(quote
            @trait_module module DiagL
            using TraitWorld
            @trait Level begin
                lvl(x::Level)::Int
            end
            struct L1; v::Int; end
            @implement Level L1 begin lvl(x) = x.v end
            twice(x::Level) = 2 * lvl(x)
            end
        end)
        @test toplevel(:(Main.DiagL.twice(Main.DiagL.L1(3)))) == 6
    finally
        TraitWorld.loadreport_switch!(false; reset = false)
    end
    s = sprint(TraitWorld.loadreport)
    @test occursin("TraitWorld load report", s)
    @test occursin("definition checks", s) || occursin("first-call checks", s)
    @test any(k -> k[1] === :definition_hook, keys(TraitWorld._LR_PARTS))
    TraitWorld.loadreport_switch!(false)                                           # dropped, off
    @test isempty(TraitWorld._LR_PARTS)
end
