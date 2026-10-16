# Dynamic values (note "Dynamic values"), shaped like the solver demonstrator's needs:
# a driver compiled once whatever the model, a model kept as a Dynamic, user hooks
# kept in a vector of dynamic values, a Dynamic opened at a bound.
# Runs inside runtests.jl, or alone: julia --project=. test/dynamic.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module DynSolv
    using TraitWorld
    export Model, rhs!, Hook, fire!, State, start, step!, reopen

    @trait Model{R} begin
        rhs!(r::R, du::Vector{Float64}, u::Vector{Float64}, t::Float64)::Nothing
    end
    @trait Hook{R} begin
        fire!(r::R, u::Vector{Float64}, t::Float64)::Bool
    end

    mutable struct State
        const u::Vector{Float64}
        t::Float64
        model::Model                  # a trait's name in a field: Dynamic{Model}
        hooks::Vector{Hook}           # in a container: Vector{Dynamic{Hook}}
    end

    # the driver: compiled once for State, whatever the model and the hooks
    function step!(s::State, dt::Float64)
        du = similar(s.u)
        rhs!(s.model, du, s.u, s.t)
        s.u .+= dt .* du
        s.t += dt
        n = 0
        for h in s.hooks
            fire!(h, s.u, s.t) && (n += 1)
        end
        return n
    end

    # made at a bound: the model projected, then kept; the hooks kept by storing them
    function start(m::Model, u0::Vector{Float64}, hs::Hook...)
        st = State(copy(u0), 0.0, Dynamic{Model}(m), Dynamic{Hook}[])
        for h in hs
            push!(st.hooks, h)
        end
        return st
    end

    whichmodel(m::Model) = "opened"
    reopen(s::State) = whichmodel(s.model)      # a Dynamic passed to a bound is opened
    end
    using .DynSolv

    @trait_module module DynBad
    using TraitWorld, ..DynSolv
    export keepany, keepwrong
    keepany(h::Hook) = (v = Any[]; push!(v, h); length(v))   # a trait object stored without a Dynamic
    keepwrong(h::Hook) = Dynamic{Model}(h)                    # kept as a Dynamic of another trait
    end
    using .DynBad
end)

toplevel(quote
    struct Decay; k::Float64; end
    DynSolv.rhs!(m::Decay, du, u, t) = (du .= -m.k .* u; nothing)
    @implement Model Decay
    struct Growth; k::Float64; end
    DynSolv.rhs!(m::Growth, du, u, t) = (du .= m.k .* u; nothing)
    @implement Model Growth
    struct Below; level::Float64; end
    DynSolv.fire!(h::Below, u, t) = u[1] < h.level
    @implement Hook Below
    struct Always; end
    DynSolv.fire!(::Always, u, t) = true
    @implement Hook Always
end)

@testset "Dynamic values" begin
    S = Main.DynSolv.State
    @test fieldtype(S, :model) === Dynamic{Main.DynSolv.Model}
    @test fieldtype(S, :hooks) === Vector{Dynamic{Main.DynSolv.Hook}}
    s = Main.DynSolv.start(Main.Decay(1.0), [1.0], Main.Below(0.95), Main.Always())
    @test s.model isa Dynamic{Main.DynSolv.Model}
    @test length(s.hooks) == 2
    @test Main.DynSolv.step!(s, 0.1) == 2                 # u = 0.9: both hooks fire
    @test s.u ≈ [0.9]
    g = Main.DynSolv.start(Main.Growth(1.0), [1.0], Main.Always())
    @test Main.DynSolv.step!(g, 0.1) == 1 && g.u ≈ [1.1]
    # one compiled driver for both models and every hook set
    @test length(Base.specializations(only(methods(Main.DynSolv.step!)))) == 1
    @test Main.DynSolv.reopen(s) == "opened"
    @test occursin("Dynamic{", sprint(show, s.model)) && occursin("Decay", sprint(show, s.model))
    @test s.model == s.model && hash(s.model) == hash(s.model)
    @test s.hooks[1] != s.hooks[2]
    @test_throws TraitUseError Main.DynBad.keepany(Main.Always())
    @test_throws ArgumentError Main.DynBad.keepwrong(Main.Always())
    @test isempty(check_definitions(Main.DynSolv))
end
