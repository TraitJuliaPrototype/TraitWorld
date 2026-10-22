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
        model::Model                  # a trait's name in a field: Kept{Model}, each value with its attribute
        hooks::Vector{Hook}           # in a container: Vector{Kept{Hook}}
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

    # made at a bound: the model and the hooks kept by storing them, each with its attribute
    function start(m::Model, u0::Vector{Float64}, hs::Hook...)
        st = State(copy(u0), 0.0, m, Hook[])
        for h in hs
            push!(st.hooks, h)
        end
        return st
    end

    whichmodel(m::Model) = "opened"
    reopen(s::State) = whichmodel(s.model)      # a kept value passed to a bound
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
    @test fieldtype(S, :model) === TraitWorld.Kept{Main.DynSolv.Model}
    @test fieldtype(S, :hooks) === Vector{TraitWorld.Kept{Main.DynSolv.Hook}}
    s = Main.DynSolv.start(Main.Decay(1.0), [1.0], Main.Below(0.95), Main.Always())
    @test s.model isa TraitWorld.Kept{Main.DynSolv.Model} && !getfield(s.model, :compiled)   # from the prompt: Dynamic
    @test length(s.hooks) == 2
    @test Main.DynSolv.step!(s, 0.1) == 2                 # u = 0.9: both hooks fire
    @test s.u ≈ [0.9]
    g = Main.DynSolv.start(Main.Growth(1.0), [1.0], Main.Always())
    @test Main.DynSolv.step!(g, 0.1) == 1 && g.u ≈ [1.1]
    # one compiled driver for both models and every hook set
    @test length(Base.specializations(only(methods(Main.DynSolv.step!)))) == 1
    @test Main.DynSolv.reopen(s) == "opened"
    @test occursin("Dynamic at Decay", sprint(show, s.model))
    typed(m::Main.Decay) = Main.DynSolv.start(m, [1.0])        # a caller that knows the type: Compiled, kept so
    @test getfield(typed(Main.Decay(1.0)).model, :compiled)
    @test getfield(Main.DynSolv.start(with_dynamic(Main.Decay(1.0)), [1.0]).model, :compiled) === false
    @test s.model == s.model && hash(s.model) == hash(s.model)
    @test s.hooks[1] != s.hooks[2]
    @test_throws TraitUseError Main.DynBad.keepany(Main.Always())
    @test_throws ArgumentError Main.DynBad.keepwrong(Main.Always())
    @test isempty(check_definitions(Main.DynSolv))
end

# A trait's name as a container's element type in a function (body and arguments) means a kept
# value, as in a field (`<:Kept{X}` in an argument); a Dynamic of a supertrait keeps only that trait's views, so a bound
# opening it runs the worker compiled for what it sees (TraitTables' columns made by TraitCSV).
toplevel(quote
    @trait_module module DynCols
    using TraitWorld
    export DCol, dlen, DGrow, dpush!, collectcols, keepall, dsum
    @trait DCol{T} begin
        T = eltype(Self)
        dlen(c::DCol)::Int
    end
    @implement DCol A where {A <: Vector} begin
        dlen(c) = length(c)
    end
    @trait DGrow{T} <: DCol begin
        T = eltype(Self)
        dpush!(c::DGrow, x::Float64)::Nothing
    end
    @implement DGrow Vector{Float64} begin
        dpush!(c, x) = (push!(c, x); nothing)
    end
    dsum(c::DCol) = dlen(c)
    asdcol(g::DGrow) = (dpush!(g, 1.0); Dynamic{DCol}(g))
    function collectcols(gs::Vector{DGrow})              # an argument container: Vector{<:Kept{DGrow}}
        out = DCol[]                                     # a body container: Kept{DCol}[]
        for g in gs
            push!(out, asdcol(g)::Dynamic{DCol})
        end
        return out
    end
    end
end)

@testset "Dynamic: containers in functions, supertrait views" begin
    D = Main.DynCols
    gs = Dynamic{D.DGrow}[Dynamic{D.DGrow}(Float64[]), Dynamic{D.DGrow}([2.0])]
    cs = D.collectcols(gs)
    @test cs isa Vector{TraitWorld.Kept{D.DCol}} && all(c -> !getfield(c, :compiled), cs)   # kept as made: Dynamic
    @test [D.dsum(c) for c in cs] == [1, 2]
    # the kept DCol has DCol's view only: the same type as one made from a plain vector
    @test typeof(TraitWorld.opened(cs[1])) === typeof(TraitWorld.opened(Dynamic{D.DCol}([1.0])))
    @test fieldcount(typeof(getfield(TraitWorld.opened(gs[1]), :views))) == 2
end

# An operation's result declared with a trait is `Dynamic`: its declared type is the trait
# (traits reference §6.2; E-156 P12, P14). The value returned is checked to conform at the
# parameters the declared trait fixes; a member's result check accepts a conforming type.
toplevel(quote
    @trait_module module DynRes
    using TraitWorld
    export Box, bval, Maker, make, readmade, readdyn, madeup, Fac, fmake, fread
    @trait Box{T} begin
        @const v::T
        bval(b::Box{T})::T
    end
    @trait Maker{T} begin
        @const seed::T
        make(m::Maker{T}, k)::Box{T}                 # a trait-typed result, at the maker's parameter
    end
    readmade(m::Maker{T}, k::Int) where {T} = (b = make(m, k); bval(compiled_for(b)) + b.v)
    readdyn(m::Maker{T}, k::Int) where {T} = bval(make(m, k))
    madeup(m::Maker{T}, k::Int) where {T} = make(m, k)  # handed to plain code: a kept value may go up
    @trait Fac{T} begin
        fmake(f::Fac{T})::Box{T}
    end
    fread(f::Fac{T}) where {T} = bval(fmake(f))
    end
    using .DynRes

    struct RBox{T}; v::T; end
    DynRes.bval(b::RBox) = b.v
    @implement Box RBox{T} where {T}
    struct RMaker{T}; seed::T; end
    DynRes.make(m::RMaker, k) = RBox(m.seed * k)
    @implement Maker RMaker{T} where {T}
    struct WrongMaker; seed::Float64; end
    DynRes.make(m::WrongMaker, k) = RBox(Float32(m.seed * k))   # a Box at another parameter: `k` untyped,
    @implement Maker WrongMaker                                   # so refused at the call
    struct RFac{T}; x::T; end
    DynRes.fmake(f::RFac) = RBox(f.x)                     # infers RBox{T}: conforms to Box{T}
    @implement Fac{T} RFac{T} where {T}
    struct BadFac{T}; x::T; end
    DynRes.fmake(f::BadFac) = f.x                         # not a Box
    @implement Fac{T} BadFac{T} where {T}
end)

@testset "an operation's result declared with a trait is Dynamic" begin
    R = Main.DynRes
    @test R.madeup(Main.RMaker(2.0), 3) isa Dynamic{R.Box{Float64}}
    typed_read(m::Main.RMaker{Float64}) = R.readmade(m, 3)
    @test typed_read(Main.RMaker(2.0)) == 12.0
    @test R.readmade(Main.RMaker(2), 3) === 12
    @test R.readdyn(Main.RMaker(2.0), 2) == 4.0
    @test R.fread(Main.RFac(1.5)) == 1.5                  # the member's result check accepts a conforming type
    e = try R.readdyn(Main.WrongMaker(1.0), 2); nothing catch err; err end
    @test e isa TraitBoundError && occursin("does not conform", sprint(showerror, e))
    e = try R.fread(Main.BadFac(1.5)); nothing catch err; err end
    @test e isa ImplementError && occursin("declared", sprint(showerror, e))
end
