# The attribute (traits §4.6, §7.4–§7.8, §13; W-111): the trait's default, the casts, `keep`,
# `Dynamic{X}` as Julia's `Core.Dynamic`, and trait modules. `keep` shows which instance ran: the
# argument where it is compiled for the value's type, a `Dynamic{X}` of it where compiled once.
using TraitWorld, Test

module Models                                # the trait's package
using TraitWorld
@trait Model begin
    @default_dynamic
    rhs(m::Model, u::Float64)::Float64
end
kind(m::Model) = keep(m) isa Dynamic ? :dynamic : :compiled
solve(m::Model, u0::Float64) = rhs(m, u0) + u0
end
using .Models: Model, rhs, solve

module UserModels                            # a user's members
using TraitWorld
import ..Model, ..rhs
struct Decay; k::Float64; end
rhs(d::Decay, u::Float64) = -d.k * u
@implement Model Decay
struct Growth; k::Float64; end
rhs(g::Growth, u::Float64) = g.k * u
@implement Model Growth
end
using .UserModels: Decay, Growth

@testset "the trait's default" begin
    @test Models.kind(Decay(1.0)) === :dynamic         # a user's member: compiled once
    @test Models.kind(Growth(1.0)) === :dynamic
    @test solve(Decay(0.5), 2.0) == 1.0 && solve(Growth(0.5), 2.0) == 3.0
end

@testset "casts" begin
    @test Models.kind(compiled_for(Decay(1.0))) === :compiled
    @test Models.kind(with_dynamic(Decay(1.0))) === :dynamic
    d = Dynamic{Model}(Growth(2.0))
    @test Models.kind(compiled_for(d)) === :compiled      # the cast passes the held object
    @test Models.kind(d) === :dynamic
    @test solve(compiled_for(Decay(0.5)), 2.0) == solve(with_dynamic(Decay(0.5)), 2.0) == 1.0
end

@testset "keep" begin
    struct Prob{M <: Model}; m::M; end
    store(m::Model) = (k = keep(m); Prob{typeof(k)}(k))
    p = store(Decay(1.0))                                 # the trait's default: compiled once
    @test p isa Prob{Dynamic{Model}} && unwrap(p.m) === Decay(1.0)
    q = store(compiled_for(Decay(1.0)))
    @test q isa Prob{Decay}
end

module Geometry
using TraitWorld
@trait_module
@trait Shape begin
    area(s::Shape)::Float64
end
struct Sq; a::Float64; end
area(s::Sq) = s.a^2
@implement Shape Sq
kind(s::Shape) = keep(s) isa Dynamic ? :dynamic : :compiled
known(s::Sq) = kind(s)                                    # the caller knows the type
unknown(v::Vector{Any}) = kind(v[1])                      # it does not
end

@testset "trait modules" begin
    opts = ccall(:jl_get_module_trait_options, Cint, (Any,), Geometry)
    @test opts == 1 | 2 | 8                                # bounded, no_pirates, first_seen
    @test ccall(:jl_get_module_facts, Cint, (Any,), Geometry) == 1
    @test Geometry.known(Geometry.Sq(2.0)) === :compiled
    @test Geometry.unknown(Any[Geometry.Sq(2.0)]) === :dynamic
end

module Casts
using TraitWorld
import ..Model, ..Decay
plain(x::Int) = x + 1
traited(m::Model) = m
useless() = plain(compiled_for(1))                        # the method does not type it by a trait
useful() = traited(with_dynamic(Decay(1.0)))
module Inner                                              # a submodule's casts are the package's too
import ..plain
inner_useless() = plain(compiled_for(2))
end
Base.identity(::Val{:casts}) = plain(compiled_for(3))     # a method of another module's function
end

@testset "reports" begin
    fb = detect_dynamic_fallbacks(Geometry)
    @test any(t -> t[1].name === :kind && t[2] == 1, fb)
    @test isempty(detect_dynamic_fallbacks(Models))       # not a trait module
    uc = detect_unused_casts(Casts)
    @test sort([t[1].name for t in uc]) == [:identity, :inner_useless, :useless] && all(t -> t[4] == 1, uc)
    @test isempty(detect_unused_casts(Casts.Inner)) == false
    @test Casts.useless() == 2 && Casts.useful() === Decay(1.0)
end

module Bounded
using TraitWorld, Test
@trait_module
@trait Pt begin
    px(p::Pt)::Float64
end
struct P2; x::Float64; end
px(p::P2) = p.x
@implement Pt P2
ok(p::Pt) = px(p) + 1.0                                   # through the contract: accepted
kept(p::Pt) = keep(p)                                     # keeping it: within every contract
@open peek(p::Pt) = p.x                                   # open on purpose
scaled(p::Pt, k::Float64 = 2.0) = k * px(p)               # a default: its method calls one defined after it
later(p::Pt) = helper(p, 1.0)                             # a call that reaches no method yet
helper(p::Pt, k::Float64) = k + px(p)
end

@testset "bounded in a trait module" begin
    @test Bounded.ok(Bounded.P2(1.0)) == 2.0
    @test Bounded.peek(Bounded.P2(3.0)) == 3.0
    @test_throws TraitUseError Core.eval(Bounded, :(bad(p::Pt) = p.x))   # open: refused
    @test !isdefined(Bounded, :bad) || isempty(methods(Bounded.bad))
    # a call that reaches no method yet waits for the next definition in the module (compiler §6.7)
    @test Bounded.scaled(Bounded.P2(1.5)) == 3.0
    @test Bounded.later(Bounded.P2(1.0)) == 2.0
    @test isempty(check_definitions(Bounded))
    Core.eval(Bounded, :(waits(p::Pt) = missing_yet(p)))                 # waits: no method yet
    @test_throws TraitUseError Core.eval(Bounded, :(missing_yet(x) = x.x))  # opens it: refused here
    @test isempty(methods(Bounded.waits))
    # at the module's end, a call that still reaches no method is outside the contract
    e = try
        Core.eval(@__MODULE__, :(module Unfinished
            using TraitWorld
            @trait_module
            using ..Bounded: Pt, px
            g(p::Pt) = never(p, 1)
            never(p::Pt) = px(p)
        end)); nothing
    catch err
        err
    end
    @test e isa TraitUseError && occursin("never", sprint(showerror, e))
end
