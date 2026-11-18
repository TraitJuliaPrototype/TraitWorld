# The trait's default and trait modules (traits §4.6, §7.1, §7.5, §7.8, §8.2, §13): a method is compiled for the
# value it is given (a plain member, the box `Dynamic{X}`, the wrapper `compiled_for(x)`); a trait that declares
# `@default_dynamic` boxes a plain member at its methods; no module option decides how a trait argument is compiled.
using TraitWorld, Test

module Models                                # the trait's package
using TraitWorld
@trait Model begin                           # no default: a plain member as it is
    rhs(m::Model, u::Float64)::Float64
end
form(x) = x isa Dynamic ? :box : x isa Compiled ? :wrapper : :plain
kind(m::Model) = form(m)
solve(m::Model, u0::Float64) = rhs(m, u0) + u0
@trait EModel begin                          # erases by default: a method at it makes its forwarder
    @default_dynamic
    erate(m::EModel, u::Float64)::Float64
end
eform(m::EModel) = form(m)
esolve(m::EModel, u0::Float64) = erate(m, u0) + u0
end
using .Models: Model, rhs, solve, EModel, erate

module UserModels                            # a user's members
using TraitWorld
import ..Model, ..rhs, ..EModel, ..erate
struct Decay; k::Float64; end
rhs(d::Decay, u::Float64) = -d.k * u
@implement Model Decay
erate(d::Decay, u::Float64) = -d.k * u
@implement EModel Decay
struct Growth; k::Float64; end
rhs(g::Growth, u::Float64) = g.k * u
@implement Model Growth
erate(g::Growth, u::Float64) = g.k * u
@implement EModel Growth
end
using .UserModels: Decay, Growth

@testset "the trait's default" begin
    # `@default_dynamic`: a method at the trait makes its forwarder where it is defined: a plain member is boxed, a
    # box and a wrapper pass as they are. A trait without the default takes a plain member as it is
    @test Models.eform(Decay(1.0)) === :box && Models.eform(Growth(1.0)) === :box
    @test Models.eform(compiled_for(Decay(1.0))) === :wrapper
    @test Models.eform(Dynamic{EModel}(Growth(2.0))) === :box
    @test Models.esolve(Decay(0.5), 2.0) == 1.0 && Models.esolve(compiled_for(Growth(0.5)), 2.0) == 3.0
    @test Models.kind(Decay(1.0)) === :plain
    @test Models.kind(compiled_for(Decay(1.0))) === :wrapper && Models.kind(Dynamic{Model}(Decay(1.0))) === :box
    @test solve(Decay(0.5), 2.0) == 1.0 && solve(Growth(0.5), 2.0) == 3.0
    @test solve(compiled_for(Decay(0.5)), 2.0) == solve(Dynamic{Model}(Decay(0.5)), 2.0) == 1.0
    # `@default_compiled` is not an item of a trait's body: a trait without the default takes a member as it is
    e = try Core.eval(Models, :(@trait CModel begin
            @default_compiled
            crate(m::CModel)::Float64
        end)); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    @test e isa ErrorException && occursin("@default_compiled", e.msg) && occursin("@default_dynamic", e.msg)
end

@testset "a struct parameter records the form" begin
    # traits §8.2: the default constructor sets the parameter to the type of what it is given
    struct Prob{M <: Model}; m::M; end
    store(m::Model) = Prob(m)
    @test store(Decay(1.0)) isa Prob{Decay}
    @test store(Dynamic{Model}(Decay(1.0))) isa Prob{Dynamic{Model}} && unwrap(store(Dynamic{Model}(Decay(1.0))).m) === Decay(1.0)
    @test store(compiled_for(Decay(1.0))) isa Prob{Compiled{Decay}}
    # at a trait that erases by default, the method's argument is a kept form
    struct EProb{M <: EModel}; m::M; end
    kstore(m::EModel) = EProb{typeof(m)}(m)
    @test kstore(Decay(1.0)) isa EProb{Dynamic{EModel}}
    @test kstore(compiled_for(Decay(1.0))) isa EProb{Compiled{Decay}}
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
kind(s::Shape) = s isa Dynamic ? :box : :plain
known(s::Sq) = kind(s)                                    # the caller knows the type
unknown(v::Vector{Any}) = kind(v[1])                      # it does not
kind2(s::Shape) = s isa Dynamic ? :box : :plain
unknown2(v::Vector{Any}) = kind2(v[1])                    # the only caller of kind2
end

@testset "trait modules" begin
    opts = ccall(:jl_get_module_trait_options, Cint, (Any,), Geometry)
    @test opts == 1 | 2 | 64                               # bounded, no_pirates, owner_only; neither dynamic nor first_seen
    @test ccall(:jl_get_module_facts, Cint, (Any,), Geometry) == 1
    @test Geometry.known(Geometry.Sq(2.0)) === :plain
    @test Geometry.unknown(Any[Geometry.Sq(2.0)]) === :plain
    # the value's type decides (traits §7.5): a call whose caller does not know the type is compiled as Julia compiles
    # any call (here the one method's body inlined behind a test of the type), and the member is passed as itself
    @test Geometry.unknown2(Any[Geometry.Sq(2.0)]) === :plain
    # no option decides how a trait argument is compiled (traits §13): `dynamic` and `first_seen` are refused,
    # with the design's forms named
    for opt in (:(dynamic = true), :(first_seen = false), :first_seen)
        e = try Core.eval(@__MODULE__, :(module WithOpt
                using TraitWorld
                @trait_module $opt
            end)); nothing catch err; err end
        while e isa LoadError; e = e.error; end
        @test e isa ErrorException && occursin("Dynamic{", e.msg) && occursin("@default_dynamic", e.msg) &&
              occursin("compiled_for(x)", e.msg)
    end
    e = try Core.eval(@__MODULE__, :(module WithOpt2; using TraitWorld; @trait_module typo = true; end)); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    @test e isa ErrorException && occursin("facts, bounded, no_pirates or owner_only", e.msg)
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
@unbounded peek(p::Pt) = p.x                                   # unbounded on purpose
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
