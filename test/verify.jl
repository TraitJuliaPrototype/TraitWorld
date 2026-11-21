# Closed programs (traits §16; W-114): `verify_main` lists every target a program reaches: the calls
# its code resolves, a function passed at a Callable at its signature, and every declared member as a
# target of an operation on a value known only by its trait; and the calls left to run time.
using TraitWorld, Test

@trait Shape2 begin
    area2(s::Shape2)::Float64
end
struct Circ; r::Float64; end
struct Sq; a::Float64; end
area2(c::Circ) = 3.0 * c.r^2
area2(s::Sq) = s.a^2
@implement Shape2 Circ
@implement Shape2 Sq

total2(xs::Vector{Shape2}) = (s = 0.0; for x in xs; s += area2(x); end; s)
applyf(f::Callable{Tuple{Float64}, Float64}, x::Float64) = f(x)
double(x::Float64) = 2x
main1(n::Int) = total2(Shape2[Circ(1.0), Sq(Float64(n))]) + applyf(double, Float64(n))
sloppy(v::Vector{Any}) = sum(v)

@testset "verify_main" begin
    r = verify_main(main1, (Int,))
    @test Tuple{typeof(area2), Circ} in r.targets && Tuple{typeof(area2), Sq} in r.targets
    @test Tuple{typeof(double), Float64} in r.targets
    @test Tuple{typeof(total2), Vector{Shape2}} in r.targets
    @test main1(2) == 3.0 + 4.0 + 4.0
    # a call folded where the program is compiled reaches no target: the wrapper's call
    @test !(Tuple{typeof(double), Float64} in verify_main(() -> applyf(compiled_for(double), 1.0), ()).targets)
    # a function boxed by `Callable`'s default where its type is known: the forwarder is compiled per function (its
    # signature's test folds, traits §9), so the box's call may be resolved where the program is compiled, as the
    # wrapper's is; a target or none, the program's result is the same
    r3 = verify_main(() -> applyf(double, 1.0), ())
    @test isempty(r3.holes) && applyf(double, 1.0) == 2.0
    r2 = verify_main(sloppy, (Vector{Any},))
    @test !isempty(r2.holes)
end

# the wrapper of a value known only by its trait (traits §16): the instances its calls run, at every declared member
scaled2(s::Shape2, k::Float64) = k * area2(s)
wrapsum(xs::Vector{Shape2}) = (s = 0.0; for x in xs; s += scaled2(compiled_for(x), 2.0)::Float64; end; s)

@testset "verify_main: the wrapper's members" begin
    r = verify_main(wrapsum, (Vector{Shape2},))
    @test Tuple{typeof(scaled2), Compiled{Circ}, Float64} in r.targets && Tuple{typeof(scaled2), Compiled{Sq}, Float64} in r.targets
    @test Tuple{typeof(compiled_for), Circ} in r.targets && Tuple{typeof(compiled_for), Sq} in r.targets
    @test Tuple{typeof(area2), Compiled{Circ}} in r.targets                 # what the wrapper's calls reach
    # the build's own check accepts the wrapping and the call it feeds: the wrapper's constructor, whose static
    # parameter the value known by its trait binds, branches over the members (compiler §7.6)
    @test isempty(r.holes)
    # the instances the wrapper's calls run at each member are entry points: no call in the code names them
    @test Tuple{typeof(scaled2), Compiled{Circ}, Float64} in r.entrypoints && Tuple{typeof(scaled2), Compiled{Sq}, Float64} in r.entrypoints
    @test add_entrypoints(r) === nothing
    @test wrapsum(Shape2[Circ(1.0), Sq(2.0)]) == 2.0 * (3.0 + 4.0)
end

# more members than a union keeps (compiler §7.6): the wrapper of a value known only by its trait is known by its
# members' wrappers, however many, and a call that takes it branches over them, each branch the call at `Compiled{M}`
@trait Shape5 begin
    area5(s::Shape5)::Float64
end
struct P1; a::Float64; end
struct P2; a::Float64; end
struct P3; a::Float64; end
struct P4; a::Float64; end
struct P5; a::Float64; end
area5(s::P1) = 1.0 * s.a
area5(s::P2) = 2.0 * s.a
area5(s::P3) = 3.0 * s.a
area5(s::P4) = 4.0 * s.a
area5(s::P5) = 5.0 * s.a
@implement Shape5 P1
@implement Shape5 P2
@implement Shape5 P3
@implement Shape5 P4
@implement Shape5 P5
scaled5(s::Shape5, k::Float64) = k * area5(s)
wrapsum5(xs::Vector{Shape5}) = (s = 0.0; for x in xs; s += scaled5(compiled_for(x), 2.0)::Float64; end; s)

@testset "verify_main: the wrappers of five members" begin
    r = verify_main(wrapsum5, (Vector{Shape5},))
    @test all(P -> Tuple{typeof(scaled5), Compiled{P}, Float64} in r.targets, (P1, P2, P3, P4, P5))
    # the build's own check: the call that takes the wrapper branches over the five members' wrappers
    @test isempty(r.holes)
    @test isfullytyped(fully_typed(wrapsum5, (Vector{Shape5},)))
    @test wrapsum5(Shape5[P1(1.0), P2(1.0), P3(1.0), P4(1.0), P5(1.0)]) == 2.0 * 15.0
end

# a call that does not know its argument's member (compiler §7.6): at a method that is not at the trait, the
# instance at the set runs; at one whose static parameter the value binds, the call branches over the members
@noinline plainpair(x) = (x, area2(x))
plainuse(xs::Vector{Shape2}) = plainpair(xs[1])[2]
@noinline typedpair(x::T) where {T} = (x, area2(x))
typeduse(xs::Vector{Shape2}) = typedpair(xs[1])[2]

@testset "verify_main: a value known only by its trait" begin
    @test isempty(verify_main(plainuse, (Vector{Shape2},)).holes)
    @test isempty(verify_main(typeduse, (Vector{Shape2},)).holes)
    @test plainuse(Shape2[Sq(2.0)]) == typeduse(Shape2[Sq(2.0)]) == 4.0
end

@testset "verify_main: entry points and the bound" begin
    r = verify_main(main1, (Int,))
    @test r.complete
    @test Tuple{typeof(area2), Circ} in r.entrypoints && Tuple{typeof(double), Float64} in r.entrypoints
    @test !(Tuple{typeof(total2), Vector{Shape2}} in r.entrypoints)      # a call in the code names it
    @test !verify_main(main1, (Int,); bound = 2).complete
end

# withfields on a box over three members (traits §6.5; lowering §8): the inner call, at the object known only by its
# trait, branches over the members (compiler §7.6), and the box made of the rebuilt object needs no dispatch: no hole
# there. The check still reports one: the declared-name test reads the declared fields (`_dynamic_field_type`),
# which the check does not fold where it lays the build's replacements of Base over the session as an overlay
# table (without the overlay it folds)
@trait WShape begin
    x::Float64
end
mutable struct WA; x::Float64; end
mutable struct WB; name::String; x::Float64; end
mutable struct WC; x::Float64; k::Int; end
@implement WShape WA
@implement WShape WB
@implement WShape WC
rebuildall(xs::Vector{Dynamic{WShape}}) = (n = 0; for d in xs; n += withfields(d; x = 0.5) isa Dynamic{WShape}; end; n)

@testset "verify_main: withfields on a box" begin
    xs = Dynamic{WShape}[Dynamic{WShape}(WA(1.0)), Dynamic{WShape}(WB("b", 2.0)), Dynamic{WShape}(WC(3.0, 1))]
    @test rebuildall(xs) == 3 && all(d -> unwrap(withfields(d; x = 0.5)).x == 0.5, xs)
    r = verify_main(rebuildall, (Vector{Dynamic{WShape}},))
    # no hole at the rebuilding: the inner call and the box's constructor
    @test !any(h -> occursin("_rebuilt(", h.call) || occursin("(Dynamic{WShape})(", h.call), r.holes)
    @test all(h -> any(c -> occursin("declared_field_type", c), h.cause), r.holes)
    @test_broken isempty(r.holes)
end
