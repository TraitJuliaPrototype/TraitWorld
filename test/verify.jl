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
    # a call folded where the program is compiled reaches no target
    @test !(Tuple{typeof(double), Float64} in verify_main(() -> applyf(double, 1.0), ()).targets)
    r2 = verify_main(sloppy, (Vector{Any},))
    @test !isempty(r2.holes)
end

# a call with `compiled_for` on a value known only by its trait: the callee at each declared member
scaled2(s::Shape2, k::Float64) = k * area2(s)
castsum(xs::Vector{Shape2}) = (s = 0.0; for x in xs; s += scaled2(compiled_for(x), 2.0)::Float64; end; s)

@testset "verify_main: a cast's members" begin
    r = verify_main(castsum, (Vector{Shape2},))
    @test Tuple{typeof(scaled2), Circ, Float64} in r.targets && Tuple{typeof(scaled2), Sq, Float64} in r.targets
    @test isempty(r.holes)
    # the instance the cast runs at each member is an entry point
    mis = [e for e in r.entrypoints if e isa Core.MethodInstance]
    @test Set(mi.specTypes for mi in mis) == Set([Tuple{typeof(scaled2), Circ, Float64}, Tuple{typeof(scaled2), Sq, Float64}])
    @test add_entrypoints(r) === nothing
    @test castsum(Shape2[Circ(1.0), Sq(2.0)]) == 2.0 * (3.0 + 4.0)
end

@testset "verify_main: entry points and the bound" begin
    r = verify_main(main1, (Int,))
    @test r.complete
    @test Tuple{typeof(area2), Circ} in r.entrypoints && Tuple{typeof(double), Float64} in r.entrypoints
    @test !(Tuple{typeof(total2), Vector{Shape2}} in r.entrypoints)      # a call in the code names it
    @test !verify_main(main1, (Int,); bound = 2).complete
end
