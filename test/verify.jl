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

# a call at a value known only by its trait (a box's object) where the member's type chooses the method (compiler
# §7.6): a method at a type that is no set (a struct, a family) takes some members; the call branches over the members
@trait Shape6 begin
    area6(s::Shape6)::Float64
end
@trait Named6 begin
    name6(s::Named6)::String
end
struct Sq6; a::Float64; end
struct Ci6; r::Float64; end
struct Rec6{F}; f::F; end
area6(s::Sq6) = s.a^2
area6(c::Ci6) = 3.0 * c.r^2
area6(r::Rec6) = 1.0
name6(s::Sq6) = "square"
@implement Shape6 Sq6
@implement Shape6 Ci6
@implement Shape6 Rec6{F} where {F}
@implement Named6 Sq6
describe6(@nospecialize(x)) = "a shape"
describe6(x::Named6) = name6(x)                   # at a trait: taken at the set instance, once
kind6(@nospecialize(x)) = 1
kind6(x::Ci6) = 2                                 # at a concrete type
inner6(@nospecialize(x)) = 0.0
inner6(r::Rec6) = Float64(length(string(r.f)))    # at a family, reading the object's field
report6(d::Dynamic{Shape6}) = (describe6(unwrap(d)), kind6(unwrap(d)), inner6(unwrap(d)) + area6(d))
function choice6(n::Int)
    s = 0.0; k = 0; t = ""
    for d in Dynamic{Shape6}[Dynamic{Shape6}(Sq6(Float64(n))), Dynamic{Shape6}(Ci6(1.0))]
        a, b, c = report6(d)
        t *= a; k += b; s += c
    end
    return (t, k, s)
end

@testset "verify_main: the member's type chooses the method" begin
    @test isempty(verify_main(choice6, (Int,)).holes)
    @test isfullytyped(fully_typed(choice6, (Int,)))
    @test choice6(2) == ("squarea shape", 3, 7.0)
    @test report6(Dynamic{Shape6}(Rec6(:ab))) == ("a shape", 1, 3.0)
end

# A set instance's members by use are the types that flow to it (compiler §7.6): forgotten at a place typed by it, or
# at a place whose values the code passes on or narrows to one. The build's check run in the session, with each
# split's set type and its members (`closed_check`'s third result) and its rounds (the fourth).
const _CC = Base.Compiler
function _closed_members(f, args)
    world = Base.get_world_counter()
    mi = _CC.specialize_method(Base._methods_by_ftype(Base.signature_type(f, args), 1, world)[1])
    res = _CC.closed_check(Any[mi], world, TraitWorld._build_base())
    members = Dict{Any,Vector{Any}}()
    length(res) >= 3 && for (X, ms) in res[3]
        members[X] = ms
    end
    return (; members, rounds = length(res) >= 4 ? res[4] : typemax(Int), errors = count(e -> !e[1], res[1]))
end
const F9a = Callable{Tuple{Float64}, Float64}
const F9b = Callable{Tuple{Int}, Int}
# (each signature's split is the wrapper's constructor, `compiled_for(f)`, which branches over its members)
sig9a(f::Callable{Tuple{Float64}, Float64}, x::Float64) = compiled_for(f)(x)
sig9b(f::Callable{Tuple{Int}, Int}, x::Int) = compiled_for(f)(x)
double9(x::Float64) = 2x
quad9(x::Float64) = 4x
inc9(x::Int) = x + 1
triple9(x::Int) = 3x
struct Holder9; f::Function; end
@noinline keep9(h::Holder9) = h
struct Wrap9{F}; f::F; end
(w::Wrap9)(x::Int) = round(Int, w.f(Float64(x)))
@implement Callable Wrap9{F} where {F}
function handon9(d::Dynamic{Callable{Tuple{Float64}, Float64}})
    ws = Callable{Tuple{Int}, Int}[]          # a place typed by the second signature
    push!(ws, Wrap9(unwrap(d)))                # `Wrap9{M}` for each member `M` at the first
    return sig9b(ws[1], 3) + sig9a(d, 1.0)
end
@noinline anyhand9(v::Vector{Any}) = (x = v[1]; x isa Callable{Tuple{Float64}, Float64} ? sig9a(x, 1.0) : 0.0)
two9(n::Int) = sig9a(double9, Float64(n)) + sig9b(inc9, n) + keep9(Holder9(triple9)).f(1)
passed9(n::Int) = sig9a(double9, Float64(n)) + sig9b(keep9(Holder9(triple9)).f, n)
wrapped9(n::Int) = handon9(Dynamic{F9a}(double9)) + sig9b(inc9, n)
viaany9(n::Int) = anyhand9(Any[quad9]) + sig9a(double9, Float64(n))

@testset "closed check: the members by the types that flow to a set instance" begin
    # two signatures, a function handed to each: each signature's members are the functions handed to it; a field
    # `f::Function` adds none until its value is handed on
    r = _closed_members(two9, (Int,))
    @test r.errors == 0
    @test get(r.members, F9a, nothing) == Any[typeof(double9)]
    @test get(r.members, F9b, nothing) == Any[typeof(inc9)]
    r = _closed_members(passed9, (Int,))
    @test r.errors == 0
    @test get(r.members, F9a, nothing) == Any[typeof(double9)]
    @test get(r.members, F9b, nothing) == Any[typeof(triple9)]
    # a callable family whose constructor is fed the first signature's members, handed on at the second: the
    # rounds converge, `Wrap9{M}` a member at the second only
    r = _closed_members(wrapped9, (Int,))
    @test r.errors == 0 && r.rounds < 16
    @test get(r.members, F9a, nothing) == Any[typeof(double9)]
    @test Wrap9{typeof(double9)} in get(r.members, F9b, Any[]) && !any(T -> T <: Wrap9, get(r.members, F9a, Any[]))
    # a value that reaches the set through `Any` and a test is counted
    r = _closed_members(viaany9, (Int,))
    @test r.errors == 0
    @test typeof(quad9) in get(r.members, F9a, Any[])
    @test (two9(2), passed9(2), wrapped9(2), viaany9(2)) == (10.0, 10.0, 11.0, 8.0)
end

# the kept form by use (compiler §7.6): the box is a branch where the build forgets a box at a place typed by the
# set, and never at the object a box holds
@trait Shape9 begin
    area9(s::Shape9)::Float64
end
struct Sq9; a::Float64; end
struct Ci9; r::Float64; end
area9(s::Sq9) = s.a^2
area9(c::Ci9) = 3.0 * c.r^2
@implement Shape9 Sq9
@implement Shape9 Ci9
boxes9(n::Int) = (v = Shape9[Dynamic{Shape9}(Sq9(Float64(n))), Ci9(1.0)]; s = 0.0; for x in v; s += area9(x); end; s)
# no member (compiler §7.6): an operation of a trait whose one entry is a family the program never uses
@trait Lonely9 begin
    lone9(x::Lonely9)::Int
end
struct LoF9{T}; end
lone9(::LoF9) = 1
@implement Lonely9 LoF9{T} where {T}
lonely9(v::Vector{Lonely9}) = isempty(v) ? 0 : lone9(v[1])

@testset "closed check: the kept form by use; no member" begin
    r = _closed_members(choice6, (Int,))                   # boxes in a `Vector{Dynamic{Shape6}}`: no box at `Shape6`
    @test r.errors == 0 && haskey(r.members, Shape6)
    @test !any(T -> T <: Dynamic, r.members[Shape6])
    r = _closed_members(boxes9, (Int,))                    # a box in a `Vector{Shape9}`
    @test r.errors == 0
    @test Set(get(r.members, Shape9, Any[])) == Set(Any[Sq9, Ci9, Dynamic{Shape9}])
    @test boxes9(2) == 7.0
    # the operation's call raises `MethodError`: no hole
    r = _closed_members(lonely9, (Vector{Lonely9},))
    @test r.errors == 0 && get(r.members, Lonely9, nothing) == Any[]
    @test lonely9(Lonely9[]) == 0 && lonely9(Lonely9[LoF9{Int}()]) == 1
end
