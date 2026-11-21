# A result trusted from a declared result (compiler §7.4, §7.1; traits §9, §7.9, §5.10): compiled code never takes
# a value that its call's type excludes. A function known only as `Callable{A, S}` (an element of a
# `Vector{Callable{A, S}}`) passed on to code compiled for its own type has the call that passes it checked against
# the type inferred for it; so does an operation's call whose result its members' check does not reach (a further
# argument declared abstract), passed on to code compiled for the member. The check of a `Callable`'s result is the
# box's: "in Callable", with its addition for `Nothing`. A box checks where it is called; a wrapper is the function.
using TraitWorld, Test

const CB = Callable{Tuple{Float64}, Bool}
const CF = Callable{Tuple{Float64}, Float64}
const CN = Callable{Tuple{Float64}, Nothing}
apply1(t, x) = t(x)
@noinline lvl2(t, x) = apply1(t, x)
struct Holder{T}; t::T; end
callh(h) = h.t(2.0)
@noinline nsp(@nospecialize(t), x) = t(x)
isb(t, x) = t(x) isa Bool
nr(t, x) = (r = t(x); r isa Bool && error("a Bool"); r)

@trait TMeas begin
    tstate(x::TMeas, s)::Float64                  # a further argument declared abstract: not inferred at the check
end
struct TMA end
tstate(::TMA, s) = 1
@implement TMeas TMA
@noinline gstate(m, s) = tstate(m, s)

callable_error(f) = try f(); nothing catch e; e isa TypeError && e.func === :Callable ? e : rethrow() end

@testset "a function known only by its signature, passed on" begin
    vb = CB[x -> 1]
    vf = CF[x -> 1]
    # each the box's check where it was a wrong answer, a value read as a type it is not, or a stop
    for f in (() -> all(t -> t(2.0), vb), () -> any(t -> t(2.0), vb), () -> map(t -> t(2.0), vf),
              () -> sum(t -> t(2.0), vf), () -> [t(2.0) for t in vf], () -> apply1(vb[1], 2.0) ? 1 : 2,
              () -> apply1(vf[1], 2.0) + 0.5, () -> lvl2(vf[1], 2.0) + 0.5, () -> callh(Holder(vf[1])) + 0.5,
              () -> nsp(vf[1], 2.0) + 0.5, () -> invoke(apply1, Tuple{CF, Float64}, vf[1], 2.0) + 0.5,
              () -> (nr(vb[1], 2.0); 0), () -> vf[1](2.0))
        e = callable_error(f)
        @test e isa TypeError && e.got === 1
    end
    # a constant read from the instance at the signature is not taken: the function's own answer
    @test (isb(vb[1], 2.0) ? "yes" : "no") == "no"
    # the addition for `Nothing`, at the direct call and at a call that passes the function on
    vn = CN[x -> 1]
    for f in (() -> vn[1](2.0), () -> apply1(vn[1], 2.0))
        e = callable_error(f)
        @test e isa TypeError && occursin("end the function with `nothing`", sprint(showerror, e))
    end
    # a function that keeps its contract passes, as before
    @test map(t -> t(2.0), CF[x -> 2x]) == [4.0] && all(t -> t(2.0), CB[x -> x > 1])
end

@testset "the controls: the box, the wrapper" begin
    # a box checks its result where it is called
    e = callable_error(() -> map(t -> t(2.0), CF[Dynamic{CF}(x -> 1)]))
    @test e isa TypeError && e.got === 1
    # a wrapper known only by the signature is checked as the function is; passed as itself it is the function
    e = callable_error(() -> map(t -> t(2.0), CF[compiled_for(x -> 1)]))
    @test e isa TypeError && e.got === 1
    @test apply1(compiled_for(x -> 1), 2.0) === 1
end

@testset "an operation's result its members' check does not reach, passed on" begin
    v = TMeas[TMA()]
    @test_throws TypeError tstate(v[1], nothing) + 0.5          # the operation's call at the set: asserted
    e = try gstate(v[1], nothing) + 0.5; nothing catch e; e end  # passed on to code compiled for the member
    @test e isa TypeError && e.got === 1
    @test gstate(TMA(), nothing) === 1                           # at the member's own type: its own result
end
