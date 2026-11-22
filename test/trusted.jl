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
op_direct(v) = tstate(v[1], nothing) + 0.5
op_passed(v) = gstate(v[1], nothing) + 0.5

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
    # (in compiled code: at the prompt `v[1]` is a `TMA`, and each call is the member's own)
    @test_throws TypeError op_direct(v)                          # the operation's call at the set: asserted
    e = try op_passed(v); nothing catch e; e end                 # passed on to code compiled for the member
    @test e isa TypeError && e.got === 1
    @test gstate(TMA(), nothing) === 1                           # at the member's own type: its own result
end

# every declared result read at a set is checked where a call passes the value on (compiler §7.1, §7.4): the
# members' check does not reach a member's own instance in every world it runs in
apply2(f, x, y) = f(x, y)
isfloat(r) = r isa Float64 ? "yes" : "no"
@trait TWhere begin
    twop(x::TWhere, d::D)::Union{Float64, D} where {D}     # an operation's own `where` variable: checked at its bound
end
struct TWA end
twop(::TWA, d) = "s"
@implement TWhere TWA
@trait TFam begin
    tfop(x::TFam)::Float64
end
struct TFF{T} end
tfop(::TFF{T}) where {T} = 1                                # a family's member: checked at its first use
@implement TFam TFF{T} where {T}
abstract type TAbs end
struct TAR <: TAbs end
@trait TAbsT begin
    taop(x::TAbsT)::Float64
end
taop(::TAR) = 1                                             # an abstract type's member: checked at its first use
@implement TAbsT TAbs
struct TFw; inner::TAbs; end
@implement TAbsT TFw by inner                               # forwarding to a field typed by such a member
@trait TFld begin
    @const tfld::Float64
end
struct TFldF{T}; tfld::T; end
@implement TFld TFldF{T} where {T}                          # a declared field of a family's member
gettfld(x) = x.tfld
@trait TBelow begin
    tbop(x::TBelow)::Float64
end
struct TBA end
tbhelp(x) = 2.0
tbop(a::TBA) = tbhelp(a)
@implement TBelow TBA
tbhelp(::TBA) = 1                                           # a method below the serving method's body, defined later
@trait TKept begin
    tkop(x::TKept)::Float64
end
struct TKA end
tkop(::TKA) = 2.0
@implement TKept TKA
tkop(::Compiled{TKA}) = 1                                   # a method at the member's wrapper
isbc(t, x) = t(x) isa Bool
invoke_const() = invoke(isbc, Tuple{CB, Float64}, CB[x -> 1][1], 2.0) ? "yes" : "no"

@testset "every declared result read at a set, passed on; Core.invoke's constant" begin
    checked(f) = try f(); false catch e; e isa TypeError && e.func === :typeassert ? true : rethrow() end
    # (each in compiled code: a closure over a vector typed by the trait, called once)
    @test checked(() -> (r = apply2(twop, TWhere[TWA()][1], 1); r isa Union{Float64, Int} ? "yes" : "no"))
    @test checked(() -> isfloat(apply1(tfop, TFam[TFF{Int}()][1])))
    @test checked(() -> isfloat(apply1(taop, TAbsT[TAR()][1])))
    @test checked(() -> isfloat(apply1(taop, TAbsT[TFw(TAR())][1])))
    @test checked(() -> isfloat(apply1(gettfld, TFld[TFldF{Int}(1)][1])))
    @test checked(() -> isfloat(apply1(tbop, TBelow[TBA()][1])))
    @test checked(() -> isfloat(apply1(tkop, TKept[compiled_for(TKA())][1])))
    # the member's own result where its own code is called at its type
    @test apply1(tfop, TFF{Int}()) === 1 && apply1(tbop, TBA()) === 1
    # a constant read at the signature is not taken through `Core.invoke`: the function's own answer
    @test invoke_const() == "no"
end
