# A member by its definition, `struct S <: X` and `abstract type A <: X end` (traits §5.2, §5.9; W-131): the
# `@implement` declares an entry like any membership. The parameters come from the declared supertype; a
# stated or field-given value that differs is refused. An abstract member's subtypes are checked at their
# first use. The entry makes the member a candidate, and the ambiguity report and strict mode see it.
using TraitWorld, Test

function thrown(ex)
    try
        Core.eval(@__MODULE__, ex)
        return nothing
    catch e
        while e isa LoadError; e = e.error; end
        return e
    end
end
latest(f, args...) = Base.invokelatest(f, args...)
member(S, X) = Base.invokelatest(() -> S <: X)
entries(T) = collect(getfield(Base.unwrap_unionall(T).name, :memberships, :acquire))
live(en) = getfield(en, :max_world, :acquire) == typemax(UInt64)
cands(X) = ccall(:jl_candidates_of, Any, (Any,), X)

@trait Shp begin
    sarea(s::Shp)::Float64
end
struct Sq <: Shp; side::Float64; end
sarea(s::Sq) = s.side^2
@implement Shp Sq

@testset "a declared subtype's entry" begin
    @test count(live, entries(Sq)) == 1
    c = cands(Shp)
    @test c !== nothing && Sq in c                      # a candidate of the trait's split
end

## the parameters come from the definition
@trait Hold{T} begin
    hget(h::Hold{T})::T
end
struct HB <: Hold{Int} end
hget(::HB) = 1
struct HC <: Hold{Int} end
hget(::HC) = 1
@trait Conv{To} begin
    @input To
    conv(c::Conv{To})::To
end
struct CB <: Conv{Int}; x::Int; end
conv(c::CB) = Float64(c.x)
@trait Boxed{T} begin
    v::T
end
struct HB3 <: Boxed{Int}; v::Float64; end

@testset "parameters from the declared supertype" begin
    @test thrown(:(@implement Hold HB)) === nothing     # the parameter from `HB <: Hold{Int}`
    @test member(HB, Hold{Int})
    e = thrown(:(@implement Hold{Float64} HC))           # a stated value that differs
    @test e isa ImplementError && occursin("declared", sprint(showerror, e))
    e = thrown(:(@implement Conv{Float64} CB))           # at an input parameter
    @test e isa ImplementError && occursin("declared", sprint(showerror, e))
    @test count(live, entries(CB)) == 0 && !member(CB, Conv{Float64})
    e = thrown(:(@implement Boxed HB3))                  # a field that differs
    @test e isa ImplementError && occursin("declared", sprint(showerror, e))
end

## an abstract member's subtypes are checked at their first use
@trait Gr begin
    greet(g::Gr)::String
end
abstract type AG <: Gr end
@implement Gr AG
struct Good <: AG end
greet(::Good) = "hi"
struct Bad <: AG end
hello(g::Gr) = greet(g)

@testset "an abstract member's subtypes" begin
    @test latest(hello, Good()) == "hi"
    @test_throws ImplementError latest(hello, Bad())
    @test TraitWorld._CHECKED[(Bad, Gr)] isa ImplementError
end

## forwarding, declared as a subtype
struct Inner2; side::Float64; end
sarea(i::Inner2) = i.side
@implement Shp Inner2
struct W2 <: Shp; s::Inner2; end
@implement Shp W2 by s

@testset "a forwarding member by its definition" begin
    es = filter(live, entries(W2))
    @test length(es) == 1 && getfield(only(es), :by) === :s
    @test latest(sarea, W2(Inner2(2.0))) == 2.0
end

## strict mode at the form, in both orders
@trait XF
@trait YF
fa(::XF) = :x
fa(::YF) = :y
struct SF1 <: XF end
@implement XF SF1
struct SF2 <: XF end
@implement YF SF2

@testset "strict mode at a declared subtype" begin
    TraitWorld.strict!(true)
    try
        # the trait of the definition first: the second trait refused, the type not its member
        @test thrown(:(@implement YF SF1)) isa ImplementError
        @test !member(SF1, YF)
        # the other trait first: the declaration of the definition's trait refused, but the type stays
        # its subtype by the definition (traits §6.3)
        @test thrown(:(@implement XF SF2)) isa ImplementError
        @test member(SF2, XF) && count(e -> live(e) && getfield(e, :set) === XF.name, entries(SF2)) == 0
    finally
        TraitWorld.strict!(false)
    end
end
