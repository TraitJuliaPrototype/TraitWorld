# Concreteness and fully typed mode (traits §14; compiler §2.7; W-114): the report `fully_typed` with
# root causes through layers; `@enforce_fully_typed` and `@warn_not_fully_typed` on a method and on a
# trait module; a trait's and a method's concrete parts.
using TraitWorld, Test

struct Holder
    data::AbstractVector                       # the root cause below
end
sink(x) = x
total(h::Holder) = sum(sink, h.data)           # a call at an abstract type
twice(x::Int) = 2x
nested(h::Holder) = deeper(h)
deeper(h::Holder) = first(h.data) + 1          # a run-time site one layer down
getdata(h::Holder) = h.data

@trait Lengthy begin
    llen(x::Lengthy)::Int
end
struct Rope; n::Int; end
llen(r::Rope) = r.n
@implement Lengthy Rope
usesop(xs::Vector{Lengthy}) = llen(xs[1]) + 1      # an operation on a value known by its trait: declared
describe1(x::Lengthy) = llen(x) > 1 ? "long" : "short"
passes(xs::Vector{Lengthy}) = describe1(xs[1])     # a value known by its trait passed to a method at the trait
@enforce_fully_typed epasses(xs::Vector{Lengthy}) = describe1(xs[1])
# an operation at an element of `Vector{Any}`: a build branches over its methods, so the mode raises nothing (traits §14)
@enforce_fully_typed eany(xs::Vector{Any}) = llen(xs[1])
# a call on an operation's result of an abstract type, at a box: the result is the root cause (traits §14)
@trait Datum begin
    ddata(d::Datum)::AbstractVector
end
struct DVec; v::Vector{Float64}; end
ddata(d::DVec) = d.v
@implement Datum DVec
@enforce_fully_typed dsum(d::Datum) = sum(ddata(d))

@enforce_fully_typed etotal(h::Holder) = sum(sink, h.data)
@enforce_fully_typed etwice(x::Int) = 2x
@enforce_fully_typed eabs(h::Holder) = h.data
@enforce_concrete_only result cabs(h::Holder) = h.data
@enforce_concrete_only result cabs2(x::Int) = 2x
@warn_not_fully_typed wtotal(h::Holder) = sum(sink, h.data)

module Strict
using TraitWorld
@enforce_fully_typed @trait_module
import ..Holder
mtotal(h::Holder) = sum(h.data)
mgood(x::Int) = x + 1
end

@trait KVec{T} begin
    @enforce_concrete_only T Self
    T = eltype(Self)
    klen(v::KVec)::Int
end
klen(v::Vector) = length(v)

@trait Soft{T} begin
    @warn_on_abstract T
    T = eltype(Self)
    slen(v::Soft)::Int
end
slen(v::Vector) = length(v)

@enforce_concrete_only T firstof(v::Vector{T}) where {T} = v[1]
@warn_on_abstract T wfirstof(v::Vector{T}) where {T} = v[1]

# a trait whose members are compiled once in a session: a build compiles for the type where the call knows it
module OnceLib
using TraitWorld
@trait_module
@trait Model begin
    @default_dynamic
    rate(m::Model, u::Float64)::Float64
end
struct Kept{K}; k::K; end
# the trait's default as generated methods (W-151): a plain member is boxed by the forwarder
inner(m::Model, u::Float64) = Kept(m)
outer(m::Model, u::Float64) = inner(m, u)            # passes the kept form on
withkw(m::Model, u::Float64; scale = 1.0) = Kept(m)  # a keyword method: its forwarder passes the keywords on
end
struct Decay; k::Float64; end
OnceLib.rate(d::Decay, u::Float64) = -d.k * u
@implement OnceLib.Model Decay
const DECAY = Decay(1.0)
once_outer() = OnceLib.outer(DECAY, 1.0)
once_kw() = OnceLib.withkw(DECAY, 1.0; scale = 2.0)

@testset "fully typed mode" begin
    # a trait with a `Dynamic` default: in a session its methods are compiled once, and a call that passes
    # the argument on is made when it runs; a build compiles for the type the call knows (compiler §7.6)
    @test once_outer() isa OnceLib.Kept{Dynamic{OnceLib.Model}}            # the box, by the forwarder
    @test once_kw() isa OnceLib.Kept{Dynamic{OnceLib.Model}}
    @test isfullytyped(fully_typed(once_outer, ())) && isfullytyped(fully_typed(once_kw, ()))
    r = fully_typed(total, (Holder,))
    @test !isfullytyped(r)
    s = sprint(show, MIME"text/plain"(), r)
    @test occursin("field `data` of `Holder` is declared AbstractVector", s)
    @test isfullytyped(fully_typed(twice, (Int,)))
    # through a layer: the site in the callee, its cause there
    r2 = fully_typed(nested, (Holder,))
    @test !isfullytyped(r2) && any(x -> x.code.def.name === :deeper, r2.sites)
    # an abstract result: its cause
    r3 = fully_typed(getdata, (Holder,))
    @test isfullytyped(r3) && occursin("field `data`", join(r3.result_cause))
    # operations on a value known by its trait count as declared
    @test isfullytyped(fully_typed(usesop, (Vector{Lengthy},)))
    # fully typed is exactly what a closed build compiles (traits §14, §16): a value known by its trait
    # passed to a method at the trait is resolved by the members, as the build resolves it
    @test isfullytyped(fully_typed(passes, (Vector{Lengthy},)))
    @test epasses(Lengthy[Rope(3)]) == "long"       # the mode raises only where a build would refuse
    @test eany(Any[Rope(3)]) == 3 && eany(Any[Dynamic{Lengthy}(Rope(2))]) == 2
    @test dsum(DVec([1.0, 2.0])) == 3.0              # at a member the result is the member's
    e = try dsum(Dynamic{Datum}(DVec([1.0]))) catch e; e end
    @test e isa NotFullyTypedError
    m = sprint(showerror, e)
    @test occursin("`ddata` returns AbstractVector at ddata(::Dynamic{", m) && !occursin("Tuple{", m)   # a call, not the tuple type

    h = Holder([1, 2])
    @test_throws NotFullyTypedError etotal(h)
    @test etwice(3) == 6
    @test eabs(h) == [1, 2]                          # a result of an abstract type is no fault of the mode
    @test_throws AbstractTypeError cabs(h)           # a method that asks for a concrete result
    @test cabs2(3) == 6
    e = try etotal(h) catch e; e end
    @test occursin("field `data` of `Holder`", sprint(showerror, e))
    @test (@test_logs (:warn, r"@warn_not_fully_typed") wtotal(h)) == 3
    @test (@test_logs wtotal(h)) == 3                          # once per signature

    # the module's option
    @test_throws NotFullyTypedError Strict.mtotal(h)
    @test Strict.mgood(1) == 2
end

@testset "concrete parts" begin
    @test_throws ImplementError @eval @implement KVec Vector{Any}
    @eval @implement KVec Vector{Float64}
    @test klen([1.0]) == 1
    # Self is the forwarding field's type where the member forwards (traits §4.4)
    @eval struct LooseBox; data::AbstractVector{Float64}; end
    @eval struct TightBox; data::Vector{Float64}; end
    e = try @eval(@implement KVec LooseBox by data); nothing catch err; err end
    @test e isa ImplementError && occursin("Self is AbstractVector{Float64}", sprint(showerror, e))
    @eval @implement KVec TightBox by data
    @test klen(TightBox([1.0, 2.0])) == 2
    @test_logs (:warn, r"not concrete") @eval @implement Soft Vector{Any}
    @test firstof([1.0]) == 1.0
    @test_throws TraitUseError firstof(Any[1])
    @test (@test_logs (:warn, r"not concrete") wfirstof(Any[1])) == 1
    @test (@test_logs wfirstof(Any[2])) == 2                    # once per method and type
    @test TraitWorld.is_concrete_part(Vector{Union{Int, Missing}})
    @test !TraitWorld.is_concrete_part(Dict{String, Any})
    @test TraitWorld.is_concrete_part(Vector{Dynamic{Lengthy}})
    @test TraitWorld.is_concrete_part(Vector{Lengthy})            # a trait as a parameter's value
end
