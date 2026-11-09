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

@enforce_fully_typed etotal(h::Holder) = sum(sink, h.data)
@enforce_fully_typed etwice(x::Int) = 2x
@enforce_fully_typed eabs(h::Holder) = h.data
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

@testset "fully typed mode" begin
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

    h = Holder([1, 2])
    @test_throws NotFullyTypedError etotal(h)
    @test etwice(3) == 6
    @test_throws AbstractTypeError eabs(h)
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
