# Kept{X} (traits §7.8): storage that holds a member with its attribute, in one type.
using Test, TraitWorld

module KeptM
using TraitWorld
@trait_module
export KShape, KScalable, KCircle, KScene, kadd!, karea, ktotal
@trait KShape begin
    karea(s::KShape)::Float64
end
@trait KScalable
struct KCircle; r::Float64; end
karea(c::KCircle) = 3.0 * c.r^2
@implement KShape KCircle
@implement KScalable KCircle
struct KScene; shapes::Vector{Kept{KShape}}; end
kadd!(sc::KScene, s::KShape) = (push!(sc.shapes, keep(s)); sc)
ktotal(sc::KScene) = sum(k -> kept_call(karea, k), sc.shapes)
end
using .KeptM
kknown(sc) = (kadd!(sc, KCircle(1.0)); sc)
kunknown(sc, xs::Vector{Any}) = (kadd!(sc, xs[1]); sc)

@testset "Kept" begin
    a = kknown(KScene(Kept{KShape}[])); b = kunknown(KScene(Kept{KShape}[]), Any[KCircle(1.0)])
    ka, kb = a.shapes[1], b.shapes[1]
    # one type whoever stores; the attribute beside the object
    @test typeof(ka) === typeof(kb) === Kept{KShape}
    @test !isdynamic(ka) && isdynamic(kb)
    # the same lines give the same answers
    @test (ka isa KScalable) == (kb isa KScalable) == false
    @test (unwrap(ka) isa KScalable) && (unwrap(kb) isa KScalable)
    @test unwrap(ka) == unwrap(kb)
    # the value with its attribute, and the call under it
    @test ka[] isa KCircle && kb[] isa Dynamic{KShape}
    @test ktotal(a) == ktotal(b) == 3.0
    # conversions
    @test Kept{KShape}(KCircle(2.0)) isa Kept{KShape}
    @test isdynamic(Kept{KShape}(Dynamic{KShape}(KCircle(2.0))))
    @test convert(Kept{KShape}, ka) === ka
    @test_throws TypeError Kept{KShape}(1)
    @test_throws ArgumentError Kept{Int}(1)
    @test_throws MethodError push!(KShape[], ka)          # storage typed by the trait takes `unwrap(k)`
    @test sprint(show, kb) == "Kept{$(KShape)}($(KCircle(1.0)), Dynamic)"
end
