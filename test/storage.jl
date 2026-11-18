# Storage keeps the form it is given (traits §8.1): a field or element typed by the trait holds a plain member, a box
# or a wrapper, each by its own type; what is stored does not depend on who stores it, since nothing beside the
# value decides how an argument is compiled (traits §7.5).
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
struct KScene; shapes::Vector{KShape}; end
kadd!(sc::KScene, s::KShape) = (push!(sc.shapes, s); sc)
ktotal(sc::KScene) = sum(karea, sc.shapes; init = 0.0)
end
using .KeptM
kknown(sc) = (kadd!(sc, KCircle(1.0)); sc)
kunknown(sc, xs::Vector{Any}) = (kadd!(sc, xs[1]); sc)

@testset "storage keeps the form given" begin
    a = kknown(KScene(KShape[])); b = kunknown(KScene(KShape[]), Any[KCircle(1.0)])
    ka, kb = a.shapes[1], b.shapes[1]
    # the same value whoever stores: the member itself, with its other traits
    @test ka === kb === KCircle(1.0)
    @test ka isa KScalable && kb isa KScalable
    @test ktotal(a) == ktotal(b) == 3.0
    # a box and a wrapper keep their forms: a box is of its trait only, a wrapper of every trait of its object
    sc = KScene(KShape[])
    kadd!(sc, Dynamic{KShape}(KCircle(2.0))); kadd!(sc, compiled_for(KCircle(2.0)))
    @test sc.shapes[1] isa Dynamic{KShape} && !(sc.shapes[1] isa KScalable)
    @test sc.shapes[2] isa Compiled{KCircle} && sc.shapes[2] isa KScalable
    @test unwrap(sc.shapes[1]) === unwrap(sc.shapes[2]) === KCircle(2.0)
    @test ktotal(sc) == 24.0
    # storage typed by the box boxes what is assigned to it (traits §8.1)
    v = Dynamic{KShape}[]
    push!(v, KCircle(1.0)); push!(v, compiled_for(KCircle(1.0)))
    @test all(x -> x isa Dynamic{KShape} && unwrap(x) === KCircle(1.0), v)
end
