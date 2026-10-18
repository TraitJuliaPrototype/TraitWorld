# verify_main and dynamic values (note "AOT": a `Dynamic` value adds the conformances whose types
# reach the place it is made): operations on dynamic values, and entries called with a trait object
# opened from one, get one target per trait object type the program keeps.
# Runs inside runtests.jl, or alone: julia --project=. test/verify_dynamic.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module VDyn
    using TraitWorld
    export Shape, area, scaled, Sq, Circ, shapes, totalarea
    @trait Shape{R} begin
        area(r::R)::Float64
    end
    struct Sq; a::Float64; end
    struct Circ; r::Float64; end
    @implement Shape{Sq} begin
        area(s) = s.a^2
    end
    @implement Shape{Circ} begin
        area(c) = 3.0 * c.r^2
    end
    scaled(s::Shape, k::Float64) = k * area(s)            # an entry, called with an opened dynamic value
    shapes() = Dynamic{Shape}[Dynamic{Shape}(Sq(2.0)), Dynamic{Shape}(Circ(1.0))]
    function totalarea(v::Vector{Dynamic{Shape}})
        s = 0.0
        for d in v
            s += area(d) + scaled(TraitWorld.opened(d), 2.0)::Float64
        end
        return s
    end
    end
    vdyn_main(args::Vector{String}) = (println(Core.stdout, VDyn.totalarea(VDyn.shapes())); 0)
end)

@testset "verify_main: targets of dynamic values" begin
    try
        @test Base.invokelatest(getglobal(Main, :vdyn_main), String[]) == 0
        r = Base.invokelatest(verify_main, getglobal(Main, :vdyn_main), (Vector{String},))
        @test !any(h -> !h.errorpath, r.holes)
        # two sites on dynamic values (an operation, and an entry called with the opened value), two types each
        @test count(p -> p.first === :dynamic, r.targets) == 4
    finally
    end
end
