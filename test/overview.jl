# traits §1's overview, as written
using TraitWorld, Test

@trait Shape begin
    area(s::Shape)::Float64
    perimeter(s::Shape)::Float64
    describe(s::Shape)::String = "a shape of area $(area(s))"    # a default
end

struct Circle; r::Float64; end
area(c::Circle) = π * c.r^2
perimeter(c::Circle) = 2π * c.r
@implement Shape Circle

@testset "overview" begin
    @test Circle(1.0) isa Shape
    total(shapes::AbstractVector{<:Shape}) = sum(area, shapes; init = 0.0)
    @test total([Circle(1.0), Circle(2.0)]) ≈ 15.707963267948966
    @test describe(Circle(1.0)) == "a shape of area 3.141592653589793"
    d = Dynamic{Shape}(Circle(1.0))
    @test d isa Shape
    @test area(d) ≈ π
    @test describe(d) == "a shape of area 3.141592653589793"
    @test unwrap(d) === Circle(1.0)
    @test sprint(show, d; context = :module => @__MODULE__) == "Dynamic{Shape}(Circle(1.0))"
end
