# `operations(x)` (W-150): the operations available on a value or a type, grouped by trait, read from the contracts.
using TraitWorld, Test
# this file runs in a module named `operations` (runtests.jl), whose own name is bound to it: the function is
# written `TraitWorld.operations` here

# The small case whose printed form is asserted exactly is declared in Main, where the REPL is: names print as from Main.
const W150_SETUP = quote
    module W150Shapes
    using TraitWorld
    export Shape, area, perimeter, describe, ratio, Placed
    @trait Shape begin
        "The area of the shape."
        area(s::Shape)::Float64
        perimeter(s::Shape)::Float64
        describe(s::Shape)::String = "a shape of area $(area(s))"
    end
    ratio(s::Shape) = area(s) / perimeter(s)
    @trait Placed begin
        x::Float64
        @const y::Float64
    end
    end
    using .W150Shapes
    struct W150Circle; r::Float64; end
    W150Shapes.area(c::W150Circle) = π * c.r^2
    W150Shapes.perimeter(c::W150Circle) = 2π * c.r
    @implement Shape W150Circle
    w150radius(c::W150Circle) = c.r
end
Core.eval(Main, :(using TraitWorld))        # the case is declared in Main: the suite must not rest on what Main has loaded
Core.eval(Main, Expr(:toplevel, W150_SETUP.args...))
const Shape = Main.W150Shapes.Shape
const Placed = Main.W150Shapes.Placed
const Circle = Main.W150Circle

# in this test's module: a member of two traits with a default, a forwarding member, an intersection's method
mutable struct Sprite
    r::Float64
    x::Float64
    const y::Float64
end
@implement Placed Sprite
@implement Shape Sprite begin
    area(s) = s.r^2
    perimeter(s) = 4s.r
end
report(s::All{Shape, Placed}) = s.x
struct Tile
    label::String
    shape::Circle
end
@implement Shape Tile by shape
struct Plain; v::Int; end
plainop(p::Plain) = p.v

texts(ls) = [l.text for l in ls]
group(ops, X) = only(filter(g -> g.trait === X, ops.traits))
shown(ops) = sprint(show, MIME("text/plain"), ops)

# the forms of the machinery that no listing shows where the user wrote none (the messages' tool's forms)
machinery(s) = occursin("Tuple{typeof(", s) || occursin("var\"#", s) || occursin("##", s)

@testset "operations" begin
    @testset "a member: the contract, a default, a docstring, the methods at the trait, other" begin
        ops = TraitWorld.operations(Circle(1.0))
        @test ops isa TraitWorld.Operations
        @test ops.kind === :value && ops.type === Circle
        @test [g.trait for g in ops.traits] == Any[Shape]
        g = group(ops, Shape)
        @test texts(g.operations) == ["area(s::Shape)::Float64", "perimeter(s::Shape)::Float64", "describe(s::Shape)::String"]
        @test [l.note for l in g.operations] == ["", "", "a default"]
        @test g.operations[1].doc == "The area of the shape."
        @test texts(g.methods) == ["ratio(s::Shape)"]
        @test texts(ops.other) == ["w150radius(c::W150Circle)"]
        @test ops.more == 0
        @test TraitWorld.operations(Circle).traits[1].trait === Shape          # a type: as for its values
    end

    @testset "the printed form" begin
        @test shown(TraitWorld.operations(Circle(1.0))) == """
            W150Circle(1.0) is a W150Circle, a member of Shape

            Shape
              operations:
                area(s::Shape)::Float64      # The area of the shape.
                perimeter(s::Shape)::Float64
                describe(s::Shape)::String   # a default
              methods at Shape:
                ratio(s::Shape)

            other: methods at W150Circle
                w150radius(c::W150Circle)"""
        @test sprint(show, TraitWorld.operations(Circle(1.0))) == "Operations(W150Circle(1.0): 1 trait)"
    end

    @testset "a member of two traits, and of their intersection" begin
        ops = TraitWorld.operations(Sprite(1.0, 0.0, 0.0))
        @test [g.trait for g in ops.traits][1:2] == Any[Placed, Shape]       # by name
        @test texts(group(ops, Placed).fields) == ["x::Float64", "@const y::Float64"]
        alls = filter(g -> TraitWorld._is_all(g.trait), ops.traits)
        @test length(alls) == 1 && texts(alls[1].methods) == ["report(s::All{Placed, Shape})"]
        @test any(l -> l.note == "a default", group(ops, Shape).operations)
    end

    @testset "a forwarding member" begin
        ops = TraitWorld.operations(Tile("door", Circle(1.0)))
        g = group(ops, Shape)
        @test g.via == "by the field `shape`"
        @test length(g.operations) == 3
        @test isempty(ops.other)            # its forwarding methods serve the operations listed; the library's are not listed
    end

    @testset "a box and a wrapper" begin
        d = Dynamic{Shape}(Circle(1.0))
        ops = TraitWorld.operations(d)
        @test ops.kind === :box && ops.type === Circle
        @test occursin("only the operations and declared fields of Shape", ops.note)
        @test group(ops, Shape).reached
        s = shown(ops)
        @test startswith(s, "Dynamic{Shape}(W150Circle(1.0)) holds a W150Circle, a member of Shape")
        @test occursin("other: methods at W150Circle (through unwrap(x))", s)
        sp = TraitWorld.operations(Dynamic{Shape}(Sprite(1.0, 0.0, 0.0)))
        @test !group(sp, Placed).reached && group(sp, Shape).reached      # behind a box of Shape, Placed needs unwrap
        @test occursin("Placed (through unwrap(x))", shown(sp))
        w = TraitWorld.operations(compiled_for(Circle(1.0)))
        @test w.kind === :wrapper && w.type === Circle && occursin("unwrap(x)", w.note)
        bt = TraitWorld.operations(Dynamic{Shape})
        @test bt.kind === :boxtype && [g.trait for g in bt.traits] == Any[Shape]
    end

    @testset "a trait itself" begin
        ops = TraitWorld.operations(Shape)
        @test ops.istrait && ops.kind === :trait
        @test "W150Circle" in ops.members && any(endswith("Sprite"), ops.members) && any(endswith("Tile"), ops.members)
        @test texts(group(ops, Shape).operations)[1] == "area(s::Shape)::Float64"
        ix = TraitWorld.operations(Indexable)
        @test [g.trait for g in ix.traits] == Any[Indexable, HasLength]   # its supertrait's contract too
        @test "AbstractVector" in ix.members
        @test occursin("<: HasLength", shown(ix))
    end

    @testset "plain values: BaseTraits' memberships, or other only" begin
        f = TraitWorld.operations(1.5)
        @test [g.trait for g in f.traits] == Any[BoundedText]
        @test texts(f.traits[1].operations) == ["textbound(x::BoundedText)::Int"]
        @test f.traits[1].via == "as Number"
        @test length(f.other) == 12 && f.more > 0                       # the bound, with the count of the rest
        @test length(TraitWorld.operations(1.5; limit = 3).other) == 3
        v = TraitWorld.operations([1.0, 2.0])
        # BaseTraits' five (the suite's other files declare more memberships of `Vector`)
        @test issubset(Set(Any[HasLength, Iterable, Indexable, MutableIndexable, Resizable]),
                       Set(g.trait for g in v.traits if !TraitWorld._is_all(g.trait)))
        @test occursin("Indexable{T}, T = Float64", shown(v))
        p = TraitWorld.operations(Plain(1))
        @test isempty(p.traits) && texts(p.other) == ["plainop(p::$(Plain))"]     # a module prefix: Plain is not visible from Main
        @test startswith(shown(p), "$(Plain)(1) is a $(Plain), a member of no trait")
        s = TraitWorld.operations(sin)
        @test isempty(s.traits) && occursin("Callable", s.note)           # Callable only where asked
        @test TraitWorld.operations(Callable).istrait
    end

    @testset "no form of the machinery" begin
        for x in (Circle(1.0), Sprite(1.0, 0.0, 0.0), Tile("t", Circle(1.0)), Shape, 1.5, [1.0], Plain(1), sin)
            s = shown(TraitWorld.operations(x))
            @test !machinery(s)
            @test !occursin("Dynamic{", s)          # no box where the user wrote none
        end
    end

    @testset "the REPL key's word" begin
        @test TraitWorld._operations_word(Main, "W150Shapes.Shape").istrait
        @test TraitWorld._operations_word(@__MODULE__, "Shape").istrait
        @test_throws ArgumentError TraitWorld._operations_word(Main, "")
        @test_throws ArgumentError TraitWorld._operations_word(Main, "f(x)")        # no call is evaluated
        @test_throws ArgumentError TraitWorld._operations_word(Main, "no_such_name_w150")
        @test_throws ArgumentError TraitWorld.install_operations_key!(nothing)
    end

end
