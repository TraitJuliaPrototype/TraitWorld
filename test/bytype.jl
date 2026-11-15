# Values carry, by type (W-151; the review of 2026-11-15, P1 as accepted; open issue 186): the two kept forms, the
# box `Dynamic{X}` and the wrapper `Compiled` that `compiled_for(x)` returns; a trait's default as methods made where
# a method is defined (W-160: the method at the kept forms, a forwarder that boxes a plain member); `convert` into storage typed
# `Dynamic{X}`; the definition-time check as a reading of the method at the box (D-3).
using Test, TraitWorld
using TraitWorld.ByType: compiled_for

module BT
using TraitWorld
@trait_module first_seen = false
@trait Shape begin
    @default_dynamic
    area(s::Shape)::Float64
    describe(s::Shape)::String = "a shape of area $(area(s))"
end
@trait Named begin                                   # no default: Julia's rule
    name(s::Named)::String
end
@trait Col{T} begin
    @default_dynamic
    cget(c::Col{T}, i::Int)::T
end
mutable struct Circle; r::Float64; end
area(c::Circle) = 3.0 * c.r^2
name(c::Circle) = "circle"
@implement Shape Circle
@implement Named Circle
struct Sq; a::Float64; end
area(s::Sq) = s.a^2
@implement Shape Sq
struct FC; v::Vector{Float64}; end
cget(c::FC, i::Int) = c.v[i]
@implement Col{Float64} FC

form(x) = x isa Dynamic ? :box : x isa Compiled ? :wrapper : :plain
kind(s::Shape) = form(s)
total(s::Shape, k::Int = 2) = k * area(s)
scaled(s::Shape; by = 1.0) = by * area(s)
typed(s::C) where {C <: Shape} = C
pair(a::Shape, b::Shape) = (form(a), form(b))
first2(c::Col{T}) where {T} = (form(c), cget(c, 1))
bare(c::Col) = form(c)                               # a parametric trait written bare: boxed at the member's instance
bare2(c::Col{<:Real}) = form(c)                      # with a parameter left open, the same
anyf(f::Callable, x) = (form(f), f(x))               # an input left open (Callable's): the plain member as it is
plainkind(n::Named) = form(n)                        # a trait without the default
apply(f::Callable{Tuple{Float64}, Float64}, x::Float64) = (form(f), f(x))
struct Prob{S <: Shape}; s::S; end                   # Julia's default outer constructor forwards too
struct Scene; items::Vector{Dynamic{Shape}}; end
struct Holder; s::Dynamic{Shape}; end
end
using .BT: Circle, Sq, FC, Shape, Named

@testset "the wrapper" begin
    c = Circle(1.0)
    w = compiled_for(c)
    @test w isa Compiled{Circle} && unwrap(w) === c
    @test w isa Shape && w isa Named                 # a member of every trait its object is in
    @test !(Dynamic{Shape}(c) isa Named)             # the box: of its trait only
    @test BT.area(w) == 3.0 && BT.name(w) == "circle" && BT.describe(w) == "a shape of area 3.0"
    @test w.r == 1.0
    w.r = 2.0
    @test c.r == 2.0                                 # the object's field, written through the wrapper
    @test compiled_for(w) === w && compiled_for(Dynamic{Shape}(c)) === w
    @test Dynamic{Shape}(w) == Dynamic{Shape}(c) && unwrap(Dynamic{Shape}(w)) === c   # a box of the wrapper holds the object
    @test sprint(show, compiled_for(Sq(1.0))) == "Compiled($(sprint(show, Sq(1.0))))"
    @test compiled_for(sin)(0.5) == sin(0.5) && compiled_for(sin) isa Callable{Tuple{Float64}, Float64}
end

@testset "the trait's default as generated methods" begin
    c = Circle(1.0)
    @test BT.kind(c) === :box && BT.kind(compiled_for(c)) === :wrapper && BT.kind(Dynamic{Shape}(c)) === :box
    @test BT.total(c) == 6.0 && BT.total(c, 3) == 9.0 && BT.total(compiled_for(c)) == 6.0
    @test BT.scaled(c; by = 2.0) == 6.0 && BT.scaled(compiled_for(c)) == 3.0
    @test BT.typed(c) === Dynamic{Shape} && BT.typed(compiled_for(c)) === Compiled{Circle}
    @test BT.pair(c, compiled_for(Sq(1.0))) === (:box, :wrapper) && BT.pair(c, c) === (:box, :box)
    @test BT.first2(FC([4.0])) === (:box, 4.0) && BT.first2(compiled_for(FC([4.0]))) === (:wrapper, 4.0)
    @test BT.bare(FC([1.0])) === :box && BT.bare2(FC([1.0])) === :box       # boxed at Col{Float64} (open issue 204)
    @test BT.bare(compiled_for(FC([1.0]))) === :wrapper
    @test BT.anyf(sin, 0.0) === (:plain, 0.0)                               # Callable's inputs: no forwarder
    @test BT.plainkind(c) === :plain && BT.plainkind(compiled_for(c)) === :wrapper
    @test BT.apply(x -> 2x, 1.5) === (:box, 3.0) && BT.apply(compiled_for(x -> 2x), 1.5) === (:wrapper, 3.0)
    # one forwarder per arity that holds the trait argument; the method at the kept forms, documented
    fw = [m for m in methods(BT.total) if TraitWorld._is_forwarder(m)]
    @test length(fw) == 2 && length(methods(BT.total)) == 4
    @test isempty([m for m in methods(BT.plainkind) if TraitWorld._is_forwarder(m)])
    # the forwarder is compiled once where the trait's parameters are fixed, per member type where only the member fixes them
    @test only(m for m in methods(BT.kind) if TraitWorld._is_forwarder(m)).nospecialize != 0
    @test only(m for m in methods(BT.first2) if TraitWorld._is_forwarder(m)).nospecialize == 0
    # a struct whose parameter is bounded by the trait: its default outer constructor boxes; its own constructor does not
    @test BT.Prob(c) isa BT.Prob{Dynamic{Shape}} && BT.Prob(compiled_for(c)) isa BT.Prob{Compiled{Circle}}
    @test BT.Prob{Circle}(c) isa BT.Prob{Circle}
    @test erases(Shape) && !erases(Named) && erases(Callable{Tuple{Int}, Int}) && erases(All{Shape, Named}) && !erases(Int)
    @test isempty(detect_ambiguities(BT))
end

@testset "storage typed by the box" begin
    sc = BT.Scene(Dynamic{Shape}[])
    push!(sc.items, Circle(1.0)); push!(sc.items, compiled_for(Sq(2.0))); push!(sc.items, Dynamic{Shape}(Sq(1.0)))
    @test all(x -> x isa Dynamic{Shape}, sc.items) && unwrap(sc.items[2]) === Sq(2.0)   # a wrapper's choice erased there
    @test BT.Holder(Circle(1.0)).s isa Dynamic{Shape}
    @test convert(Dynamic{Shape}, Dynamic{Shape}(Sq(1.0))) === Dynamic{Shape}(Sq(1.0))
    @test_throws TypeError convert(Dynamic{Shape}, 1.0)
end

@testset "the check reads the method at the box" begin
    @test isempty(check_definitions(BT))
    M = Module(:BTMistakes)
    code = quote
        using TraitWorld
        @trait_module bounded = false first_seen = false
        @trait T2 begin
            @default_dynamic
            n2(t::T2)::Int
        end
        helper(x) = length(x)
        good(t::T2) = n2(t) + 1
        spread(t::T2) = size(t)
        through(t::T2) = helper(t)
        field(t::T2) = t.data
        leak(t::T2) = typeof(t)
    end
    Core.eval(M, Expr(:toplevel, code.args...))      # each statement expanded after the one before it is evaluated
    ps = check_definitions(M)
    @test length(ps) == 3
    for (name, what) in (("spread", "size("), ("through", "reaches length("), ("field", "the field `data`"))
        m = only(m for m in methods(getglobal(M, Symbol(name))) if TraitWorld._at_box_checked(m))
        @test any(p -> startswith(p, name) && occursin(":$(m.line):", p) && occursin(what, p), ps)
    end
end
