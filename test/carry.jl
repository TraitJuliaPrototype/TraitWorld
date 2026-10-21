# Values carry their attribute through storage (traits reference §6.6, §10, §10.3, §10.4): a value's
# `Compiled` or `Dynamic` is set where a plain value first meets a trait and kept through calls,
# bounds and storage; only `compiled_for` and `with_dynamic` change it; constructors and types never
# cast. A trait's name in storage is `Kept{X}`; a struct parameter bounded by a trait keeps the value
# itself (`Compiled`) or a `Dynamic{X}`.
# Runs inside runtests.jl, or alone: julia --project=. test/carry.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module Carry
    using TraitWorld
    export Shape, area, kind, kinds, kinds_c, kinds_d, Bag, keep!, bagkinds, recast!, Holder, ShapeBox, boxit, applyh, boxkind
    @trait Shape begin
        area(s::Shape)::Float64
    end
    kind(s::Shape) = TraitWorld.is_dynamic(s) ? :dynamic : :compiled
    kinds(ms::Iterable{Shape}) = (r = Symbol[]; for m in ms; push!(r, kind(m)); end; r)
    kinds_c(ms::Iterable{Compiled{Shape}}) = (r = Symbol[]; for m in ms; push!(r, kind(m)); end; r)
    kinds_d(ms::Iterable{Dynamic{Shape}}) = (r = Symbol[]; for m in ms; push!(r, kind(m)); end; r)
    mutable struct Bag
        items::Vector{Shape}                 # Kept{Shape}: each value with its attribute
        last::Dynamic{Shape}                 # an attribute in storage is a default only: Kept{Shape} too
    end
    keep!(b::Bag, s::Shape) = (push!(b.items, s); b.last = s; nothing)
    bagkinds(b::Bag) = (r = Symbol[]; for m in b.items; push!(r, kind(m)); end; r)
    recast!(xs::MutableIndexable{Shape}) = (xs[1] = compiled_for(xs[1]); nothing)   # a library's cast, written back
    struct Holder{T, F <: Callable{Tuple{T}, T}}       # a parameter bounded by a trait: the field keeps the value itself or its Dynamic
        f::F
        x::T
    end
    applyh(h::Holder) = h.f(h.x)
    struct ShapeBox{S <: Shape}
        s::S
    end
    boxit(s::Shape) = ShapeBox(s)                      # from trait code: the trait object kept by its key
    boxkind(b::ShapeBox) = kind(b.s)
    end
end)
toplevel(quote
    abstract type AbsShape end
    struct CHex <: AbsShape; a::Float64; end
    struct CSq <: AbsShape; a::Float64; end
    Carry.area(h::CHex) = h.a
    Carry.area(s::CSq) = s.a^2
    @implement Carry.Shape CHex
    @implement Carry.Shape CSq
end)

@testset "values carry: items of a Vector{Any} keep their attribute (the bug of 2026-10-21)" begin
    C = Main.Carry; S = C.Shape; h = Main.CHex(1.0)
    v = Any[Dynamic{S}(h), Compiled{S}(h), compiled_for(h), with_dynamic(h), h]
    @test C.kinds(v) == [:dynamic, :compiled, :compiled, :dynamic, :dynamic]      # plain item: Dynamic (abstract item type)
    @test C.kinds_c(v) == [:dynamic, :compiled, :compiled, :dynamic, :compiled]   # the position's attribute decides plain items only
    @test C.kinds_d(v) == [:dynamic, :compiled, :compiled, :dynamic, :dynamic]
    @test C.kinds([h]) == [:compiled] && C.kinds_d([h]) == [:dynamic]            # a concrete item type, as before
    allocs(f::F, x::X) where {F,X} = (b0 = Base.gc_bytes(); f(x); Base.gc_bytes() - b0)
    w = Any[Main.CSq(1.0) for _ in 1:200]
    d = DynamicItems{S}(w)
    nread(xs::DynamicItems) = (n = 0; for x in xs; n += x isa Kept; end; n)
    nread(d); nread(d)
    @test allocs(nread, d) == 0                                                   # a Kept{X} per read, inline
end

@testset "values carry: storage keeps each value's attribute" begin
    C = Main.Carry; S = C.Shape; h = Main.CHex(1.0)
    b = C.Bag(Kept{S}[], Kept{S}(Dynamic{S}(h)))
    @test fieldtype(C.Bag, :items) === Vector{Kept{S}} && fieldtype(C.Bag, :last) === Kept{S}
    typed(b, x::Main.CHex) = Main.Carry.keep!(b, x)           # a caller that knows the type: Compiled
    C.keep!(b, h)                                             # at the prompt: Dynamic
    typed(b, h)
    C.keep!(b, compiled_for(h)); C.keep!(b, with_dynamic(h))
    C.keep!(b, Compiled{S}(h)); C.keep!(b, Dynamic{S}(h))
    @test C.bagkinds(b) == [:dynamic, :compiled, :compiled, :dynamic, :compiled, :dynamic]
    @test getfield(b.last, :compiled) === false
    @test sprint(show, b.items[2]) == "Kept{$(S)}: Compiled at $(Main.CHex)"
end

@testset "values carry: casts, constructors, equality" begin
    S = Main.Carry.Shape; h = Main.CHex(2.0)
    d = Dynamic{S}(h); c = Compiled{S}(h); k = Kept{S}(d)
    @test compiled_for(d) isa Compiled{S} && with_dynamic(c) isa Dynamic{S}
    @test getfield(compiled_for(k), :compiled) && !getfield(with_dynamic(Kept{S}(c)), :compiled)
    @test compiled_for(c) === c && with_dynamic(d) === d
    @test_throws TraitBoundError Dynamic{S}(c)                # constructors never cast
    @test_throws TraitBoundError Compiled{S}(d)
    @test_throws TraitBoundError Dynamic{S}(Kept{S}(c))
    @test getfield(Kept{S}(h), :compiled)                     # a plain value: the trait's default, Compiled
    @test d == c == k && hash(d) == hash(c) == hash(k)        # one object, whatever its attribute
    @test Main.Carry.area(c) == Main.Carry.area(d) == Main.Carry.area(k) == 2.0
    @test !(Kept{S}(h) === Kept{S}(d))                        # `===` differs by attribute
end

@testset "values carry: a write stores what reads back the same" begin
    C = Main.Carry; S = C.Shape; h = Main.CHex(1.0)
    v = Any[h, Main.CSq(2.0)]
    C.recast!(v)                                              # a library's cast, written to a Vector{Any}
    @test v[1] isa TraitWorld.CompiledFor && C.kinds(v) == [:compiled, :dynamic]
    a = AbsShape[h, Main.CSq(2.0)]
    @test_throws TraitBoundError C.recast!(a)                 # a Vector{AbsShape} cannot hold the cast: types never cast
    @test a[1] === h
    r = Any[compiled_for(h), Main.CSq(2.0), 3.0]
    @test_throws TraitBoundError C.kinds(r)                   # an item that does not conform, when read
end

@testset "values carry: a struct parameter bounded by a trait" begin
    C = Main.Carry; S = C.Shape; h = Main.CHex(3.0)
    sq(x) = x^2
    @test typeof(C.Holder(sq, 2.0)).parameters[2] === Dynamic{Callable{Tuple{Float64}, Float64}}   # Callable's default
    @test typeof(C.Holder(compiled_for(sq), 2.0)).parameters[2] === typeof(sq)                      # the function itself
    @test typeof(C.Holder(with_dynamic(sq), 2.0)).parameters[2] <: Dynamic
    @test C.applyh(C.Holder(sq, 2.0)) == C.applyh(C.Holder(compiled_for(sq), 2.0)) == 4.0
    @test typeof(C.ShapeBox(h)).parameters[1] <: Dynamic                   # at the prompt: Dynamic
    tbox(x::Main.CHex) = Main.Carry.ShapeBox(x)
    @test typeof(tbox(h)).parameters[1] === Main.CHex                     # a caller that knows the type: the value itself
    @test typeof(C.ShapeBox(compiled_for(h))).parameters[1] === Main.CHex
    @test typeof(C.ShapeBox(Compiled{S}(h))).parameters[1] === Main.CHex  # opened by its type
    @test typeof(C.ShapeBox(with_dynamic(h))).parameters[1] <: Dynamic
    tboxit(x::Main.CHex) = Main.Carry.boxit(x)
    @test typeof(tboxit(h)).parameters[1] === Main.CHex                   # from trait code: the trait object by its key
    @test typeof(C.boxit(h)).parameters[1] <: Dynamic
    @test C.boxkind(tboxit(h)) === :compiled && C.boxkind(C.boxit(h)) === :dynamic
    err = try
        toplevel(quote
            @trait_module module CarryBad
            using TraitWorld, ..Carry
            struct Two{F <: Carry.Shape}
                a::F
                b::F
            end
            end
        end)
        nothing
    catch e
        e
    end
    @test err isa LoadError                                              # a bounded parameter types one field
end
