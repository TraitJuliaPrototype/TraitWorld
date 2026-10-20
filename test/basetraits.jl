# BaseTraits (traits reference §18): collection traits for Base's containers, a user's containers
# seen with `Dynamic{X}` items without a copy, and the `Dynamic` that holds the user's object.
# Runs inside runtests.jl, or alone: julia --project=. test/basetraits.jl
using Test, TraitWorld
const BT = TraitWorld.BaseTraits      # (runtests.jl's Main has other traits of these names)
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module BTCells
    using TraitWorld
    export Cell, isnum, weight, countnums, countnums_i, keepnums!, countvals, lookup, sumints, firstnum
    @trait Cell begin
        isnum(c::Cell)::Bool
        weight(c::Cell)::Int
    end
    @implement Cell Int begin
        isnum(c) = true
        weight(c) = c
    end
    @implement Cell String begin
        isnum(c) = false
        weight(c) = length(c)
    end
    countnums(xs::Iterable{Cell}) = (n = 0; for c in xs; n += isnum(c); end; n)     # Iterable{Dynamic{Cell}}
    countnums_i(xs::Indexable{Cell}) = (n = 0; for i in 1:length(xs); n += isnum(xs[i]); end; n)
    keepnums!(xs::(MutableIndexable{Cell}, Resizable)) = retain!(isnum, xs)
    countvals(d::Iterable{Pair{String, Cell}}) = (n = 0; for (k, c) in d; n += isnum(c); end; n)
    lookup(d::Keyed{String, Cell}, k::String) = haskey(d, k) ? weight(d[k]) : -1
    sumints(xs::Iterable{Int}) = (s = 0; for x in xs; s += x; end; s)      # a Base container of a concrete item type
    function firstnum(xs::Iterable{Cell})                                   # stops at the first number
        for c in xs
            isnum(c) && return weight(c)
        end
        return -1
    end
    end
    using .BTCells

    mutable struct BTBox; n::Int; end
    BTCells.isnum(b::BTBox) = true
    BTCells.weight(b::BTBox) = b.n
    @implement BTCells.Cell BTBox

    # declaration order decides the first candidates of the split (E-130)
    @trait_module module BTOrder
    using TraitWorld
    export Tag, tag
    @trait Tag begin
        tag(t::Tag)::Int
    end
    struct O1 end; struct O2 end; struct O3 end; struct O4 end; struct O5 end; struct O6 end
    @implement Tag O1 begin tag(t) = 1 end
    @implement Tag O2 begin tag(t) = 2 end
    @implement Tag O3 begin tag(t) = 3 end
    @implement Tag O4 begin tag(t) = 4 end
    @implement Tag O5 begin tag(t) = 5 end
    @implement Tag O6 begin tag(t) = 6 end
    end
end)

@testset "BaseTraits: Base's containers conform by Base's methods" begin
    C = Main.BTCells
    @test C.sumints([1, 2, 3]) == 6
    @test C.sumints(1:4) == 10                                 # an AbstractArray
    @test conforms(Vector{Int}, BT.Iterable{Int}) && !conforms(Vector{Int}, BT.Iterable{Float64})
    @test conforms(Dict{String, Int}, BT.Keyed{String, Int})
    @test conforms(Vector{Dynamic{C.Cell}}, BT.MutableIndexable{Dynamic{C.Cell}})
    @test !conforms(Vector{Any}, BT.Iterable{Dynamic{C.Cell}})      # a Vector{Any} crosses through a view
end

@testset "BaseTraits: a trait's name in a bound's parameters means its Dynamic" begin
    C = Main.BTCells
    w = Dynamic{C.Cell}[Dynamic{C.Cell}(1), Dynamic{C.Cell}("a"), Dynamic{C.Cell}(3)]
    @test C.countnums(w) == 2 && C.countnums_i(w) == 2
end

@testset "BaseTraits: DynamicItems, a user's vector without a copy" begin
    C = Main.BTCells
    v = Any[1, "ab", 3, "c", 5]
    d = DynamicItems{C.Cell}(v)
    @test conforms(typeof(d), BT.MutableIndexable{Dynamic{C.Cell}})
    @test C.countnums(d) == 3 && C.countnums_i(d) == 3
    @test d[2] isa Dynamic{C.Cell} && C.weight(d[2]) == 2
    # writes reach the user's vector, which holds the user's objects, not dynamic values
    C.keepnums!(d)
    @test v == Any[1, 3, 5] && all(x -> x isa Int, v)
    b = Main.BTBox(7)
    u = Any[b, "x", b]
    C.keepnums!(DynamicItems{C.Cell}(u))
    @test length(u) == 2 && u[1] === b && u[2] === b             # the same object, not a copy
    # a dynamic value holds the user's object: one made from the value and one made in trait code are equal
    @test TraitWorld._dyn_object(Dynamic{C.Cell}(b)) === b
    @test Dynamic{C.Cell}(b) == Dynamic{C.Cell}(b) && hash(Dynamic{C.Cell}(b)) == hash(Dynamic{C.Cell}(b))
    b.n = 9
    @test C.weight(Dynamic{C.Cell}(b)) == 9                      # it sees the user's field rebound
    # an item that does not conform fails when it is read, after the items before it
    bad = Any[1, 2.5, 3]
    @test C.firstnum(DynamicItems{C.Cell}(bad)) == 1             # never reaches the Float64
    @test_throws TraitBoundError C.countnums(DynamicItems{C.Cell}(bad))
    # a copy into Vector{Dynamic{X}} through the view
    w = collect(DynamicItems{C.Cell}(Any[1, "a"]))
    @test w isa Vector{Dynamic{C.Cell}} && C.countnums(w) == 1
end

@testset "BaseTraits: DynamicValues, a user's Dict{String,Any}" begin
    C = Main.BTCells
    dd = Dict{String, Any}("a" => 1, "b" => "xyz", "c" => 3)
    dv = DynamicValues{C.Cell}(dd)
    @test C.countvals(dv) == 2
    @test C.lookup(dv, "b") == 3 && C.lookup(dv, "zz") == -1
    @test C.countvals(Dict{String, Dynamic{C.Cell}}(k => Dynamic{C.Cell}(v) for (k, v) in dd)) == 2
end

@testset "Dynamic: made from a value of unknown type without a search or a copy" begin
    C = Main.BTCells
    v = Any[i for i in 1:200]
    d = DynamicItems{C.Cell}(v)
    allocs(f, x) = @allocated f(x)
    allocs(C.countnums, d); allocs(C.countnums, d)
    @test allocs(C.countnums, d) < 200                           # no allocation per item read (200 items)
    F = TraitWorld._family(C.Cell)
    @test TraitWorld._cand_flag(F, Int)[] == TraitWorld._SESSION[]   # registered once, by a flag
    @test Int in Base.Compiler.dynamic_candidates(F)            # the user's type is the candidate
end

@testset "Dynamic: the first candidates are the first declared" begin
    O = Main.BTOrder
    F = TraitWorld._family(O.Tag)
    @test Base.Compiler.dynamic_candidates(F) == Any[O.O1, O.O2, O.O3, O.O4]
    @test sum(O.tag(Dynamic{O.Tag}(x)) for x in (O.O1(), O.O5(), O.O6())) == 12   # beyond the split: the fallback
end
