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

@testset "BaseTraits: a trait's name in a bound's parameters names an item position" begin
    C = Main.BTCells
    w = Dynamic{C.Cell}[Dynamic{C.Cell}(1), Dynamic{C.Cell}("a"), Dynamic{C.Cell}(3)]
    @test C.countnums(w) == 2 && C.countnums_i(w) == 2
end

@testset "BaseTraits: DynamicItems, a user's vector without a copy" begin
    C = Main.BTCells
    v = Any[1, "ab", 3, "c", 5]
    d = DynamicItems{C.Cell}(v)
    @test conforms(typeof(d), BT.MutableIndexable{TraitWorld.Kept{C.Cell}})       # items of a Vector{Any} may carry `Compiled`
    @test C.countnums(d) == 3 && C.countnums_i(d) == 3
    @test d[2] isa TraitWorld.Kept{C.Cell} && !getfield(d[2], :compiled) && C.weight(d[2]) == 2   # a plain item: Dynamic
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
    # a copy through the view: each item kept with its attribute, `Dynamic` for plain items
    w = collect(DynamicItems{C.Cell}(Any[1, "a"]))
    @test w isa Vector{TraitWorld.Kept{C.Cell}} && all(x -> !getfield(x, :compiled), w) && C.countnums(w) == 1
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
    # measured in typed code: Julia's `@allocated f(x)` calls through `Base.allocated(f, x)`, a dispatch
    # at run time, where the value is `Dynamic` (traits reference §6.6)
    allocs(f::F, x::X) where {F,X} = (b0 = Base.gc_bytes(); f(x); Base.gc_bytes() - b0)
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

# The crossing (traits reference §10.3): a function bounded with dynamic items takes the user's
# container itself; its entry translates it by its bound into the view.
toplevel(quote
    @trait_module module BTCross
    using TraitWorld
    using ..BTCells: Cell, isnum, weight
    export countc, keepc!, valsc, lookc, which_one, firstc, sumw
    countc(xs::Iterable{Cell}) = (n = 0; for c in xs; n += isnum(c); end; n)
    keepc!(xs::(MutableIndexable{Cell}, Resizable)) = retain!(isnum, xs)
    valsc(d::Iterable{Pair{String, Cell}}) = (n = 0; for (k, c) in d; n += isnum(c); end; n)
    lookc(d::Keyed{String, Cell}, k::String) = weight(d[k])
    which_one(xs::Iterable{Int}) = :ints                  # a container meeting a bound as it is never crosses
    which_one(xs::Iterable{Cell}) = :cells
    function firstc(xs::Indexable{Cell})                   # reads item 1, then item 2
        a = weight(xs[1])
        b = weight(xs[2])
        return a + b
    end
    sumw(xs::Iterable{Cell}) = (s = 0; for c in xs; s += weight(c); end; s)
    end
    abstract type BTAbs end
    struct BTA <: BTAbs; n::Int; end
    BTCells.isnum(::BTA) = true
    BTCells.weight(a::BTA) = a.n
    @implement BTCells.Cell BTA
    cross_untyped(f, x) = f(x)                              # a caller that does not know the type
end)

@testset "BaseTraits: the crossing, a user's container taken directly" begin
    C = Main.BTCross
    v = Any[1, "ab", 3, "c", 5]
    @test C.countc(v) == 3                                   # Vector{Any}
    @test C.countc(Main.BTAbs[Main.BTA(1), Main.BTA(2)]) == 2    # an abstract element type
    @test C.countc([1, 2, 3]) == 3                           # a concrete element type that conforms
    @test C.countc(Union{Int,String}[1, "x"]) == 1           # a Union
    @test C.countc(Dynamic{Main.BTCells.Cell}[Dynamic{Main.BTCells.Cell}(1)]) == 1   # already dynamic items: as it is
    @test_throws TraitBoundError C.countc([1.5, 2.5])        # items that cannot conform: refused at the entry
    # writes reach the user's vector, which keeps the user's objects
    C.keepc!(v)
    @test v == Any[1, 3, 5]
    b = Main.BTBox(4)
    u = Any[b, "x"]
    C.keepc!(u)
    @test length(u) == 1 && u[1] === b
    # a Dict{String,Any}: its pairs, and keyed access
    dd = Dict{String, Any}("a" => 1, "b" => "xyz")
    @test C.valsc(dd) == 1 && C.lookc(dd, "b") == 3
    # bounds met as they are win
    @test C.which_one([1, 2]) === :ints && C.which_one(Any[1, "a"]) === :cells
    # an item that does not conform fails when it is read, after the items before it
    e = try C.firstc(Any[1, 2.5]); nothing catch err; err end
    @test e isa TraitBoundError && occursin("Float64", sprint(showerror, e))
    @test C.firstc(Any[1, "ab", 2.5]) == 3                   # never reads item 3
    # an untyped caller crosses too
    @test Base.invokelatest(Main.cross_untyped, C.sumw, Any[2, "abc"]) == 5
    @test Base.invokelatest(Main.cross_untyped, C.sumw, Any[2, "abc"]) == 5
    # once decided, a crossing container is not assembled as it is (under `all`, a Dict{String,Any}
    # fails the Iterable family's check, and its slow path cost 2.7 ms per call)
    big = Dict{String, Any}(string(i) => i for i in 1:1000)
    # measured in typed code: Julia's `@allocated f(x)` calls through `Base.allocated(f, x)`, a dispatch
    # at run time, where the value is `Dynamic` (traits reference §6.6)
    allocs(f::F, x::X) where {F,X} = (b0 = Base.gc_bytes(); f(x); Base.gc_bytes() - b0)
    allocs(C.valsc, big); allocs(C.valsc, big)
    @test allocs(C.valsc, big) < 1000
    # the explicit view still works, and costs the same path
    @test C.countc(DynamicItems{Main.BTCells.Cell}(Any[1, "a"])) == 1
end

toplevel(quote
    cross_main(args::Vector{String}) = (v = Any[1, "a", 2]; println(Core.stdout, BTCross.countc(v), " ", BTCross.lookc(Dict{String,Any}("k" => 3), "k")); 0)
    explicit_main(args::Vector{String}) = (v = Any[1, "a", 2]; println(Core.stdout, BTCross.countc(DynamicItems{BTCells.Cell}(v))); 0)
end)
# verify_main does not list a family member's workers yet (Base's containers and the views are
# family members; lowering L-11, L-14): the crossing adds no hole of its own beyond those
@testset "BaseTraits: verify_main and the crossing" begin
    @test Base.invokelatest(getglobal(Main, :cross_main), String[]) == 0
    holes(m) = filter(h -> !h.errorpath, Base.invokelatest(verify_main, getglobal(Main, m), (Vector{String},)).holes)
    cr = holes(:cross_main)
    @test !any(h -> h.callee in (TraitWorld.crossed, TraitWorld._satisfies, TraitWorld._cross_decide), cr)
    @test Set(h.kind for h in cr) ⊆ Set(h.kind for h in holes(:explicit_main))
end
