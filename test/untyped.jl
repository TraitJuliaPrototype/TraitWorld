# Calls from code that does not know the argument's type (untyped.jl, plan step 3 (c)): the entry
# compiled once at `Any` finds the implementation's builder in its position's table and makes one
# dynamic call to its method specialized on the builder, compiled once per key, not per type.
# Runs inside runtests.jl, or alone.
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module UTab
    using TraitWorld
    export Series, sfirst, ssum, scaled, Own, oval
    @trait Series begin
        @const data::Vector{Float64}
    end
    sfirst(s::Series) = s.data[1]
    ssum(s::Series, k::Int) = k * sum(s.data)
    scaled(s::Series, k) = k .* s.data                    # an untyped ordinary argument
    @trait Own begin
        oval(o::Own)::Float64
    end
    otwice(o::Own) = 2 * oval(o)
    end
end)
toplevel(quote
    struct UA; name::String; data::Vector{Float64}; end        # immutable, forwarding
    mutable struct UB; n::Int; data::Vector{Float64}; end      # mutable, same key
    struct UC; a::Int; data::Vector{Float64}; b::Int; end      # another offset, same key
    @implement UTab.Series UA
    @implement UTab.Series UB
    @implement UTab.Series UC
    struct OV; v::Float64; end                                 # its own receiver (a key of its own)
    UTab.oval(o::OV) = o.v
    @implement UTab.Own OV
end)

"The specializations of the entry methods specialized on builders (the table path), by method."
companions(f) = [mi for (g, n, tag, tpos) in UTab.__tw_untyped__ if g === f for m in methods(tag) for mi in Base.specializations(m) if mi isa Core.MethodInstance]

@testset "untyped calls: the table of declared implementations" begin
    xs = Any[UA("a", [1.0, 2.0]), UB(1, [3.0, 4.0]), UC(0, [5.0, 6.0], 9)]
    typed = [UTab.sfirst(xs[1]::UA), UTab.sfirst(xs[2]::UB), UTab.sfirst(xs[3]::UC)]
    # a loop, not a comprehension: `collect` infers its function at the first element's type
    untyped(v) = (r = Float64[]; for x in v; push!(r, UTab.sfirst(x)::Float64); end; r)
    @test untyped(xs) == typed == [1.0, 3.0, 5.0]
    @test [UTab.ssum(x, 2) for x in xs] == [6.0, 14.0, 22.0]
    @test [UTab.scaled(x, 2.0) for x in xs] == [[2.0, 4.0], [6.0, 8.0], [10.0, 12.0]]
    # three user types of one key: the specialized method is specialized once, on the builder
    @test count(mi -> isconcretetype(mi.specTypes.parameters[2]), companions(UTab.sfirst)) == 1
    # a mutable object's current value is read
    xs[2].data = [30.0]
    @test UTab.sfirst(xs[2]) == 30.0
    # a type that is its own receiver: its key, its method
    @test UTab.otwice(Any[OV(1.5)][1]) == 3.0
    # an implementation declared later is found; a type without one falls back as before
    toplevel(quote
        struct UD; data::Vector{Float64}; end
        @implement UTab.Series UD
    end)
    @test Base.invokelatest(untyped, Any[Main.UD([7.0])]) == [7.0]
    # reached only by untyped calls: no entry for the type, and the same specialized method
    entry = only(m for m in methods(UTab.sfirst) if TraitWorld._is_entry(m))
    @test !any(mi -> mi isa Core.MethodInstance && mi.specTypes.parameters[2] === Main.UD, collect(Base.specializations(entry)))
    @test count(mi -> isconcretetype(mi.specTypes.parameters[2]), companions(UTab.sfirst)) == 1
    @test_throws MethodError untyped(Any[42])
end
