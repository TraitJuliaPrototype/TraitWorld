# Calls from code that does not know the argument's type: the value is `Dynamic` (traits reference
# §6.6), and the entry compiled once at `Any` calls the worker at the erased key, compiled once for
# every type (lowering §9.2). A value the caller converts with `compiled_for` takes the table of
# declared implementations (untyped.jl): one lookup by its type, then the code for its key.
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

"The specializations of `f`'s workers at the erased key (a `Dynamic` trait object)."
erased_workers(f) = [mi for m in methods(f) if TraitWorld._isworker(m) for mi in Base.specializations(m)
                     if mi isa Core.MethodInstance && mi.specTypes isa DataType && any(T -> T isa DataType && T <: TObj && TraitWorld._is_erased(T.parameters[2]),
                                                          mi.specTypes.parameters[2:end])]

@testset "untyped calls: Dynamic, the worker at the erased key" begin
    xs = Any[UA("a", [1.0, 2.0]), UB(1, [3.0, 4.0]), UC(0, [5.0, 6.0], 9)]
    typed = [UTab.sfirst(xs[1]::UA), UTab.sfirst(xs[2]::UB), UTab.sfirst(xs[3]::UC)]
    # a loop, not a comprehension: `collect` infers its function at the first element's type
    untyped(v) = (r = Float64[]; for x in v; push!(r, UTab.sfirst(x)::Float64); end; r)
    @test untyped(xs) == typed == [1.0, 3.0, 5.0]
    @test [UTab.ssum(x, 2) for x in xs] == [6.0, 14.0, 22.0]
    @test [UTab.scaled(x, 2.0) for x in xs] == [[2.0, 4.0], [6.0, 8.0], [10.0, 12.0]]
    # three user types: the worker is compiled once, at the erased key
    @test length(erased_workers(UTab.sfirst)) == 1
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
    # reached only by untyped calls: no entry for the type, and the same worker
    entry = only(m for m in methods(UTab.sfirst) if TraitWorld._is_entry(m))
    @test !any(mi -> mi isa Core.MethodInstance && mi.specTypes.parameters[2] === Main.UD, collect(Base.specializations(entry)))
    @test length(erased_workers(UTab.sfirst)) == 1
    @test_throws MethodError untyped(Any[42])
end

@testset "untyped calls of Compiled values: the table" begin
    xs = Any[UA("a", [1.0, 2.0]), UB(1, [3.0, 4.0]), UC(0, [5.0, 6.0], 9), OV(2.5)]
    cf(v) = (r = Float64[]; for x in v[1:3]; push!(r, UTab.sfirst(compiled_for(x))::Float64); end; r)
    @test cf(xs) == [1.0, 3.0, 5.0]
    @test UTab.otwice(compiled_for(xs[4])) == 5.0
    @test UTab.ssum(compiled_for(xs[1]), 2) == 6.0
    # served by the table: a pointer entry per type
    ptypes(f) = [e.T for e in (@atomic TraitWorld._ptable(only(t for (g, n, t, p) in UTab.__tw_untyped__ if g === f)).entries)]
    @test issubset([UA, UB, UC], ptypes(UTab.sfirst))
    @test OV in ptypes(UTab.otwice)
    # a type without an implementation: the entry's own path, as plain Julia
    @test_throws MethodError UTab.sfirst(compiled_for(Any[42][1]))
end

# The table's worlds and the implementations it does not serve: a redefined operation, a type
# declared after a call (an older world must not see it), a family member, a generic implementation.
toplevel(quote
    @trait_module module UTab2
    using TraitWorld
    export Val1, vtwice, Fam, fsum, Gen, gfirst
    @trait Val1 begin
        val1(v::Val1)::Float64
    end
    vtwice(v::Val1) = 2 * val1(v)
    @trait Fam begin
        @const data::Vector{Float64}
    end
    fsum(f::Fam) = sum(f.data)
    @trait Gen{R} begin
        glen(r::R)::Int
    end
    @implement Gen{A} where {A <: AbstractVector} begin           # a generic implementation
        glen(r) = length(r)
    end
    gfirst(g::Gen) = glen(g)
    end
end)
toplevel(quote
    struct V1; x::Float64; end
    UTab2.val1(v::V1) = v.x
    @implement UTab2.Val1 V1
    struct FM{P}; data::Vector{Float64}; p::P; end
    @implement UTab2.Fam FM{P} where {P}                          # a family
end)

@testset "untyped calls: worlds, redefinitions, families, generic implementations" begin
    call1(v) = (r = Float64[]; for x in v; push!(r, UTab2.vtwice(x)::Float64); end; r)
    cfcall(v) = (r = Float64[]; for x in v; push!(r, UTab2.vtwice(compiled_for(x))::Float64); end; r)   # compiled_for through the table
    xs = Any[V1(1.5)]
    @test call1(xs) == [3.0]
    @test cfcall(xs) == [3.0]
    w = Base.get_world_counter()
    toplevel(:(UTab2.val1(v::V1) = 10 * v.x))                    # the operation redefined
    @test Base.invokelatest(call1, xs) == [30.0]
    @test Base.invoke_in_world(w, call1, xs) == [3.0]               # the older world: the old method
    @test Base.invokelatest(cfcall, xs) == [30.0]
    @test Base.invoke_in_world(w, cfcall, xs) == [3.0]
    # a type declared after the site was used: the older world has no implementation for it
    toplevel(quote
        struct V2; x::Float64; end
        UTab2.val1(v::V2) = v.x + 1
    end)
    w2 = Base.get_world_counter()
    toplevel(:(@implement UTab2.Val1 V2))
    ys = Any[Base.invokelatest(getglobal(Main, :V2), 1.0)]
    @test Base.invokelatest(call1, ys) == [4.0]
    @test_throws MethodError Base.invoke_in_world(w2, call1, ys)    # as plain Julia: no method there
    # a family member and a generic implementation, called untyped: the entry's own path
    callf(v) = (r = Float64[]; for x in v; push!(r, UTab2.fsum(x)::Float64); end; r)
    @test callf(Any[FM([1.0, 2.0], :a), FM([3.0], 1)]) == [3.0, 3.0]
    callg(v) = (r = Int[]; for x in v; push!(r, UTab2.gfirst(x)::Int); end; r)
    @test callg(Any[[1, 2, 3], [1.0]]) == [3, 1]
end
