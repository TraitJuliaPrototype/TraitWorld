# The runtime as methods (explorations/keys-plan.md §6): conformances are methods, entries
# are ordinary inlined methods, workers are compiled per key. Also the parts of the keys design
# that came with it: no implementing type when defaults serve every operation, overrides refused
# after a conformance, fields that define parameters by matching, immutable user types held.
# Runs inside runtests.jl, or alone.
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module RT
    using TraitWorld
    export RTable, rncols, rcol, rtotal, Sampled, mean_data, rmean, rfirst, Series2, nel, rsum2

    @trait RTable begin
        rncols(t::RTable)::Int
        rcol(t::RTable, i::Int)::Vector{Float64}
    end
    @implement RTable Vector{Vector{Float64}} begin
        rncols(t) = length(t)
        rcol(t, i) = t[i]
    end
    rtotal(t::RTable, len::Int) = (s = 0.0; for i in 1:rncols(t), j in 1:len; s += rcol(t, i)[j]; end; s)

    # a record-like trait: a field whose type defines T by matching, and a default over it
    @trait Sampled{T} begin
        @const data::Vector{T}
        mean_data(s::Sampled)::T = sum(s.data) / length(s.data)
    end
    rmean(s::Sampled) = mean_data(s)
    rfirst(s::Sampled) = s.data[1]

    # a field mentioning two parameters
    @trait Series2{K, V} begin
        @const pairs::Dict{K, V}
        nel(s::Series2)::Int = length(s.pairs)
    end
    rsum2(s::Series2) = sum(values(s.pairs))
    rnel(s::Series2) = nel(s)
    end
end)

toplevel(quote
    import .RT: rncols, rcol, mean_data
    struct RMeas; label::String; data::Vector{Vector{Float64}}; end          # immutable, forwarding
    @implement RT.RTable RMeas
    mutable struct RMeasM; label::String; data::Vector{Vector{Float64}}; end  # mutable, forwarding
    @implement RT.RTable RMeasM
    struct ROwn; base::Vector{Float64}; n::Int; end                          # implements the operations
    rncols(r::ROwn) = r.n
    rcol(r::ROwn, i::Int) = r.base .* i
    @implement RT.RTable ROwn

    struct SampleA; name::String; data::Vector{Float64}; end                 # keeps the default
    @implement RT.Sampled SampleA
    mutable struct SampleB; data::Vector{Float64}; count::Int; end           # keeps the default, mutable
    @implement RT.Sampled SampleB
    struct Sorted; data::Vector{Float64}; end                                # overrides the default
    mean_data(s::Sorted) = s.data[(length(s.data) + 1) ÷ 2]
    @implement RT.Sampled Sorted
    struct SampleI; data::Vector{Int}; end
    @implement RT.Sampled SampleI
    struct PairsA; pairs::Dict{Symbol,Float64}; tag::Int; end
    @implement RT.Series2 PairsA
end)

"Bytes allocated by `f(x)` after a first call, measured inside a function."
alloc1(f, x) = (f(x); @allocated f(x))
"The trait object an entry builds for `x` at `f`'s first argument."
tobj(f, x, nargs) = TraitWorld.enter(TraitWorld.EntryPos{typeof(f),1,nargs}(), x)

@testset "runtime as methods: conformances, entries, keys" begin
    v = [[1.0, 2.0], [3.0, 4.0]]
    m, mm, o = RMeas("a", v), RMeasM("b", v), ROwn([1.0, 2.0], 2)
    @test RT.rtotal(v, 2) == RT.rtotal(m, 2) == RT.rtotal(mm, 2) == 10.0
    @test RT.rtotal(o, 2) == 9.0
    # conformances are methods: one per declared type, the fallback for the rest
    @test TraitWorld._has_conformance_method(RT.RTable, RMeas)
    @test TraitWorld._has_conformance_method(RT.RTable, Vector{Vector{Float64}})
    @test !TraitWorld._has_conformance_method(RT.RTable, Matrix{Float64})
    @test TraitWorld.conformance(TraitWorld.As{RT.RTable}(), [1.0]) === TraitWorld.NOTRAIT
    # one worker per key: an immutable and a mutable type forwarding to the same field type share it
    T1, T2, T3 = typeof(tobj(RT.rtotal, m, 2)), typeof(tobj(RT.rtotal, mm, 2)), typeof(tobj(RT.rtotal, v, 2))
    @test T1 === T2 === T3
    @test typeof(tobj(RT.rtotal, o, 2)) !== T1
    # an immutable type's parts are held, a mutable one is read through
    @test getfield(only(getfield(tobj(RT.rtotal, m, 2), :views)), :o) === nothing
    @test getfield(only(getfield(tobj(RT.rtotal, mm, 2), :views)), :o) === mm
    # a mutable object rebound after the trait object was made: reads see the current value
    t = tobj(RT.rtotal, mm, 2)
    mm.data = [[10.0, 10.0]]
    @test rcol(t, 1) == [10.0, 10.0]
    mm.data = v
    # typed callers: no allocation per call
    typed(x) = RT.rtotal(x, 2)
    @test alloc1(typed, m) == 0 && alloc1(typed, mm) == 0 && alloc1(typed, v) == 0   # (ROwn's `rcol` allocates its column)
end

@testset "a new conformance invalidates no entry" begin
    untyped(xs::Vector{Any}) = RT.rtotal(xs[1], 1)
    @test untyped(Any[RMeas("a", [[1.0]])]) == 1.0
    @test untyped(Any[ROwn([2.0], 1)]) == 2.0
    entry = only(m for m in methods(RT.rtotal) if TraitWorld._is_entry(m))
    mis = collect(Base.specializations(entry))
    @test !isempty(mis)
    valid(mi) = isdefined(mi, :cache) && mi.cache.max_world == typemax(UInt)
    before = [valid(mi) for mi in mis]
    mi_u = only(Base.specializations(only(methods(untyped))))
    @test valid(mi_u)
    toplevel(quote
        struct RNew; data::Vector{Vector{Float64}}; end
        @implement RT.RTable RNew
        struct RNew2; z::Int; data::Vector{Vector{Float64}}; end
        @implement RT.RTable RNew2
    end)
    @test [valid(mi) for mi in mis] == before
    @test valid(mi_u)
    @test untyped(Any[Main.RNew([[3.0]])]) == 3.0
end

@testset "no implementing type when defaults serve every operation" begin
    a, b, s = SampleA("x", [1.0, 2.0, 6.0]), SampleB([1.0, 2.0, 6.0], 0), Sorted([1.0, 2.0, 6.0])
    @test RT.rmean(a) == RT.rmean(b) == 3.0
    @test RT.rmean(s) == 2.0                                  # the override
    Ka = typeof(tobj(RT.rmean, a, 1)).parameters[2].parameters[1].parameters[3]
    Kb = typeof(tobj(RT.rmean, b, 1)).parameters[2].parameters[1].parameters[3]
    Ks = typeof(tobj(RT.rmean, s, 1)).parameters[2].parameters[1].parameters[3]
    @test Ka === Kb === TraitWorld.Key{Nothing,NamedTuple{(:data,),Tuple{Vector{Float64}}}}
    @test Ks === TraitWorld.Key{Sorted,NamedTuple{(:data,),Tuple{Vector{Float64}}}}
    @test typeof(tobj(RT.rmean, a, 1)) === typeof(tobj(RT.rmean, b, 1))   # one worker for both
    # the type printer, which patched Julia registers (stock Julia prints the machinery type)
    @test endswith(sprint(TraitWorld._show_tobj_type, typeof(tobj(RT.rmean, a, 1))), "Sampled{Float64} at data::Vector{Float64}")
end

@testset "fields define parameters by matching" begin
    @test RT.rfirst(SampleI([4, 5])) === 4
    K = typeof(tobj(RT.rfirst, SampleI([4]), 1)).parameters[2].parameters[1].parameters[1]
    @test K === RT.Sampled{Int,TraitWorld.Key{Nothing,NamedTuple{(:data,),Tuple{Vector{Int}}}}}
    @test RT.rsum2(PairsA(Dict(:a => 1.0, :b => 2.0), 0)) == 3.0
    @test RT.rnel(PairsA(Dict(:a => 1.0), 0)) == 1
    # a field whose type does not match the declared pattern is refused at the conformance
    e = try
        toplevel(quote
            struct BadSample; data::Matrix{Float64}; end
            @implement RT.Sampled BadSample
        end)
        nothing
    catch err
        err isa LoadError ? err.error : err
    end
    @test e isa ImplementError
    @test occursin("does not match", sprint(showerror, e))
end

@testset "an override after a conformance is refused" begin
    toplevel(quote
        struct LateS; data::Vector{Float64}; end
        @implement RT.Sampled LateS
    end)
    @test isempty(TraitWorld.check_overrides())
    if TraitWorld._HAS_DEF_HOOK[]
        # the patched runtime's definition hook: refused at the definition, never visible
        e = try toplevel(:(RT.mean_data(s::LateS) = 0.0)); nothing catch err; err end
        while e isa LoadError; e = e.error; end
        @test e isa ImplementError && occursin("mean_data", sprint(showerror, e))
        @test isempty(methods(RT.mean_data, Tuple{Main.LateS})) || all(m -> m.sig.parameters[2] !== Main.LateS, methods(RT.mean_data, Tuple{Main.LateS}))
        @test isempty(TraitWorld.check_overrides())
    else
        toplevel(:(RT.mean_data(s::LateS) = 0.0))                # plain Julia would now call this
        ps = TraitWorld.check_overrides()
        @test length(ps) == 1 && occursin("mean_data", ps[1]) && occursin("LateS", ps[1])
        @test_throws ImplementError TraitWorld._refuse_overrides()
        Base.delete_method(only(methods(RT.mean_data, Tuple{Main.LateS})))
        @test isempty(TraitWorld.check_overrides())
    end
end
