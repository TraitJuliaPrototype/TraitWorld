# The trait syntax of the keys design (note "Declaring a trait", "How a type conforms"):
# operations declared at the trait, `Self` for the implementing type, every header parameter
# an associated type, a field that defines its parameter, implementations for a type, `by`
# forwarding, families with `where`. Lowered to TraitWorld's internal form; keys over several
# fields come in the next phase. Runs inside runtests.jl, or alone.
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module KCols
    using TraitWorld
    export KTable, kncols, kcol, kwith, kmean, kscaled, KVec, klen, kget, ksum, KInteg, kadvance

    @trait KTable begin                                      # the overview's ColTable, in the design's syntax
        kncols(t::KTable)::Int
        kcol(t::KTable, i::Int)::Vector{Float64}
        kwith(t::KTable, cs::Vector{Vector{Float64}})::Self  # a constructor operation
    end
    @implement KTable Vector{Vector{Float64}} begin           # an implementation for a type
        kncols(t) = length(t)
        kcol(t, i) = t[i]
        kwith(t, cs) = cs
    end
    kmean(t::KTable, i::Int) = (c = kcol(t, i); sum(c) / length(c))
    kscaled(t::KTable, a::Float64)::Like{t} = kwith(t, [a .* kcol(t, i) for i in 1:kncols(t)])

    @trait KVec{T} begin                                      # an associated type defined by an equation
        T = eltype(Self)
        klen(v::KVec)::Int
        kget(v::KVec{T}, i::Int)::T
    end
    @implement KVec A where {A <: Vector{<:Real}} begin      # a family; T from the trait's equation
        klen(v) = length(v)
        kget(v, i) = v[i]
    end
    ksum(v::KVec) = (s = zero(kget(v, 1)); for i in 1:klen(v); s += kget(v, i); end; s)

    @trait KInteg{U, P} begin                                 # fields only; their types define U and P
        u::U
        @const p::P
        t::Float64
    end
    kadvance(i::KInteg, dt::Float64) = (i.t = i.t + dt; i.t)
    knorm(i::KInteg) = (s = 0.0; for x in i.u; s += x * x; end; s * i.p[1])   # reads only
    end
end)

toplevel(quote
    import .KCols: kncols, kcol, kwith, klen, kget
    struct KMeas; label::String; data::Vector{Vector{Float64}}; end
    @implement KCols.KTable KMeas                              # forwards to `data`, the one conforming field
    struct KHalves; left::Vector{Vector{Float64}}; right::Vector{Vector{Float64}}; end
    @implement KCols.KTable KHalves by right                   # forwarding written out
    struct KRamp; base::Vector{Float64}; n::Int; end
    kncols(r::KRamp) = r.n
    kcol(r::KRamp, i::Int) = r.base .* i
    kwith(r::KRamp, cs::Vector{Vector{Float64}}) = KRamp(cs[1], length(cs))
    @implement KCols.KTable KRamp                              # the type implements the operations
    mutable struct KState; u::Vector{Float64}; p::Tuple{Float64,Float64}; t::Float64; end
    @implement KCols.KInteg KState
    mutable struct KState2; tag::Symbol; t::Float64; p::Tuple{Float64,Float64}; u::Vector{Float64}; end
    @implement KCols.KInteg KState2                             # another layout, the same key
    struct KFrozen; p::Tuple{Float64,Float64}; u::Vector{Float64}; t::Float64; end
end)

@testset "Keys: the design's trait syntax" begin
    K = Main.KCols
    @test K.kmean([[1.0, 3.0]], 1) == 2.0
    m = Main.KMeas("run", [[1.0, 2.0], [4.0]])
    @test K.kmean(m, 2) == 4.0
    @test K.kmean(Main.KHalves([[0.0]], [[6.0]]), 1) == 6.0
    @test K.kmean(Main.KRamp([1.0, 3.0], 2), 2) == 4.0
    s = K.kscaled(m, 2.0)
    @test s isa Main.KMeas && s.label == "run" && s.data == [[2.0, 4.0], [8.0]]
    @test K.kscaled(Main.KRamp([1.0], 1), 3.0) isa Main.KRamp
    @test K.ksum([1, 2, 3]) === 6 && K.ksum([0.5, 0.25]) === 0.75
    @test TraitWorld.param(K.KVec, Val(:T), Vector{Int}) === Int
    st = Main.KState([1.0], (2.0, 3.0), 0.0)
    @test K.kadvance(st, 0.5) == 0.5 && st.t == 0.5
    key = first(TraitWorld._key_and_slots(K.KInteg, TraitWorld.proj_lookup(K.KInteg, Main.KState), Main.KState,
                                              TraitWorld.proj_witness(K.KInteg, Main.KState, TraitWorld.proj_lookup(K.KInteg, Main.KState))))
    @test key === TraitWorld.Key{Nothing,@NamedTuple{u::Vector{Float64}, p::Tuple{Float64,Float64}, t::Float64}}
    @test TraitWorld.param(K.KInteg, Val(:U), key) === Vector{Float64}
    @test TraitWorld.param(K.KInteg, Val(:P), key) === Tuple{Float64,Float64}
    # one worker per key: two mutable types and an immutable one, in different field orders
    @test K.kadvance(Main.KState2(:a, 1.0, (1.0, 1.0), [0.0]), 0.5) == 1.5
    @test K.knorm(st) == 2.0 && K.knorm(Main.KState2(:b, 0.0, (2.0, 0.0), [1.0, 1.0])) == 4.0
    e = try toplevel(:(@implement KCols.KInteg KFrozen)); nothing catch err; err end   # `t` is writable: refused
    while e isa LoadError; e = e.error; end
    @test e isa ImplementError && occursin("cannot be written", sprint(showerror, e))
    wk = only(m for m in methods(K.knorm) if Base.unwrap_unionall(m.sig).parameters[2] !== Any)
    # (instances at archetypes, from the definition and keep analyses, are not workers for a key)
    @test count(mi -> !occursin("Archetype", string(mi.specTypes)), Base.specializations(wk)) == 1
    @test isempty(check_definitions(K))
    # a parameter defined by a field and by an equation is refused
    e = try toplevel(quote
        @trait KBad{U} begin
            U = eltype(Self)
            x::U
        end
    end); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    @test e isa ErrorException && occursin("defined by the field", e.msg)
end

# A family conformance fixes each member's conformance at its first use: an override of an operation
# its default serves, defined later, is refused (as for a single type's declaration); defined before
# the member's first use, it is the member's own (session 27; the review of decisions 1 and 4, case v).
toplevel(quote
    @trait_module module FamOv
    using TraitWorld
    export Fam2, nf2, dbl, S2, d2
    @trait Fam2 begin
        nf2(x::Fam2)::Int
        dbl(x::Fam2)::Int = 2 * nf2(x)
    end
    struct S2{P}; p::P; k::Int; end
    nf2(s::S2) = s.k
    @implement Fam2 S2{P} where {P}
    d2(x::Fam2) = dbl(x)
    end
end)
@testset "Keys: late overrides for family members" begin
    F = Main.FamOv
    @test F.d2(F.S2{Int}(1, 2)) == 4                        # S2{Int}'s conformance is now fixed
    if TraitWorld._HAS_DEF_HOOK[]
        @test_throws Exception Core.eval(Main, :(FamOv.dbl(s::FamOv.S2{Int}) = 100))
        @test F.d2(F.S2{Int}(1, 2)) == 4
    else
        Core.eval(Main, :(FamOv.dbl(s::FamOv.S2{Int}) = 100))
        @test !isempty(TraitWorld.check_overrides())         # without the hook: found at the next checkpoint
        Base.delete_method(which(F.dbl, (F.S2{Int},)))
    end
    Core.eval(Main, :(FamOv.dbl(s::FamOv.S2{Float64}) = 100))  # before S2{Float64}'s first use: its own
    @test F.d2(F.S2{Float64}(1.0, 2)) == 100
end
