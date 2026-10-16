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
    @test TraitWorld.param(K.KInteg, Val(:U), Main.KState) === Vector{Float64}
    @test TraitWorld.param(K.KInteg, Val(:P), Main.KState) === Tuple{Float64,Float64}
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
