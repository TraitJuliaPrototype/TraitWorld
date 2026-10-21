# The checks at the declaration (traits reference §4.9, §3.4, §4.7): a parameter outside its bound is
# refused, a family member that does not conform is refused at its first use, and a refused
# declaration defines nothing. Runs inside runtests.jl, or alone: julia --project=. test/declaration.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module DeclG
    using TraitWorld
    export RVec, rlen, rfirst, NVec, nfirst, FVec, flen, fget, fsum, rsum, NumberLike, nval
    @trait NumberLike begin
        nval(x::NumberLike)::Float64
    end
    @implement NumberLike Float64 begin
        nval(x) = x
    end
    @trait RVec{T <: Real} begin
        T = eltype(Self)
        rlen(v::RVec)::Int
        rfirst(v::RVec{T})::T
    end
    @trait NVec{T <: NumberLike} begin
        T = eltype(Self)
        nfirst(v::NVec{T})::T
    end
    @trait FVec{T} begin
        T = eltype(Self)
        flen(v::FVec)::Int
        fget(v::FVec{T}, i::Int)::T
    end
    @implement FVec A where {A <: Vector{<:Real}} begin
        flen(v) = length(v)
        fget(v, i) = v[i] * 1.0          # a Float64: right for Vector{Float64}, outside T for Vector{Int8}
    end
    fsum(v::FVec) = sum(fget(v, i) for i in 1:flen(v))
    rsum(v::RVec) = rfirst(v)
    end
end)

using .DeclG
struct DStr; v::Vector{String}; end
struct DFloat; v::Vector{Float64}; end
struct DBad; v::Vector{Float64}; end
Base.eltype(::Type{DStr}) = String
Base.eltype(::Type{DFloat}) = Float64
Base.eltype(::Type{DBad}) = Float64
struct DIntv; v::Vector{Int}; end
Base.eltype(::Type{DIntv}) = Int

inner(e) = e isa LoadError ? e.error : e

@testset "checks at the declaration" begin
    G = Main.DeclG
    # a parameter within its bound, and outside it (§3.4)
    toplevel(:(@implement RVec DFloat begin
        rlen(d) = length(d.v)
        rfirst(d) = d.v[1]
    end))
    @test G.rsum(DFloat([2.0])) == 2.0
    e = try toplevel(:(@implement RVec DStr begin
            rlen(d) = length(d.v)
            rfirst(d) = d.v[1]
        end)); nothing catch err; err end
    @test inner(e) isa ImplementError && occursin("outside its bound T <: Real", sprint(showerror, inner(e)))
    # a refused declaration defines nothing (§4.9): no operation's method, no record
    @test !hasmethod(G.rlen, Tuple{DStr})
    @test TraitWorld.implementation(G.RVec, DStr) === nothing
    @test_throws MethodError G.rsum(DStr(["a"]))
    # a trait as the bound: the parameter's value must conform
    e = try toplevel(:(@implement NVec DIntv begin nfirst(d) = d.v[1] end)); nothing catch err; err end
    @test inner(e) isa ImplementError && occursin("outside its bound T <: NumberLike", sprint(showerror, inner(e)))
    toplevel(:(@implement NVec DFloat begin nfirst(d) = d.v[1] end))
    @test TraitWorld.implementation(G.NVec, DFloat) !== nothing
    # a result that does not infer: refused, and nothing defined
    e = try toplevel(:(@implement RVec DBad begin
            rlen(d) = length(d.v)
            rfirst(d) = string(d.v[1])
        end)); nothing catch err; err end
    @test inner(e) isa ImplementError && occursin("returns `String`", sprint(showerror, inner(e)))
    @test !hasmethod(G.rfirst, Tuple{DBad}) && !hasmethod(G.rlen, Tuple{DBad})
    # a family member that does not conform is refused at its first use (§4.7)
    @test G.fsum([1.0, 2.0]) == 3.0
    e = try G.fsum(Int8[1]); nothing catch err; err end
    @test e isa ImplementError && occursin("member of a family implementation", sprint(showerror, e))
    @test G.fsum([3.0]) == 3.0                                  # other members unaffected
end

toplevel(quote
    @trait_module module DeclS
    using TraitWorld
    export SA, sa, SB, sb
    @trait SA begin
        sa(x::SA)::Float64
    end
    @trait SB <: SA begin
        sb(x::SB)::Float64
    end
    end
end)
using .DeclS
struct SPart; a::Float64; end
DeclS.sa(p::SPart) = p.a
DeclS.sb(p::SPart) = 2p.a
struct SWhole; part::SPart; b::Float64; end
DeclS.sa(w::SWhole) = w.b
DeclS.sb(w::SWhole) = w.b
struct SOk; part::SPart; end

@testset "a subtrait's implementation agrees with its supertrait's" begin
    toplevel(:(@implement SA SPart))
    toplevel(:(@implement SB SPart))
    toplevel(:(@implement SA SWhole))                          # by its own methods
    e = try toplevel(:(@implement SB SWhole by part)); nothing catch err; err end   # by a field: disagrees
    @test inner(e) isa ImplementError && occursin("its supertrait SA by its own methods", sprint(showerror, inner(e)))
    @test TraitWorld.projection(SB, SWhole) === nothing && !TraitWorld._declared_for(SB, SWhole)   # nothing defined
    toplevel(:(@implement SA SOk by part))
    toplevel(:(@implement SB SOk by part))                    # the same field: agrees
    @test TraitWorld.implementation(SB, SOk) !== nothing || TraitWorld.projection(SB, SOk) !== nothing
end

