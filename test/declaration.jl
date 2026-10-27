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


# A bounded method in a trait module defines a method of the function its name resolves to, as in
# Julia (traits §5.5; T-66, found by E-156 X1): a name the module has only by an implicit `using`
# (Base's `peek`) is a new function of the module; one imported by name is that function.
toplevel(quote
    @trait_module module DeclName
    using TraitWorld
    export XN, xv
    @trait XN begin
        xv(x::XN)::Int
    end
    peek(x::XN) = xv(x)                  # Base exports `peek`: here a new function DeclName.peek
    end
    struct XNv; v::Int; end
    DeclName.xv(x::XNv) = x.v
    @implement DeclName.XN XNv
end)
@testset "a bounded method's name resolves as in Julia" begin
    @test DeclName.peek !== Base.peek && parentmodule(DeclName.peek) === DeclName
    @test DeclName.peek(XNv(3)) == 3
    e = try toplevel(quote
        @trait_module module DeclNameImp
        using TraitWorld, ..DeclName
        import Base: peek
        peek(x::DeclName.XN) = 1         # imported by name: Base's function, which this module does not own
        end
    end); nothing catch err; err end
    @test inner(e) isa ErrorException && occursin("belongs to Base", sprint(showerror, inner(e)))
end

# A supertrait with parameters takes the subtrait's parameters by name (traits §3.6; T-67, W-46,
# E-156 P5): a type implements the subtrait at `U, T` only if it implements the supertrait at the
# same values; a parameter the supertrait's fields define comes from there; the supertrait's
# parameters may be written with constants and type constructors.
toplevel(quote
    @trait_module module DeclSup
    using TraitWorld
    export PView, PInt, pstep!, QInt, qn, supkind, iparams, drive!, qparams
    @trait PView{U, T} begin
        u::U
        t::T
    end
    @trait PInt{U, T} <: PView{U, T} begin
        pstep!(i::PInt)::Nothing
    end
    @trait QInt{T} <: PView{Vector{T}, Float64} begin
        qn(q::QInt)::Int
    end
    supkind(i::PView) = :view
    supkind(i::PInt) = :integrator
    iparams(i::PInt{U, T}) where {U, T} = (U, T)
    drive!(i::PInt{U, T}) where {U, T} = (pstep!(i); pstep!(i); i.t)    # the supertrait's field through the subtrait
    qparams(q::QInt{T}) where {T} = (T, q.t)
    end
end)
using .DeclSup
mutable struct PI{U, T}; u::U; t::T; end
DeclSup.pstep!(i::PI) = (i.t += one(i.t); nothing)
mutable struct PS; u::Vector{Float64}; t::Float64; end
DeclSup.pstep!(i::PS) = nothing
mutable struct PS2; u::Vector{Float64}; t::Float64; end
DeclSup.pstep!(i::PS2) = nothing
mutable struct PF{U, T}; u::U; t::T; end
DeclSup.pstep!(i::PF) = nothing
mutable struct QS; u::Vector{Float32}; t::Float64; end
DeclSup.qn(q::QS) = length(q.u)
mutable struct QS2; u::Vector{Float32}; t::Float64; end
DeclSup.qn(q::QS2) = length(q.u)
toplevel(quote
    @implement PView PI{U, T} where {U, T}
    @implement PInt PI{U, T} where {U, T}                 # the parameters from PView's fields
    @implement PView PS
    @implement PView PS2
    @implement PView PF{U, T} where {U, T}
    @implement PInt{U, Float32} PF{U, T} where {U, T}     # a member at T ≠ Float32 disagrees with PView
    @implement PView QS
    @implement PView QS2
end)
@testset "a supertrait with parameters takes the subtrait's parameters by name" begin
    @test supkind(PI([1.0], 0.0)) === :integrator && supkind(PS([1.0], 0.0)) === :view
    @test iparams(PI(Float32[1], 0.0f0)) === (Vector{Float32}, Float32)
    typed_drive(i::PI{Vector{Float64}, Float64}) = drive!(i)
    @test typed_drive(PI([1.0], 0.0)) === 2.0
    toplevel(:(@implement PInt{Vector{Float64}, Float64} PS2))          # the same values as PView's: accepted
    @test iparams(PS2([1.0], 0.0)) === (Vector{Float64}, Float64)
    e = try toplevel(:(@implement PInt{Vector{Float32}, Float64} PS)); nothing catch err; err end
    @test inner(e) isa ImplementError && occursin("disagree", sprint(showerror, inner(e)))
    @test supkind(PS([1.0], 0.0)) === :view                               # nothing defined
    @test supkind(PF([1.0], 0.0f0)) === :integrator                       # a member at Float32 agrees
    e = try supkind(PF([1.0], 0.0)); nothing catch err; err end
    @test e isa ImplementError && occursin("asks for", sprint(showerror, e))
    toplevel(:(@implement QInt{Float32} QS))                           # PView at Vector{Float32}, Float64
    @test qparams(QS(Float32[1], 2.0)) === (Float32, 2.0)
    e = try toplevel(:(@implement QInt{Float64} QS2)); nothing catch err; err end
    @test inner(e) isa ImplementError && occursin("asks for", sprint(showerror, inner(e)))
end

# `@implement` of a bundle is the tuple's (traits reference §3.6, §3.7; T-73, W-54): it implements
# each member, by the type's own methods
@testset "@implement of a bundle" begin
    toplevel(quote
        @trait_module module DeclB
        using TraitWorld
        export A4, B4, AB4, fa, fb, both
        @trait A4 begin; fa(x::A4)::Int; end
        @trait B4 begin; fb(x::B4)::Int; end
        @trait AB4 <: (A4, B4)
        both(x::AB4) = fa(x) + fb(x)
        end
        struct G4; n::Int; end
        DeclB.fa(g::G4) = g.n
        DeclB.fb(g::G4) = 2g.n
    end)
    toplevel(:(@implement DeclB.AB4 G4))
    D, G4 = Base.invokelatest(getglobal, Main, :DeclB), Base.invokelatest(getglobal, Main, :G4)
    A4, B4 = Base.invokelatest(getglobal, D, :A4), Base.invokelatest(getglobal, D, :B4)
    @test Base.invokelatest(conforms, G4, A4) && Base.invokelatest(conforms, G4, B4)
    @test Base.invokelatest(Base.invokelatest(getglobal, D, :both), Base.invokelatest(G4, 1)) == 3
end
