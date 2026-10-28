# BaseTraits' capabilities from the ports' cases (traits reference §8.1, "Next in BaseTraits"):
# `asvector`, `Solvable`, `BoundedText`, `HasProperty`, each with its case in miniature.
# Runs inside runtests.jl, or alone: julia --project=. test/basetraits_next.jl
using Test, TraitWorld
using LinearAlgebra, Dates
const BTN = TraitWorld.BaseTraits      # (runtests.jl's Main has other traits of these names)
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))
"The exception evaluating `ex` at top level throws (unwrapping `LoadError`), or `nothing`."
function thrown_btn(ex)
    try
        toplevel(ex)
        return nothing
    catch e
        while e isa LoadError
            e = e.error
        end
        return e
    end
end

# --- asvector: the DataFrames kernels' `CellVector`, a column handed to plain code -------------------
toplevel(quote
    @trait_module module BTNCols
    using TraitWorld
    export cellmean, cellmedian, cellvec, cellsum_dyn
    # a kernel hands the cells to plain code that reads a vector (Base's `sum`, `sort`), in place
    cellmean(c::Indexable{Float64}) = sum(asvector(c)) / length(c)
    cellmedian(c::Indexable{Float64}) = (s = sort(asvector(c)); s[(length(s) + 1) ÷ 2])
    cellvec(c::Indexable{T}) where {T} = asvector(c)
    cellsum_dyn(c::Dynamic{Indexable{T}}) where {T} = sum(asvector(c))
    end
end)

# a user's column type, Indexable by its own methods
struct BTNCol
    data::Vector{Float64}
end
Base.length(c::BTNCol) = length(c.data)
Base.getindex(c::BTNCol, i::Int) = c.data[i]
Base.eltype(::Type{BTNCol}) = Float64
@implement BTN.HasLength BTNCol
@implement BTN.Indexable BTNCol

btn_cellvec(c::BTNCol) = Main.BTNCols.cellvec(c)

@testset "asvector: a trait collection as an AbstractVector for plain code" begin
    C = Main.BTNCols
    c = BTNCol([1.0, 2.0, 6.0])
    @test C.cellmean(c) == 3.0
    @test C.cellmean([1.0, 2.0, 6.0]) == 3.0
    @test C.cellmedian(c) == 2.0 && c.data == [1.0, 2.0, 6.0]
    v = btn_cellvec(c)                                              # a caller that knows the type: Compiled
    @test v isa AbstractVector{Float64} && v isa IndexableVector
    @test v == [1.0, 2.0, 6.0] && length(v) == 3 && v[3] == 6.0
    c.data[1] = 10.0
    @test v[1] == 10.0                                              # no copy: reads the user's object
    # Compiled: the collection's own type is the parameter, so plain code is compiled per type
    @test typeof(v) === IndexableVector{Float64, BTNCol}
    # Dynamic: one vector type per item type, whatever the collection
    @test typeof(C.cellvec(compiled_for(c))) === IndexableVector{Float64, BTNCol}
    vd = C.cellvec(with_dynamic(c))
    @test typeof(vd) === IndexableVector{Float64, Dynamic{BTN.Indexable{Float64}}}
    @test typeof(C.cellvec(with_dynamic([1.0, 2.0]))) === typeof(vd)
    @test vd == [10.0, 2.0, 6.0]
    @test C.cellsum_dyn(c) == 18.0 && C.cellsum_dyn([1.0, 2.0]) == 3.0
    @test C.cellvec(1:3) == [1, 2, 3] && eltype(C.cellvec(1:3)) === Int
end

# --- Solvable: ODECore's `LinearCache`, a factorization kept to solve ------------------------------
toplevel(quote
    @trait_module module BTNLin
    using TraitWorld
    using LinearAlgebra: lu!, qr
    export Newtonish, step!, factor
    # a solver keeps whatever factorization its linear solver made, as a Solvable
    mutable struct Newtonish
        F::Solvable{Float64}                        # Kept{Solvable{Float64}}
        x::Vector{Float64}
    end
    step!(s::Newtonish, b::Vector{Float64}) = (solve!(s.F, s.x, b); s.x)
    solvewith(F::Solvable{T}, b::Vector{T}) where {T} = (x = similar(b); solve!(F, x, b); x)
    factor(W::Matrix{Float64}, how::Symbol) = how === :lu ? Kept{Solvable{Float64}}(lu!(W)) : Kept{Solvable{Float64}}(qr(W))
    end
end)

@testset "Solvable: LinearAlgebra's factorizations solve linear systems" begin
    L = Main.BTNLin
    A = [4.0 1.0; 2.0 3.0]; b = [1.0, 2.0]
    @test conforms(typeof(lu(A)), Solvable{Float64}) && conforms(typeof(qr(A)), Solvable{Float64})
    @test conforms(typeof(cholesky([2.0 0.0; 0.0 3.0])), Solvable{Float64})
    @test !conforms(typeof(lu(A)), Solvable{Float32}) && !conforms(Matrix{Float64}, Solvable{Float64})
    @test L.solvewith(lu(A), b) ≈ A \ b
    @test L.solvewith(qr(A), b) ≈ A \ b
    @test L.solvewith(lu(Float32.(A)), Float32.(b)) ≈ Float32.(A \ b)
    s = L.Newtonish(L.factor(copy(A), :lu), zeros(2))
    @test L.step!(s, b) ≈ A \ b
    s.F = L.factor(copy(A), :qr)                    # another factorization, the same field
    @test L.step!(s, b) ≈ A \ b
    @test_throws TraitBoundError Kept{Solvable{Float64}}(A)
end

# --- BoundedText: CSV's writer sizing its buffers from the cells' types ------------------------------
toplevel(quote
    @trait_module module BTNText
    using TraitWorld
    export rowbound, cellbound
    rowbound(cells::Iterable{BoundedText}) = (n = 0; for c in cells; n += textbound(c) + 1; end; n)
    cellbound(x::BoundedText) = textbound(x)
    end
end)

@testset "BoundedText: a bound on the bytes print writes" begin
    T = Main.BTNText
    samples = Any[true, false, typemin(Int8), typemax(UInt8), typemin(Int64), typemax(UInt64), typemin(Int128), typemax(UInt128),
                  big(2)^200, -big(3)^100, -floatmin(Float64), -nextfloat(0.0), 1.2345678901234567e-5, -1.2345678901234567e15,
                  -floatmin(Float32), Float16(-6.104e-5), -big"1.5e-123456789", big(2)^100 // 3, -7 // 3, 1.0 - NaN * im,
                  Complex(true, false), π, ℯ, :abc, :πx, 'a', 'π', '😀', "", "abc", "πx😀", SubString("hello", 2, 4),
                  typemax(Date), typemin(Date), typemin(DateTime), DateTime(2024, 1, 2, 3, 4, 5, 678), typemax(Time),
                  Millisecond(typemin(Int)), Day(3), Dates.CompoundPeriod(Day(1), Hour(2)), Dates.CompoundPeriod()]
    for x in samples
        @test conforms(typeof(x), BoundedText)
        @test ncodeunits(sprint(print, x)) <= T.cellbound(x)
    end
    @test T.cellbound(typemax(Int64)) == T.cellbound(0)              # a constant of a fixed-width type
    @test T.rowbound(Any[1, "abc", 2.5, Date(2024, 1, 1)]) >= ncodeunits("1,abc,2.5,2024-01-01")
    @test !conforms(Vector{Int}, BoundedText) && !conforms(Nothing, BoundedText)
end

# --- HasProperty: SciML's `integ.ps[:σ]` in a callback that receives `Dynamic{IntegratorView}` ------------
toplevel(quote
    @trait_module module BTNProp
    using TraitWorld
    export IntegView, ParamInteg, PView, curt, sigma_now, sigma_dyn, x_and_sigma, Saved, keep, sigma_kept, readps
    "Parameters read by name, as SciML's `integ.ps[:σ]`."
    struct PView
        names::Vector{Symbol}
        vals::Vector{Float64}
    end
    Base.getindex(p::PView, s::Symbol) = p.vals[findfirst(==(s), p.names)]
    @trait IntegView begin
        curt(i::IntegView)::Float64
    end
    # the integrator a callback sees: its time, and its parameters by name, a computed property
    @trait ParamInteg{PS} <: (IntegView, HasProperty{:ps, PS}) begin
        stepcount(i::ParamInteg)::Int
    end
    sigma_now(i::ParamInteg{PView}) = i.ps[:σ] * curt(i)
    sigma_dyn(i::Dynamic{ParamInteg{PView}}) = i.ps[:σ]                  # a callback compiled once
    x_and_sigma(i::(HasProperty{:ps, PView}, HasProperty{:x, Float64})) = i.x + i.ps[:σ]
    readps(i::HasProperty{:ps, PS}) where {PS} = i.ps
    mutable struct Saved
        integ::ParamInteg{PView}                                         # Kept{ParamInteg{PView}}
    end
    keep(i::ParamInteg{PView}) = Saved(i)
    sigma_kept(s::Saved) = s.integ.ps[:σ]
    end
end)

mutable struct BTNInteg
    t::Float64
    u::Vector{Float64}
    p::Vector{Float64}
    n::Int
end
const BTNP = Main.BTNProp
@implement BTNP.IntegView BTNInteg begin
    curt(i) = i.t
end
# one type at two names: `HasProperty{:ps, …}` and `HasProperty{:x, …}`, each its own implementation
@implement HasProperty{:ps, BTNP.PView} BTNInteg begin
    property(i, ::Val{:ps}) = BTNP.PView([:σ, :ρ], i.p)
end
@implement HasProperty{:x, Float64} BTNInteg begin
    property(i, ::Val{:x}) = i.u[1]
end
@implement BTNP.ParamInteg{BTNP.PView} BTNInteg begin
    stepcount(i) = i.n
end
struct BTNOther
    t::Float64
end
@implement BTNP.IntegView BTNOther begin
    curt(i) = i.t
end
btn_sigma(i::BTNInteg) = BTNP.sigma_now(i)
btn_ps(d::Dynamic{BTNP.ParamInteg{BTNP.PView}}) = d.ps                 # a plain caller reading a kept value's property
btn_x(d::Dynamic{HasProperty{:x, Float64}}) = d.x

@testset "HasProperty: property access at a name, an input parameter" begin
    P = BTNP
    i = BTNInteg(2.0, [5.0], [10.0, 28.0], 3)
    @test conforms(BTNInteg, HasProperty{:ps, P.PView}) && conforms(BTNInteg, HasProperty{:x, Float64})
    @test !conforms(BTNInteg, HasProperty{:x, Int}) && !conforms(BTNInteg, HasProperty{:y, Float64})
    @test !conforms(BTNOther, HasProperty{:ps, P.PView})
    @test TraitWorld._family(HasProperty{:ps, P.PView}) === HasProperty{:ps}
    # through a supertrait: the callback's integrator reads `integ.ps[:σ]`
    @test P.sigma_now(i) == 20.0 && btn_sigma(i) == 20.0
    @test P.sigma_dyn(i) == 10.0
    @test P.x_and_sigma(i) == 15.0                               # two names of one type, one bound
    @test P.readps(i).vals == [10.0, 28.0]
    # a kept value: `Dynamic{ParamInteg{PView}}` reads `x.ps` through the operation
    d = Dynamic{P.ParamInteg{P.PView}}(i)
    @test d.ps[:ρ] == 28.0
    @test P.sigma_kept(P.keep(i)) == 10.0
    i.p[1] = 11.0
    @test d.ps[:σ] == 11.0                                       # reads the user's object
    # a plain caller's `x.ps` stays typed: the name is a constant carried into the operation
    @test Base.return_types(btn_ps, (Dynamic{P.ParamInteg{P.PView}},)) == Any[P.PView]
    @test btn_x(Dynamic{HasProperty{:x, Float64}}(i)) == 5.0
    @test Base.return_types(btn_x, (Dynamic{HasProperty{:x, Float64}},)) == Any[Float64]
    # a value without the property: refused at the bound, and `x.name` on a kept value without it raises
    @test_throws Exception P.sigma_now(BTNOther(1.0))
    @test_throws Exception Dynamic{P.IntegView}(i).ps
    # an input parameter is stated as a value; a bound fixes it
    @test thrown_btn(:(@implement HasProperty BTNOther begin property(i, ::Val{:t}) = i.t end)) isa ImplementError
end
