# The library core (W-106): the forms of traits §3–§6, §7.7, §8 and their checks.
using TraitWorld, Test

## parameters (traits §3.2)
@trait KVec{T} begin
    T = eltype(Self)
    klen(v::KVec)::Int
    kget(v::KVec{T}, i::Int)::T
end
struct Ramp; n::Int; end
Base.eltype(::Type{Ramp}) = Float64
klen(r::Ramp) = r.n
kget(r::Ramp, i::Int) = Float64(i)
@implement KVec Ramp

@trait Integrator{U, P} begin
    u::U
    @const p::P
    t::Float64
end
mutable struct Integ
    u::Vector{Float64}
    const p::Tuple{Int,Int}
    t::Float64
end
@implement Integrator Integ

@trait ArrayLike{T, N} begin
    alen(a::ArrayLike)::Int
end
struct MyVec; data::Vector{Float32}; end
alen(v::MyVec) = length(v.data)
@implement ArrayLike{Float32, 1} MyVec

@testset "parameters" begin
    @test Ramp(3) isa KVec{Float64}
    @test !(Ramp(3) isa KVec{Int})
    @test Ramp(3) isa KVec{<:Real}
    @test Ramp <: KVec
    @test Integ([1.0], (1, 2), 0.0) isa Integrator{Vector{Float64}, Tuple{Int,Int}}
    @test MyVec(Float32[1]) isa ArrayLike{Float32, 1}
    @test kget(Ramp(3), 2) === 2.0
    f(v::KVec{T}) where {T} = T
    @test f(Ramp(1)) === Float64
end

## refusals at the declaration (traits §5.10)
struct NoLen end
Base.eltype(::Type{NoLen}) = Int
struct WideKget; end
Base.eltype(::Type{WideKget}) = Int
klen(::WideKget) = 1
kget(::WideKget, i::Int) = i > 0 ? i : 1.0
struct BadT; end
Base.eltype(::Type{BadT}) = Int
klen(::BadT) = 1
kget(::BadT, i::Int) = i

@testset "refusals" begin
    e = try @eval(@implement KVec NoLen); nothing catch err; err end
    @test e isa ImplementError
    @test occursin("klen", sprint(showerror, e)) && occursin("kget", sprint(showerror, e))
    @test !(NoLen() isa KVec)
    e = try @eval(@implement KVec WideKget); nothing catch err; err end
    @test e isa ImplementError && occursin("wider", sprint(showerror, e))
    e = try @eval(@implement KVec{Float64} BadT); nothing catch err; err end   # stated against the equation
    @test e isa ImplementError && occursin("equation", sprint(showerror, e))
    e = try @eval(@implement ArrayLike MyVec); nothing catch err; err end       # undetermined parameters
    @test e isa ImplementError && occursin("not determined", sprint(showerror, e))
end

mutable struct FrozenInteg
    u::Vector{Float64}
    p::Tuple{Int,Int}
    const t::Float64
end
struct ImmInteg
    u::Vector{Float64}
    p::Tuple{Int,Int}
    t::Float64
end
@testset "fields" begin
    e = try @eval(@implement Integrator FrozenInteg); nothing catch err; err end
    @test e isa ImplementError && occursin("const", sprint(showerror, e))
    e = try @eval(@implement Integrator ImmInteg); nothing catch err; err end
    @test e isa ImplementError && occursin("immutable", sprint(showerror, e))
    i = Integ([1.0], (1, 2), 0.0)
    g(x::Integrator) = (x.t += 1.0; x.u[1])
    @test g(i) == 1.0 && i.t == 1.0
end

## a block of methods, forwarding (traits §5.4, §5.5)
@trait ColTable begin
    ncols(t::ColTable)::Int
    col(t::ColTable, i::Int)::Vector{Float64}
    firstcol(t::ColTable)::Vector{Float64} = col(t, 1)
end
@implement ColTable Vector{Vector{Float64}} begin
    ncols(t) = length(t)
    col(t, i) = t[i]
end
struct Halves
    name::String
    right::Vector{Vector{Float64}}
end
@implement ColTable Halves by right
colmean(t::ColTable, i::Int) = (c = col(t, i); sum(c) / length(c))

@testset "block and forwarding" begin
    v = [[1.0, 2.0], [3.0, 5.0]]
    @test v isa ColTable
    @test ncols(v) == 2 && firstcol(v) == [1.0, 2.0]
    h = Halves("h", v)
    @test h isa ColTable
    @test ncols(h) == 2 && col(h, 2) == [3.0, 5.0] && firstcol(h) == [1.0, 2.0]
    @test colmean(h, 2) == 4.0
    h2 = like(h, [[7.0]])
    @test h2 isa Halves && h2.name == "h" && ncols(h2) == 1
    @test withfields(h; name = "k").name == "k"
    struct Chain; inner::Halves; end
    e = try @eval(@implement ColTable Chain by inner); nothing catch err; err end
    @test e isa ImplementError && occursin("chain", sprint(showerror, e))
end

## supertraits (traits §4.5)
@trait DCol begin
    dlen(c::DCol)::Int
end
@trait DGrow{T} <: DCol begin
    T = eltype(Self)
    dpush!(c::DGrow, x::Float64)::Nothing
end
mutable struct Buf; xs::Vector{Float64}; end
Base.eltype(::Type{Buf}) = Float64
dlen(b::Buf) = length(b.xs)
dpush!(b::Buf, x::Float64) = (push!(b.xs, x); nothing)
@implement DGrow Buf
struct OnlyGrow; end
Base.eltype(::Type{OnlyGrow}) = Float64
dpush!(::OnlyGrow, ::Float64) = nothing

@testset "supertraits" begin
    @test DGrow <: DCol
    @test Buf(Float64[]) isa DCol && Buf(Float64[]) isa DGrow{Float64}
    e = try @eval(@implement DGrow OnlyGrow); nothing catch err; err end
    @test e isa ImplementError && occursin("dlen", sprint(showerror, e))
end

## Dynamic (traits §7.7, §8.3)
@testset "Dynamic" begin
    d = Dynamic{ColTable}([[1.0, 2.0]])
    @test d isa ColTable && ncols(d) == 1 && firstcol(d) == [1.0, 2.0]
    @test colmean(d, 1) == 1.5
    @test_throws ArgumentError Dynamic{KVec}(Ramp(2))           # the parameters required
    dk = Dynamic{KVec{Float64}}(Ramp(2))
    @test dk isa KVec{Float64} && kget(dk, 2) === 2.0 && klen(dk) == 2
    @test_throws TypeError Dynamic{ColTable}(Ramp(2))
    @test Dynamic{ColTable}(d) == d && unwrap(Dynamic{ColTable}(d)) === unwrap(d)
    v = [[1.0]]
    @test Dynamic{ColTable}(v) == Dynamic{ColTable}(v) && hash(Dynamic{ColTable}(v)) == hash(Dynamic{ColTable}(v))
    @test Dynamic{ColTable}(v) != Dynamic{ColTable}([[1.0]])
    dg = Dynamic{DGrow{Float64}}(Buf([1.0]))
    @test dg isa DCol && dlen(dg) == 1 && dpush!(dg, 2.0) === nothing && dlen(dg) == 2
    di = Dynamic{Integrator{Vector{Float64}, Tuple{Int,Int}}}(Integ([1.0], (1, 2), 0.0))
    @test di.u == [1.0] && (di.t = 2.0; di.t == 2.0)
    @test_throws ArgumentError (di.p = (3, 4))
    @test like(d, [[5.0]]) isa Dynamic{ColTable}
    hs = Dynamic{ColTable}[Dynamic{ColTable}(v), Dynamic{ColTable}(Halves("x", v))]
    @test sum(ncols, hs) == 2
end

## families (traits §5.8) and members checked at their first use (lowering §4)
@trait Fam begin
    fsize(x::Fam)::Int
end
struct Box{P}; x::P; end
fsize(b::Box) = 1
@implement Fam Box{P} where {P}

@testset "families" begin
    @test Box(1) isa Fam && Box("a") isa Fam
    @test fsize(Box(2.0)) == 1
    @test TraitWorld.check_first_use(Box{Int}, Fam) === nothing
end

## dispatch (traits §6)
describe2(v::Vector{Float64}) = "a vector"
describe2(m::AbstractMatrix) = "a matrix"
describe2(t::ColTable) = "a table with $(ncols(t)) columns"
describe2(x) = "something else"
@testset "dispatch" begin
    @test describe2([[1.0]]) == "a table with 1 columns"
    @test describe2(Halves("a", [[1.0]])) == "a table with 1 columns"
    @test describe2([1.0]) == "a vector"
    @test describe2(1) == "something else"
end

## a family's member that fails the contract, checked at its first use (F10; lowering §4)
@trait Sized2 begin
    sz(x::Sized2)::Int
end
struct W2{P}; x::P; end
sz(w::W2{Int}) = 1
@implement Sized2 W2{P} where {P}
@testset "first use" begin
    @test W2(1.0) isa Sized2                       # memberships only grow: isa stays true
    @test sz(W2(1)) == 1                           # its own method: no use through the trait
    # at dispatch (the hook's half in the compile queue is not built: lowering L-52)
    e = try Base.invokelatest(sz, W2(1.0)); nothing catch err; err end
    @test e isa ImplementError && occursin("sz", sprint(showerror, e))
    e2 = try Base.invokelatest(sz, W2(2.0)); nothing catch err; err end
    @test e2 === e                                 # the kept failure, raised at every use
end

## a family variable bounded by a Union: one membership per type (lowering §3)
@trait BoundedText begin
    btext(x::BoundedText)::String
end
btext(x::Integer) = string(x)
@implement BoundedText I where {I <: Union{Int8, Int16}}
@testset "Union-bounded family" begin
    @test Int8(1) isa BoundedText && Int16(1) isa BoundedText && !(Int32(1) isa BoundedText)
    @test length(Int8.name.memberships) == 1 && length(Int16.name.memberships) == 1
end

## intersections All{X, Y} (traits §3.6), where the build has them (W-107)
if isdefined(Core, :All)
    @trait IShape begin
        iarea(s::IShape)::Float64
    end
    @trait IPlaced begin
        iorigin(p::IPlaced)::Tuple{Float64, Float64}
    end
    struct IDisc
        r::Float64
    end
    iarea(d::IDisc) = pi * d.r^2
    iorigin(::IDisc) = (0.0, 0.0)
    struct IDot end
    iorigin(::IDot) = (1.0, 1.0)
    @implement (IShape, IPlaced) IDisc
    @implement IPlaced IDot
    const ShapeAt = All{IShape, IPlaced}                    # a bundle: a name for the intersection
    idescribe(x::ShapeAt) = (iarea(x), iorigin(x))
    idescribe(x::IPlaced) = iorigin(x)
    @testset "intersections" begin
        @test All === Core.All
        @test IDisc <: ShapeAt && !(IDot <: ShapeAt)
        @test ShapeAt === All{IPlaced, IShape}
        @test idescribe(IDisc(1.0)) == (float(pi), (0.0, 0.0))
        @test idescribe(IDot()) == (1.0, 1.0)
        d = Dynamic{ShapeAt}(IDisc(2.0))
        @test d isa IShape && d isa IPlaced && d isa ShapeAt
        @test Base.invokelatest(idescribe, d)[1] ≈ 4pi
        @test_throws TypeError Dynamic{ShapeAt}(IDot())
    end
end

## the override rule (traits §5.11) and the module's end (traits §5.2), by Julia's hooks (W-108)
if isdefined(Core, :All)
    @trait Greeter begin
        greet(g::Greeter)::String = "hello"              # a default
    end
    struct Polite end
    @implement Greeter Polite
    struct Formal end
    greet(::Formal) = "good evening"                     # before the membership: its own method
    @implement Greeter Formal
    @testset "override rule" begin
        @test greet(Polite()) == "hello"
        @test_throws ImplementError @eval greet(::Polite) = "good day"
        @test greet(Polite()) == "hello"                  # refused before it was visible
        @test greet(Formal()) == "good evening"
        @eval greet(::Formal) = "good night"              # not a default's call: allowed
        @test Base.invokelatest(greet, Formal()) == "good night"
    end
    @testset "module end" begin
        err = try
            Core.eval(@__MODULE__, :(module NoImpl
                struct S <: $Greeter end
            end))
            nothing
        catch e
            e
        end
        @test err isa ImplementError && occursin("@implement", sprint(showerror, err))
        m = Core.eval(@__MODULE__, :(module WithImpl
            using TraitWorld
            struct S <: $Greeter end
            @implement $Greeter S
        end))
        @test m isa Module && Base.invokelatest(greet, Base.invokelatest(getglobal, m, :S)()) == "hello"
    end
end

## an operation at a receiver typed by its trait is inferred as its declared result (compiler §7.1)
@trait Measured begin
    msize(x::Measured)::Int
    mname(x::Measured)::String = "m"
end
struct M1 end
struct M2 end
struct M3 end
struct M4 end
msize(::M1) = 1
msize(::M2) = 2
msize(::M3) = 3
msize(::M4) = 4
@implement Measured M1
@implement Measured M2
@implement Measured M3
@implement Measured M4
@trait Holds{T} begin
    T = eltype(Self)
    hget(x::Holds{T}, i::Int)::T
end
hget(v::Vector{Float64}, i::Int) = v[i]
@implement Holds Vector{Float64}
mtotal(v::Vector{Measured}) = (s = 0; for x in v; s += msize(x); end; s)
@testset "operation results" begin
    @test Base.infer_return_type(x -> msize(x), (Measured,)) === Int        # four members
    @test Base.infer_return_type(x -> mname(x), (Measured,)) === String     # a default
    @test Base.infer_return_type(mtotal, (Vector{Measured},)) === Int
    @test mtotal(Measured[M1(), M4()]) == 5
    @test Base.infer_return_type(x -> hget(x, 1), (Holds{Float64},)) === Float64
    @test Base.infer_return_type(x -> msize(x), (Any,)) !== Int             # an untyped receiver: Julia's rule
    @test Base.infer_return_type(x -> msize(x), (M2,)) === Int              # a concrete member: its method
end

## the split over a trait's first members, and the fallback past them (compiler §7.2)
struct M5 end
msize(::M5) = 5
@implement Measured M5
mfirst(x::Measured) = msize(x)
@testset "split" begin
    @test mtotal(Measured[M1(), M2(), M3(), M4(), M5()]) == 15
    @test mfirst(M5()) == 5                                   # the fifth member: the fallback
    src = sprint(show, first(Base.code_typed(mtotal, (Vector{Measured},)))[1])
    @test occursin("isa", src)                               # branches on the first members
end

## the table of a call's targets past the split (compiler §7.3)
@trait Scaled begin
    scaled(x::Scaled, k::Int)::Int
end
for (i, n) in enumerate((:S1, :S2, :S3, :S4, :S5))
    @eval struct $n end
    @eval scaled(::$n, k::Int) = $i * k
    @eval @implement Scaled $n
end
scale_all(v::Vector{Scaled}, k::Int) = (s = 0; for x in v; s += scaled(x, k); end; s)
@testset "table" begin
    src = sprint(show, first(Base.code_typed(scale_all, (Vector{Scaled}, Int)))[1])
    @test occursin("jl_split_table_ptr", src)
    @test scale_all(Scaled[S1(), S5()], 2) == 12                # the fifth member through the table
    @eval struct S6 end
    @eval scaled(::S6, k::Int) = 6 * k
    @eval @implement Scaled S6
    @test Base.invokelatest(scale_all, Scaled[S6(), S5(), S1()], 1) == 12   # declared later
end

## a declared field read at a value typed by its trait: its declared type (compiler §7.1)
gu(x::Integrator) = x.u
gt(x::Integrator) = x.t
@testset "declared fields" begin
    @test Base.infer_return_type(gt, (Integrator,)) === Float64
    @test Base.infer_return_type(gu, (Integrator{Vector{Float64}, Tuple{Int,Int}},)) === Vector{Float64}
    @test gt(Integ([1.0], (1, 2), 2.5)) == 2.5
end

## the classification (traits §7.3): fully bounded methods, open ones, @bounded and @open
module ClassifyCase
using TraitWorld
@trait CTable begin
    ncols(t::CTable)::Int
    col(t::CTable, i::Int)::Vector{Float64}
end
struct CT; data::Vector{Vector{Float64}}; end
ncols(t::CT) = length(t.data)
col(t::CT, i::Int) = t.data[i]
@implement CTable CT
colmean(t::CTable, i::Int) = sum(col(t, i)) / length(col(t, i))   # fully bounded
helper(t) = ncols(t) + 1                                          # unannotated, followed
viahelper(t::CTable) = helper(t)                                  # fully bounded through it
leak(t::CTable) = typeof(t)                                       # open
wide(t::CTable) = length(t)                                       # open: `length` is not an operation
end
@testset "classification" begin
    C = ClassifyCase
    @test isempty(classify(only(methods(C.colmean))))
    @test isempty(classify(only(methods(C.viahelper))))
    @test !isempty(classify(only(methods(C.leak))))
    @test !isempty(classify(only(methods(C.wide))))
    ps = check_definitions(C)
    @test length(ps) == 2 && any(p -> occursin("leak", p), ps) && any(p -> occursin("wide", p), ps)
    e = try Core.eval(C, :(@bounded leak2(t::CTable) = typeof(t))); nothing catch err; err end
    @test e isa TraitUseError
    @test !isdefined(C, :leak2) || isempty(methods(getglobal(C, :leak2)))
    Core.eval(C, :(@open leak3(t::CTable) = typeof(t)))
    Core.eval(C, :(@bounded ok2(t::CTable) = ncols(t)))
    @test Base.invokelatest(getglobal(C, :ok2), C.CT([[1.0]])) == 1
    @test length(check_definitions(C)) == 2                         # @open is skipped
end

## the classification's further rules (traits §7.3), found by W-104's third slice: a declared field written,
## a constructor storing the argument in a field typed by the trait, a callee's own variables, an `@open`
## function's uses its own, a value of an unrelated trait not tracked
module ClassifyMore
using TraitWorld
@trait VWin{U} begin
    @const u::U
    flag::Bool
    winop(w::VWin{U})::Nothing
end
mutable struct WinS; u::Vector{Float64}; flag::Bool; end
winop(w::WinS) = nothing
@implement VWin{Vector{Float64}} WinS
@trait Other begin
    otherop(o::Other)::Int
end
struct Holder{U}; w::VWin{U}; end
setflag!(w::VWin{U}) where {U} = (w.flag = true; nothing)                # a writable declared field
hold(w::VWin{U}) where {U} = Holder{U}(w)                                 # stored in a field typed by the trait
pass(w::VWin{U}) where {U} = setflag!(w)                                  # the callee's own `U`
@open peek(w::VWin{U}) where {U} = typeof(w)                              # open on purpose
viapeek(w::VWin{U}) where {U} = (peek(w); nothing)                        # its use is peek's
struct Box; o::Other; end
reads(w::VWin{U}, b::Box) where {U} = (string(b.o); nothing)              # `b.o` is no argument of VWin's
end
@testset "classification: further rules" begin
    C = ClassifyMore
    for f in (C.setflag!, C.hold, C.pass, C.viapeek)
        @test isempty(classify(only(methods(f))))
    end
    @test isempty(classify(only(methods(C.reads))))
    @test !isempty(classify(only(methods(C.peek))))
end

## a family's variables are in scope in its block's methods (traits §5.4, §5.8)
module FamilyScope
using TraitWorld
@trait Holds{T} begin
    elt(h::Holds{T})::Type
end
struct Box2{T}; x::T; end
@implement Holds{T} Box2{T} where {T} begin
    elt(h) = T
end
end
@testset "a family's variables in its block" begin
    @test FamilyScope.elt(FamilyScope.Box2(1.5)) === Float64
    @test FamilyScope.elt(FamilyScope.Box2("a")) === String
end

## a `Dynamic` callable kept at two signatures takes the one its arguments match (traits §7.7)
@testset "Dynamic{All{Callable…}} at either signature" begin
    d = Dynamic{All{Callable{Tuple{Int}, Int}, Callable{Tuple{Float64}, Float64}}}(x -> 2x)
    @test d(3) === 6 && d(1.5) === 3.0
    @test_throws MethodError d("a")
end
