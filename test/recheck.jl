# A member's check holds while it is a member (traits §5.10, §5.11): a method defined after the check
# that would serve a checked call with a result outside the declared one, make the operation ambiguous
# at the member, or take a call the membership fixed (a default's, the forwarding's) is refused before
# it exists. A result within the declared one is accepted.
using TraitWorld, Test

function thrown(ex)
    try
        Core.eval(@__MODULE__, ex)
        return nothing
    catch e
        while e isa LoadError; e = e.error; end
        return e
    end
end
latest(f, args...) = Base.invokelatest(f, args...)
msg(e) = sprint(showerror, e)
nrecords(f, member) = count(r -> r.member === member, get(TraitWorld._CHECKED_RESULTS, f, Any[]))

@trait Meas begin
    msz(x::Meas)::Int
    mget(x::Meas, i::Int)::Int
    mstate(x::Meas, s)::Int                      # a further argument declared abstract: nothing recorded
end
via(x::Meas) = msz(x)                            # a call through the trait

struct MA end
msz(::MA) = 1
mget(::MA, i::Integer) = 10
mstate(::MA, s) = 0
@implement Meas MA

@testset "a redefinition" begin
    e = thrown(:(msz(::MA) = UInt(2)))
    @test e isa ImplementError
    m = msg(e)
    @test occursin("MA", m) && occursin("msz", m) && occursin("Meas", m)
    @test occursin("UInt64", m) && occursin("Int", m) && occursin("return within", m) && occursin("do not define the method", m)
    @test latest(msz, MA()) === 1 && latest(via, MA()) === 1   # the old method in force
    @test thrown(:(msz(::MA) = 3)) === nothing                 # within the declared result
    @test latest(msz, MA()) === 3 && latest(via, MA()) === 3
    @test nrecords(msz, MA) == 1
end

@testset "a more specific method" begin
    @test thrown(:(mget(::MA, i::Int) = UInt(1))) isa ImplementError
    @test latest(mget, MA(), 1) === 10
    @test thrown(:(mget(::MA, i::Int) = 11)) === nothing
    @test latest(mget, MA(), 1) === 11
    @test thrown(:(mget(::MA, i::Int8) = UInt(1))) === nothing   # not a call the check made
end

@testset "an abstract further argument" begin
    @test nrecords(mstate, MA) == 0
    @test thrown(:(mstate(::MA, s::Int) = UInt(1))) === nothing
end

@testset "a method defined in another module" begin
    e = thrown(:(module Pir
        import ..msz, ..MA
        msz(::MA) = UInt(9)
    end))
    @test e isa ImplementError
    @test latest(msz, MA()) === 3
end

struct MB end
msz(::MB) = 1
mget(::MB, i::Integer) = 1
mstate(::MB, s) = 0
@implement Meas MB
@testset "an ambiguity at the member" begin
    e = thrown(:(mget(::Any, i::Int) = 2))
    @test e isa ImplementError && occursin("ambiguous", msg(e))
    @test latest(mget, MB(), 1) === 1
end

struct MC end
msz(::MC) = 1
mget(::MC, i::Int) = 1
mstate(::MC, s) = 0
@implement Meas MC
@testset "deleted, then defined again (Revise's order)" begin
    Base.delete_method(which(msz, (MC,)))
    @test_throws OperationError latest(msz, MC())
    @test thrown(:(msz(::MC) = UInt(1))) isa ImplementError   # the record, not the state, is the reference
    @test thrown(:(msz(::MC) = 2)) === nothing
    @test latest(via, MC()) === 2
end

## a pattern member, checked at its first use (lowering §4)
@trait Meas3 begin
    m3(x::Meas3)::Int
end
struct Fam3{P}; x::P; end
m3(::Fam3) = 1
@implement Meas3 Fam3{P} where {P}

@testset "a pattern member at its first use" begin
    @test TraitWorld.check_first_use(Fam3{Float64}, Meas3) === nothing
    @test thrown(:(m3(::Fam3{Float64}) = UInt(3))) isa ImplementError
    @test latest(m3, Fam3(1.0)) === 1
    @test thrown(:(m3(::Fam3{Float64}) = 4)) === nothing
    @test thrown(:(m3(::Fam3{Int8}) = UInt(3))) === nothing   # not checked yet: its first use checks it
    e = try TraitWorld.check_first_use(Fam3{Int8}, Meas3); nothing catch err; err end
    @test e isa ImplementError                               # the first use refuses it
end

## the forwarding's methods are the membership's (traits §5.11)
@trait Meas2 begin
    msz2(x::Meas2)::Int
end
struct Inner; n::Int; end
msz2(x::Inner) = x.n
@implement Meas2 Inner
struct Outer; i::Inner; end
@implement Meas2 Outer by i
via2(x::Meas2) = msz2(x)

@testset "a forwarding member" begin
    e = thrown(:(msz2(::Outer) = UInt(5)))
    @test e isa ImplementError && occursin("forwarding", msg(e))
    @test latest(msz2, Outer(Inner(4))) === 4 && latest(via2, Outer(Inner(4))) === 4
    @test thrown(:(@implement Meas2 Outer by i)) === nothing   # a redeclaration defines them anew
end

## a member of two traits that share an operation
@trait TwoA begin
    sh(x::TwoA)::Int
end
@trait TwoB begin
    sh(x::TwoB)::Integer
end
struct MD end
sh(::MD) = 1
@implement TwoA MD

@testset "the second trait's block" begin
    e = thrown(:(@implement TwoB MD begin
        sh(::MD) = UInt(1)
    end))
    @test e isa ImplementError                               # TwoA's check of sh at MD holds
    @test latest(sh, MD()) === 1
    @test thrown(:(@implement TwoB MD)) === nothing
end

## a membership redeclared with a block; a trait redeclared
@trait Meas4 begin
    m4(x::Meas4)::Integer
end
struct ME end
m4(::ME) = 1
@implement Meas4 ME

@testset "redeclarations" begin
    @test thrown(:(@implement Meas4 ME begin
        m4(::ME) = Int8(7)
    end)) === nothing
    @test latest(m4, ME()) === Int8(7)
    @test nrecords(m4, ME) == 1                              # the old membership's record forgotten
    @test thrown(:(m4(::ME) = 1.5)) isa ImplementError
    # the trait redeclared as a new type: the old type's members keep no record
    @test thrown(:(@trait Meas4 begin
        m4(x::Meas4)::Real
    end)) === nothing
    @test thrown(:(m4(::ME) = 1.5)) === nothing
    @test latest(m4, ME()) === 1.5
    @test thrown(:(@implement Meas4 ME)) === nothing        # a member of the new type, checked anew
    @test thrown(:(m4(::ME) = "x")) isa ImplementError
end
