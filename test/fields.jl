# Trait fields (note "Declaring a trait": fields are properties, writable unless const;
# a field of type R names the projection and is a lens) and kept values that follow
# the user's fields (note "Dynamic values"), shaped like an integrator's fields.
# Runs inside runtests.jl, or alone: julia --project=. test/fields.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module FieldSolv
    using TraitWorld
    export Stepper, advance!, twice!, nudge!, keepstep, Buffer, total, swap!, readtotal, Series3, amount, keepseries

    @trait Stepper{R} begin
        @const t::Float64             # read-only
        dt::Float64                   # writable
        advance!(r::R)::Nothing
    end
    twice!(s::Stepper) = (advance!(s); advance!(s); s.t)
    nudge!(s::Stepper, x::Float64) = (s.dt = x; s.dt)
    keepstep(s::Stepper) = Dynamic{Stepper}(s)

    @trait Buffer{R} begin
        data::R                       # the projection field, writable: a lens
        total(r::R)::Float64
    end
    @implement Buffer{Vector{Float64}} begin
        total(r) = sum(r)
    end
    swap!(b::Buffer, v::Vector{Float64}) = (b.data = v; total(b))
    readtotal(b::Buffer) = total(b)

    @trait Series3{R} begin
        amount(r::R)::Float64
    end
    @implement Series3{Vector{Float64}} begin
        amount(r) = sum(r)
    end
    keepseries(s::Series3) = Dynamic{Series3}(s)
    end
    using .FieldSolv

    @trait_module module FieldBad
    using TraitWorld, ..FieldSolv
    export writeconst!, readsecret
    writeconst!(s::Stepper) = (s.t = 1.0; nothing)     # a const field written
    readsecret(s::Stepper) = s.secret                   # a field no trait declares
    end
    using .FieldBad
end)

toplevel(quote
    mutable struct Clock; t::Float64; dt::Float64; end
    FieldSolv.advance!(c::Clock) = (c.t += c.dt; nothing)
    @implement Stepper Clock                       # its own representation: fields are its own

    mutable struct Box; data::Vector{Float64}; tag::String; end
    @implement Buffer Box by data                  # Buffer declares `data` with its receiver type: a lens on Box's field

    mutable struct MBox; data::Vector{Float64}; end
    @implement Series3 MBox by data                # forwarding to a field of a mutable type
    struct IBox; data::Vector{Float64}; end
    @implement Series3 IBox by data                # immutable: its field cannot be rebound
end)

@testset "Trait fields and lenses" begin
    c = Main.Clock(0.0, 0.5)
    @test Main.FieldSolv.twice!(c) == 1.0
    @test Main.FieldSolv.nudge!(c, 0.25) == 0.25 && c.dt == 0.25
    @test_throws TraitUseError Main.FieldBad.writeconst!(c)
    @test_throws TraitUseError Main.FieldBad.readsecret(c)
    d = Main.FieldSolv.keepstep(c)
    @test d.t == c.t && d.dt == 0.25
    d.dt = 0.125                                   # a write through a kept value reaches the user's object
    @test c.dt == 0.125
    @test_throws ArgumentError (d.t = 3.0)

    b = Main.Box([1.0, 2.0], "x")
    @test Main.FieldSolv.readtotal(b) == 3.0
    @test Main.FieldSolv.swap!(b, [5.0]) == 5.0    # the user's field rebound, as `b.data = v` in plain Julia
    @test b.data == [5.0]

    m = Main.MBox([1.0])
    k = Main.FieldSolv.keepseries(m)
    m.data = [2.0, 3.0]                            # the user rebinds the field after the value was kept
    @test Main.FieldSolv.amount(k) == 5.0          # the kept value follows it
    i = Main.IBox([1.0, 2.0])
    @test Main.FieldSolv.amount(Main.FieldSolv.keepseries(i)) == 3.0

    # conformance refusals
    e1 = try toplevel(quote
        struct RClock; t::Float64; dt::Float64; end
        FieldSolv.advance!(c::RClock) = nothing
        @implement Stepper RClock
    end); nothing catch err; err end
    while e1 isa LoadError; e1 = e1.error; end
    @test e1 isa ImplementError && occursin("dt", sprint(showerror, e1))
    e2 = try toplevel(quote
        mutable struct IntClock; t::Int; dt::Float64; end
        FieldSolv.advance!(c::IntClock) = nothing
        @implement Stepper IntClock
    end); nothing catch err; err end
    while e2 isa LoadError; e2 = e2.error; end
    @test e2 isa ImplementError && occursin("`t`", sprint(showerror, e2))
    e3 = try toplevel(quote
        struct IBuf; data::Vector{Float64}; end
        @implement Buffer IBuf by data
    end); nothing catch err; err end
    while e3 isa LoadError; e3 = e3.error; end
    @test e3 isa ImplementError && occursin("mutable", sprint(showerror, e3))
    # a trait that declares a field with its receiver type is implemented with `by` too: no field is special
    e4 = try toplevel(quote
        struct NoBy; data::Vector{Float64}; tag::String; end
        @implement Buffer NoBy
    end); nothing catch err; err end
    while e4 isa LoadError; e4 = e4.error; end
    @test e4 isa ImplementError && occursin("by data", sprint(showerror, e4))

    @test isempty(check_definitions(Main.FieldSolv))
end

# a family member's declared fields are checked at its first use, as a single type's at its
# declaration (traits §4.7, §4.9; T-63, found by E-156 P9): a trait's write goes by pointer, so a
# `const` field must be refused before it is written
toplevel(quote
    @trait_module module FieldFam
    using TraitWorld
    export Flagged, setflag!
    @trait Flagged begin
        u_modified::Bool
    end
    setflag!(f::Flagged) = (f.u_modified = true; nothing)
    end
    using .FieldFam
    mutable struct FamGood{T}; x::T; u_modified::Bool; end
    mutable struct FamBad{T}; x::T; u_modified::Int; end
    mutable struct FamConst{T}; x::T; const u_modified::Bool; end
    struct FamMiss{T}; x::T; end
    @implement Flagged FamGood{T} where {T}
    @implement Flagged FamBad{T} where {T}
    @implement Flagged FamConst{T} where {T}
    @implement Flagged FamMiss{T} where {T}
end)
@testset "family members: declared fields checked at first use" begin
    firstuse(f) = try Base.invokelatest(f); nothing catch err
        while err isa LoadError || (hasfield(typeof(err), :error) && getfield(err, :error) isa Exception); err = getfield(err, :error); end
        err
    end
    g = FamGood(1, false)
    @test firstuse(() -> setflag!(g)) === nothing && g.u_modified
    c = FamConst(1, false)
    e = firstuse(() -> setflag!(c))
    @test e isa ImplementError && occursin("const", sprint(showerror, e))
    @test c.u_modified == false                          # the const field was not written
    e = firstuse(() -> setflag!(FamBad(1, 0)))
    @test e isa ImplementError && occursin("exactly that type", sprint(showerror, e))
    e = firstuse(() -> setflag!(FamMiss(1)))
    @test e isa ImplementError && occursin("no field", sprint(showerror, e))
end

# a dotted update of a declared field, `t.u .+= x`: Julia lowers it to `Base.dotgetproperty`,
# a read of the field (traits §5.3; T-65, found by E-156 P11)
toplevel(quote
    @trait_module module FieldDot
    using TraitWorld
    export Integ, bump!, bumpsecret!
    @trait Integ begin
        @const u::Vector{Float64}
        @const du::Vector{Float64}
    end
    bump!(i::Integ) = (i.u .+= i.du; i.u .*= 2.0; i.u[1])
    end
    using .FieldDot
    @trait_module module FieldDotBad
    using TraitWorld, ..FieldDot
    bumpsecret!(i::Integ) = (i.secret .+= 1.0; nothing)     # a field no trait declares
    end
    struct DotInteg; u::Vector{Float64}; du::Vector{Float64}; secret::Vector{Float64}; end
    @implement Integ DotInteg
end)
@testset "a dotted update of a declared field" begin
    @test isempty(check_definitions(Main.FieldDot))
    d = DotInteg([1.0], [2.0], [0.0])
    @test FieldDot.bump!(d) == 6.0 && d.u == [6.0]
    e = try check_definitions(Main.FieldDotBad); nothing catch err; err end
    @test e isa TraitUseError && occursin("secret", join(e.problems))
end
