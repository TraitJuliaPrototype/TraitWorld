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
