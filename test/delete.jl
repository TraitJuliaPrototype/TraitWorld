# Taking a membership back (traits §5.13; facts §10; compiler §4.3, §5.5, §5.6; W-155, D-13): as a method's
# deletion. From the next world on the type is no member; the code that relied on the membership is
# compiled again (a call that selected a method at the trait, an `isa` that folded true, code compiled at
# the member for the trait); a call that reached the member's own method keeps its code; a task in an
# older world keeps the membership; the member's check and records are forgotten.
using TraitWorld, Test

latest(f, args...) = Base.invokelatest(f, args...)
G(m::Symbol, n::Symbol) = Base.invokelatest(getglobal, getglobal(Main, m), n)
toplevel(q) = Core.eval(Main, Expr(:toplevel, q.args...))
function thrown(ex)
    try
        Core.eval(Main, ex)
        return nothing
    catch e
        while e isa LoadError; e = e.error; end
        return e
    end
end
# the valid CodeInstance compiled by facts for `f` at the argument types `T`, or nothing
function code_of(f, T)
    for m in methods(f), mi in Base.specializations(m)
        (mi isa Core.MethodInstance && mi.specTypes === Tuple{typeof(f), T.parameters...} && isdefined(mi, :cache)) || continue
        ci = mi.cache
        while true
            ci.max_world == typemax(UInt) && (ci.flags & 0x20) != 0 && return ci
            isdefined(ci, :next) || break; ci = ci.next
        end
    end
    return nothing
end

toplevel(quote
    module DShapes
    using TraitWorld
    @trait_module bounded = false
    @trait DShape begin
        darea(s::DShape)::Float64
        dname(s::DShape)::String = "shape"        # a default: a method at the trait
    end
    struct Circ; r::Float64; end
    darea(c::Circ) = 3.0 * c.r^2
    @implement DShape Circ
    describe(s::DShape) = "a shape"                # a method at the trait
    describe(x) = "other"
    isshape(x) = x isa DShape
    callarea(c::Circ) = darea(c)                   # the member's own method
    calldesc(c::Circ) = describe(c)                # a method at the trait, selected at the member
    callname(c::Circ) = dname(c)                   # the default's method, compiled at the member
    callisshape(c::Circ) = isshape(c)
    struct Sq <: DShape; a::Float64; end           # a member by its definition
    darea(s::Sq) = s.a^2
    @implement DShape Sq
    end
    module DThird                                  # owns neither the trait nor the types
    using TraitWorld
    end
end)

@testset "a membership taken back" begin
    DS = getglobal(Main, :DShapes)
    DShape, Circ, Sq = DS.DShape, DS.Circ, DS.Sq
    c = Circ(1.0)
    @test latest(<:, Circ, DShape) && latest(DS.callisshape, c)
    @test latest(DS.calldesc, c) == "a shape" && latest(DS.callname, c) == "shape" && latest(DS.callarea, c) == 3.0
    @test Circ in ccall(:jl_candidates_of, Any, (Any,), DShape)
    area_code = code_of(DS.callarea, Tuple{Circ})
    desc_code, name_code, isa_code = code_of(DS.calldesc, Tuple{Circ}), code_of(DS.callname, Tuple{Circ}), code_of(DS.callisshape, Tuple{Circ})
    @test area_code !== nothing && desc_code !== nothing && name_code !== nothing && isa_code !== nothing
    w = Base.get_world_counter()

    # what cannot be taken back alone
    @test_throws ImplementError delete_membership(DShape, Sq)              # a member by its definition
    @test_throws ImplementError delete_membership(DShape, Dynamic{DShape})  # the box's
    @test_throws ImplementError delete_membership(DShape, Int)              # no such membership

    delete_membership(DShape, Circ)
    # from the next world on, Circ is no member
    @test !latest(<:, Circ, DShape) && !latest(isa, c, DShape)
    @test !latest(DS.callisshape, c)                                         # the folded positive ended
    @test latest(DS.calldesc, c) == "other"                                  # the selection at the member changed
    @test_throws MethodError latest(DS.callname, c)                          # the default no longer applies
    @test latest(DS.callarea, c) == 3.0                                      # the member's own method stays
    @test isa_code.max_world < typemax(UInt) && desc_code.max_world < typemax(UInt) && name_code.max_world < typemax(UInt)
    @test area_code.max_world == typemax(UInt)                               # its code was not compiled again
    @test !(Circ in ccall(:jl_candidates_of, Any, (Any,), DShape))
    # a task in an older world keeps the membership
    @test Base.invoke_in_world(w, isa, c, DShape)
    @test Base.invoke_in_world(w, DS.calldesc, c) == "a shape"
    # values stored before stay; a call on them dispatches by type
    v = DShape[]
    @test_throws MethodError push!(v, c)

    # declared again: a new declaration, checked as any
    Core.eval(DS, :(@implement DShape Circ))
    @test latest(<:, Circ, DShape) && latest(DS.callisshape, c) && latest(DS.calldesc, c) == "a shape"
    @test latest(DS.callname, c) == "shape"

    # by neither owner: a pirate's, followed with a warning; refused in strict mode where code compiled by facts relies on it
    DT = getglobal(Main, :DThird)
    TraitWorld.strict!(true)
    try
        @test latest(DS.callisshape, c)
        @test_throws PirateError delete_membership(DShape, Circ; by = DT)
        @test latest(<:, Circ, DShape)
        delete_membership(DShape, Circ)                                      # the owner's: followed
        @test !latest(<:, Circ, DShape)
    finally
        TraitWorld.strict!(false)
    end
    Core.eval(DS, :(@implement DShape Circ))
    @test_logs (:warn, r"a pirate's") match_mode = :any delete_membership(DShape, Circ; by = DT)
    @test !latest(<:, Circ, DShape)
    Core.eval(DS, :(@implement DShape Circ))
    @test latest(<:, Circ, DShape)
end
