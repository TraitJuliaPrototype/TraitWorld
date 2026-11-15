# Owner-only functions (traits §6.8, §12.2; facts §1, §3; compiler §1.2; W-155, D-9): a trait module's
# functions that it neither exports nor declares public, and those it declares `@owner_only`, take
# methods from it only. A call of one is a fact at any signature; a method of one by another package is a
# pirate's, whatever types it names: reported by default, refused in strict mode.
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
# the code compiled by facts for `f` at `T`, valid in the latest world: its result type and its G2 bit
function code_of(f, T)
    for m in methods(f), mi in Base.specializations(m)
        (mi isa Core.MethodInstance && mi.specTypes === Tuple{typeof(f), T.parameters...} && isdefined(mi, :cache)) || continue
        ci = mi.cache
        while true
            ci.max_world == typemax(UInt) && (ci.flags & 0x20) != 0 && return (ci.rettype, (ci.flags & 0x10) != 0)
            isdefined(ci, :next) || break; ci = ci.next
        end
    end
    return nothing
end

toplevel(quote
    module OOLib
    using TraitWorld
    @trait_module
    export pubf, decl
    helper(x) = 1                             # internal: owner-only by the trait module's default
    pubf(x) = 2                               # exported: others may extend it
    decl(x) = 3                               # exported, and declared owner-only
    @owner_only decl
    useall(v::Vector{Any}) = helper(v[1]) + 1
    usepub(v::Vector{Any}) = pubf(v[1])
    end
    module OOThird
    import ..OOLib
    struct T end
    end
end)

@testset "owner-only functions" begin
    OOLib, OOThird = getglobal(Main, :OOLib), getglobal(Main, :OOThird)
    CC = Base.Compiler
    @test CC.is_owner_only(typeof(OOLib.helper))
    @test !CC.is_owner_only(typeof(OOLib.pubf))
    @test CC.is_owner_only(typeof(OOLib.decl))
    @test !CC.is_owner_only(typeof(sum))                     # Base's functions are not
    @test CC.is_fact_sig(Tuple{typeof(OOLib.helper), Any})
    @test !CC.is_fact_sig(Tuple{typeof(OOLib.pubf), Any})

    # a call of an owner-only function at an abstract signature is inferred: a fact, in the deep class
    v = Any[1.0]
    @test latest(OOLib.useall, v) == 2 && latest(OOLib.usepub, v) == 2
    rt, deep = code_of(OOLib.useall, Tuple{Vector{Any}})
    @test rt === Int && deep
    @test code_of(OOLib.usepub, Tuple{Vector{Any}})[1] === Any       # a run-time site

    # another package's method of it is a pirate's, at the package's own type too
    T3 = G(:OOThird, :T)
    @eval OOThird OOLib.helper(x::T) = 10
    m = latest(which, OOLib.helper, (T3,))
    @test !TraitWorld.owned_method(m)
    @test TraitWorld.sig_owners(Tuple{typeof(OOLib.helper), T3}) == Base.IdSet{Any}([OOLib])
    @eval OOThird OOLib.pubf(x::T) = 20                       # at an exported function: no pirate
    m2 = latest(which, OOLib.pubf, (T3,))
    @test TraitWorld.owned_method(m2)
    @eval OOThird OOLib.decl(x::T) = 30                       # at a declared one: a pirate
    m3 = latest(which, OOLib.decl, (T3,))
    @test !TraitWorld.owned_method(m3)
    foreach(Base.delete_method, (m, m2, m3))

    # by default it is followed, and reported where it ends code in the deep class
    @test latest(OOLib.useall, v) == 2
    n = length(TraitWorld.PIRATE_REPORTS)
    @test_logs (:warn, r"a pirate ended code compiled by facts.*helper.*OOLib\.useall") match_mode = :any @eval OOThird OOLib.helper(x::Float64) = 100
    @test length(TraitWorld.PIRATE_REPORTS) == n + 1
    @test latest(OOLib.useall, v) == 101
    Base.delete_method(latest(which, OOLib.helper, (Float64,)))
    @test latest(OOLib.useall, v) == 2

    # in strict mode it is refused where it would win at a fact of code compiled by facts
    TraitWorld.strict!(true)
    try
        e = thrown(:(@eval OOThird OOLib.helper(x::Float64) = 100))
        @test e isa PirateError
        @test latest(OOLib.useall, v) == 2
        # the owner's own method is a stakeholder's change: followed
        @test thrown(:(@eval OOLib helper(x::Float64) = 5)) === nothing
        @test latest(OOLib.useall, v) == 6
    finally
        TraitWorld.strict!(false)
    end
end
