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

# The messages at a method of another module's owner-only function (traits §11.3, §12.2): the function, why it is
# owner-only, its owner, that only the owner adds methods whatever types they are for, and what the owner writes to
# let others extend it; never that the definer owns no type in the signature, nor to define it where a type is owned.
@testset "the messages at an owner-only function's pirate" begin
    OOLib = getglobal(Main, :OOLib)
    msg(e) = sprint(showerror, e)
    v = Any[1]                                # (the testset above gave the owner a method at Float64)
    @test latest(OOLib.useall, v) == 2
    # in a trait module (`no_pirates`), at the module's own type: OwnershipError
    e = thrown(:(module OOMine
        using TraitWorld, ..OOLib
        @trait_module
        struct Mine end
        OOLib.helper(::Mine) = 0
        end))
    @test e isa OwnershipError
    @test occursin("helper(::Mine) in Main.OOMine is a pirate, and the scope declares `no_pirates`", msg(e))
    @test occursin("`helper` is an owner-only function of Main.OOLib (neither exported nor declared `public`)", msg(e))
    @test occursin("only Main.OOLib adds methods to it, whatever types they are for", msg(e))
    @test occursin("Main.OOLib declares it `public` or exports it, or names Main.OOMine a joint owner (`@joint_owners`)", msg(e))
    @test !occursin("owns neither", msg(e))
    # a function declared `@owner_only`, exported: what the owner writes is not `public`
    e = thrown(:(module OOMine2
        using TraitWorld, ..OOLib
        @trait_module
        struct Mine end
        OOLib.decl(::Mine) = 0
        end))
    @test e isa OwnershipError
    @test occursin("`decl` is an owner-only function of Main.OOLib (declared `@owner_only`)", msg(e))
    @test occursin("Main.OOLib does not declare it `@owner_only`", msg(e))
    # the classic pirate's names the owners
    e = thrown(:(module OOMine3
        using TraitWorld
        @trait_module
        Base.length(x::Vector{Int8}) = 0
        end))
    @test e isa OwnershipError
    @test occursin("Main.OOMine3 owns neither the function (owned by Julia) nor a type in each of its signatures (owned by Julia)", msg(e))
    # the report, by default
    logs, _ = Test.collect_test_logs() do
        @eval Main OOLib.helper(x::Float32) = 7
    end
    w = join((string(l.message) for l in logs if l.level == Base.CoreLogging.Warn), "\n")
    @test occursin("helper(::Float32)", w) && occursin("only Main.OOLib adds methods to it", w)
    @test !occursin("Define it where a type it is for is owned", w)
    Base.delete_method(latest(which, OOLib.helper, (Float32,)))
    @test latest(OOLib.useall, v) == 2
    # strict mode's PirateError: the method as a call, the same text
    TraitWorld.strict!(true)
    try
        e = thrown(:(@eval Main OOLib.helper(x::Float32) = 7))
        @test e isa PirateError
        @test occursin("strict mode refuses `helper(::Float32)`", msg(e))
        @test occursin("`helper` is an owner-only function of Main.OOLib", msg(e))
        @test occursin("Main.OOLib declares it `public` or exports it", msg(e))
        @test !occursin("Define it where a type it is for is owned", msg(e))
    finally
        TraitWorld.strict!(false)
    end
end
