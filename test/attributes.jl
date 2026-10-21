# `Compiled` and `Dynamic` (traits reference §6, §6.3, §5.8, §7; lowering §5, §8.2, §13): every value
# in trait code is one or the other, decided where a plain value enters, kept inside the trait world.
# A mode chooses speed, never results. Runs inside runtests.jl, or alone: julia --project=. test/attributes.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module AttrG
    using TraitWorld
    export Shape, area, kind, kind_d, kind_c, pass, with_dyn, comp_of, atotal, kwkind, vkind,
           Visitor, visit, doit, PF, getd, setd!, SV, first_of, first_dyn, Model, mval, mkind, MyModel,
           cm, cm_c, cm_kind, cmc_kind, AFBox, Hotm, hval, hkind, hkind_d, hkinds, HBox
    public kind_hidden
    @trait Shape begin
        area(s::Shape)::Float64
    end
    kind(s::Shape) = TraitWorld.is_dynamic(s) ? :dynamic : :compiled
    kind_d(s::Dynamic{Shape}) = TraitWorld.is_dynamic(s) ? :dynamic : :compiled
    kind_c(s::Compiled{Shape}) = TraitWorld.is_dynamic(s) ? :dynamic : :compiled
    pass(s::Shape) = (kind(s), area(s))                 # a value keeps its attribute from worker to worker
    with_dyn(s::Shape) = kind(with_dynamic(s))
    comp_of(s::Dynamic{Shape}) = kind(compiled_for(s))
    atotal(s::Shape) = 2 * area(s)
    kwkind(t::Shape; s::Shape) = kind(s)   # (with no bounded positional argument, the entry and the worker collide: a known gap)
    vkind(ss::Shape...) = kind(ss[1])

    @trait Visitor begin
        visit(v::Visitor, s::Dynamic{Shape})::Float64   # an operation's argument declared `Dynamic`: a type
    end
    doit(v::Visitor, s::Shape) = visit(v, s)            # a trait object passed there is converted

    @trait PF begin
        @const data::Vector{Float64}
        label::String
    end
    getd(t::PF) = t.data
    setd!(t::PF, s::String) = (t.label = s; nothing)

    @trait SV{T} begin
        @const u::Vector{T}
    end
    first_of(s::SV) = s.u[1]
    first_dyn(s::Dynamic{SV{Float64}}) = s.u[1]

    @trait Model begin
        @default_with_dynamic_self
        mval(m::Model)::Int
    end
    @trait Hotm begin
        @default_compiled_for_self
        hval(h::Hotm)::Int
    end
    hkind(h::Hotm) = TraitWorld.is_dynamic(h) ? :dynamic : :compiled
    hkind_d(h::Dynamic{Hotm}) = hkind(h)
    hkinds(hs::Iterable{Hotm}) = (r = Symbol[]; for h in hs; push!(r, hkind(h)); end; r)
    struct HBox{H <: Hotm}
        h::H
    end
    mkind(m::Model) = TraitWorld.is_dynamic(m) ? :dynamic : :compiled
    struct MyModel; k::Int; end                      # a type of the trait world: its own module's
    TraitWorld.@implement Model MyModel begin mval(m) = m.k end

    cm(f::Callable{Tuple{Float64},Float64}, x::Float64) = f(x)
    cm_c(f::Compiled{Callable{Tuple{Float64},Float64}}, x::Float64) = f(x)
    cm_kind(f::Callable{Tuple{Float64},Float64}) = TraitWorld.is_dynamic(f) ? :dynamic : :compiled
    cmc_kind(f::Compiled{Callable{Tuple{Float64},Float64}}) = TraitWorld.is_dynamic(f) ? :dynamic : :compiled

    struct AFBox
        f::Dynamic{Callable{Tuple{Float64},Float64}}
    end
    kind_hidden(s::Dynamic{Shape}) = TraitWorld.is_dynamic(s) ? :dynamic : :compiled
    # item positions (traits reference §8.2): each item's attribute when it is read
    ikinds(ms::Iterable{Shape}) = (r = Symbol[]; for m in ms; push!(r, kind(m)); end; r)
    ikinds_c(ms::Iterable{Compiled{Shape}}) = (r = Symbol[]; for m in ms; push!(r, kind(m)); end; r)
    ikinds_d(ms::Iterable{Dynamic{Shape}}) = (r = Symbol[]; for m in ms; push!(r, kind(m)); end; r)
    iarea(ms::Iterable{Shape}) = (s = 0.0; for m in ms; s += area(m); end; s)
    kkind(d::Keyed{String, Shape}, k::String) = kind(d[k])
    export ikinds, ikinds_c, ikinds_d, iarea, kkind
    end
end)

toplevel(quote
    using .AttrG
    struct ACircle; r::Float64; end
    struct ASquare; s::Float64; end
    TraitWorld.@implement AttrG.Shape ACircle begin area(c) = pi * c.r^2 end
    TraitWorld.@implement AttrG.Shape ASquare begin area(q) = q.s^2 end
    struct AVisit; w::Float64; end
    TraitWorld.@implement AttrG.Visitor AVisit begin visit(v, s) = v.w * area(s) end
    mutable struct APF; data::Vector{Float64}; label::String; end
    TraitWorld.@implement AttrG.PF APF
    struct ASV; u::Vector{Float64}; end
    TraitWorld.@implement AttrG.SV ASV
    struct AUserModel; k::Int; end
    TraitWorld.@implement AttrG.Model AUserModel begin mval(m) = m.k end
    struct AHot; k::Int; end
    TraitWorld.@implement AttrG.Hotm AHot begin hval(h) = h.k end

    # callers that know the type, and callers that do not
    a_typed(c::ACircle) = kind(c)
    a_untyped(v::Vector{Any}) = kind(v[1])
    a_d_typed(c::ACircle) = kind_d(c)
    a_c_untyped(v::Vector{Any}) = kind_c(v[1])
    a_pass_typed(c::ACircle) = pass(c)
    a_pass_untyped(v::Vector{Any}) = pass(v[1])
    a_cf_untyped(v::Vector{Any}) = kind(compiled_for(v[1]))
    a_wd_typed(c::ACircle) = kind(with_dynamic(c))
    a_dyn_typed(d::Dynamic{AttrG.Shape}) = kind(d)
    a_kw_typed(c::ACircle) = kwkind(c; s = c)
    a_kw_untyped(v::Vector{Any}) = kwkind(ACircle(1.0); s = v[1])
    a_va_typed(c::ACircle) = vkind(c, c)
    a_va_untyped(v::Vector{Any}) = vkind(v[1])
    a_m_user(m::AUserModel) = mkind(m)
    a_h_d(h::AHot) = AttrG.hkind_d(h)
    a_m_tw(m::AttrG.MyModel) = mkind(m)
    a_m_cf(m::AUserModel) = mkind(compiled_for(m))
    a_cm_closure(r::Float64) = cm_kind(x -> r * x)
    a_cm_abs2(x::Float64) = cm_kind(abs2)
    a_cm_cf(r::Float64) = cm_kind(compiled_for(x -> r * x))
    a_cmc_closure(r::Float64) = cmc_kind(x -> r * x)
    a_cmc_wd(x::Float64) = cmc_kind(with_dynamic(abs2))
end)

@testset "Compiled and Dynamic" begin
    c = ACircle(1.0)
    v = Any[c]
    @testset "the type the caller knows decides (rule 2)" begin
        @test a_typed(c) === :compiled
        @test a_untyped(v) === :dynamic
        @test Core.eval(Main, :(kind($c))) === :dynamic            # the prompt knows no types
    end
    @testset "an attribute at the position overrides (rule 4)" begin
        @test a_d_typed(c) === :dynamic
        @test a_c_untyped(v) === :compiled
    end
    @testset "values keep their attribute; results never change" begin
        @test a_pass_typed(c) == (:compiled, Float64(pi))
        @test a_pass_untyped(v) == (:dynamic, Float64(pi))
        @test a_dyn_typed(Dynamic{AttrG.Shape}(c)) === :dynamic         # a Dynamic is never opened at a bound
        @test atotal(ASquare(2.0)) == 8.0 && a_untyped(Any[ASquare(2.0)]) === :dynamic
    end
    @testset "conversions always win (rule 5)" begin
        @test a_cf_untyped(v) === :compiled
        @test a_wd_typed(c) === :dynamic
        @test AttrG.with_dyn(c) === :dynamic                              # inside trait code
        @test AttrG.comp_of(c) === :compiled
    end
    @testset "keywords and varargs" begin
        @test a_kw_typed(c) === :compiled
        # a bounded keyword from an untyped caller: Dynamic (the entry's keyword sorter takes the keywords unspecialized)
        @test a_kw_untyped(v) === :dynamic
        @test a_va_typed(c) === :compiled
        @test a_va_untyped(v) === :dynamic
    end
    @testset "an operation's argument declared Dynamic{Y}: the seam" begin
        @test doit(AVisit(2.0), ASquare(3.0)) == 18.0
        @test doit(AVisit(2.0), Any[ASquare(3.0)][1]) == 18.0
    end
    @testset "declared fields at the erased key: typed" begin
        x = APF([1.0, 2.0], "a")
        @test getd(Any[x][1]) == [1.0, 2.0]
        setd!(Any[x][1], "b"); @test x.label == "b"
        d = Dynamic{AttrG.PF}(x)
        @test (@inferred (q -> q.data)(d)) == [1.0, 2.0]
        d.label = "c"; @test x.label == "c"
    end
    @testset "parameters: carried by the erased key; a Dynamic attribute must fix them" begin
        s = ASV([4.0, 5.0])
        @test first_of(Any[s][1]) === 4.0
        @test first_dyn(s) === 4.0
        err = try
            toplevel(quote
                @trait_module module AttrBad
                using TraitWorld, ..AttrG
                bad(s::Dynamic{AttrG.SV}) = s.u[1]
                end
            end)
            nothing
        catch e
            e
        end
        @test err isa LoadError && err.error isa TraitBoundError         # refused when the method is defined
    end
    @testset "a trait's default, @default_compiled_for_self: Compiled whatever the caller knew" begin
        h = AHot(2)
        @test Core.eval(Main, :(AttrG.hkind(AHot(2)))) === :compiled            # at the prompt, too
        @test AttrG.hkind(with_dynamic(h)) === :dynamic                          # a cast wins
        @test a_h_d(h) === :dynamic                                              # an annotation wins
        @test AttrG.hkinds(Any[h, AHot(3)]) == [:compiled, :compiled]            # plain items of a Vector{Any}
        @test getfield(Kept{AttrG.Hotm}(h), :compiled)
        @test typeof(Core.eval(Main, :(AttrG.HBox(AHot(2))))).parameters[1] === AHot   # a struct parameter: the value itself
        err = try
            toplevel(quote
                @trait_module module AttrOld
                using TraitWorld
                @trait OldD begin
                    @dynamic
                    oval(o::OldD)::Int
                end
                end
            end)
            nothing
        catch e
            e
        end
        @test err isa LoadError                                                  # the old spelling is refused
    end
    @testset "a trait's default, @default_with_dynamic_self (rule 3): not for types of the trait world" begin
        @test a_m_user(AUserModel(1)) === :dynamic
        @test a_m_tw(AttrG.MyModel(1)) === :compiled
        @test a_m_cf(AUserModel(1)) === :compiled
        @test AttrG.mval(Dynamic{AttrG.Model}(AUserModel(3))) == 3
    end
    @testset "Callable: its Dynamic default, Compiled{Callable}, casts, Dynamic{Callable}" begin
        @test a_cm_closure(2.0) === :dynamic
        @test a_cm_abs2(2.0) === :compiled                            # a function of the trait world, its type known
        @test Core.eval(Main, :(cm_kind(abs2))) === :dynamic          # at the prompt
        @test a_cm_cf(2.0) === :compiled
        @test a_cmc_closure(2.0) === :compiled
        @test a_cmc_wd(2.0) === :dynamic
        @test cm(x -> 3x, 2.0) == 6.0 && cm_c(x -> 3x, 2.0) == 6.0
        b = AFBox(Dynamic{Callable{Tuple{Float64},Float64}}(x -> x + 1))
        @test b.f(1.0) == 2.0
        @test cm(b.f, 1.0) == 2.0 && cm_kind(b.f) === :dynamic
        @test_throws MethodError b.f(1)                               # the signature is checked
    end
    @testset "items: each item's attribute when it is read" begin
        cs = [ACircle(1.0), ACircle(2.0)]
        as = Any[ACircle(1.0), ASquare(2.0)]
        @test ikinds(cs) == [:compiled, :compiled]                     # a concrete item type: Compiled
        @test ikinds(as) == [:dynamic, :dynamic]                       # an abstract one: Dynamic
        @test ikinds_c(as) == [:compiled, :compiled]                   # `Iterable{Compiled{Shape}}`: each opened when read
        @test ikinds_d(cs) == [:dynamic, :dynamic]                     # `Iterable{Dynamic{Shape}}`
        ds = Dynamic{AttrG.Shape}[Dynamic{AttrG.Shape}(c) for c in cs]
        @test ikinds_c(ds) == [:dynamic, :dynamic]                     # stored Dynamic items carry their attribute
        @test iarea(cs) == iarea(Any[cs...]) == iarea(ds) == 5pi        # results never change
        @test kkind(Dict("a" => ACircle(1.0)), "a") === :compiled
        @test kkind(Dict{String, Any}("a" => ACircle(1.0)), "a") === :dynamic
        @test_throws TraitBoundError ikinds_c(Any[ACircle(1.0), 1])     # an item that does not conform: when read
    end
    @testset "functions held: Compiled, Dynamic, Kept; constructors never cast (traits §5.8)" begin
        C = Callable{Tuple{Float64}, Float64}
        sq(x) = x^2
        d = Dynamic{C}(sq); c = Compiled{C}(sq)
        @test d(3.0) == 9.0 && c(3.0) == 9.0
        @test getfield(c, :t) === sq                                   # Compiled: the function itself
        @test compiled_for(d) isa Compiled{C} && getfield(compiled_for(d), :t) === sq
        @test with_dynamic(c) isa Dynamic{C} && with_dynamic(c)(2.0) == 4.0
        @test_throws TraitBoundError Dynamic{C}(compiled_for(sq))      # only a cast changes an attribute
        @test_throws TraitBoundError Dynamic{C}(c)
        @test_throws TraitBoundError Compiled{C}(d)
        @test getfield(Kept{C}(sq), :compiled) === false              # a plain function: Callable's default
        @test getfield(Kept{C}(c), :compiled) === true && Kept{C}(c)(2.0) == 4.0
        @test cm_kind(c) === :compiled && cm_kind(d) === :dynamic       # at a bound: carried
        @test cm_kind(Kept{C}(c)) === :compiled && cm_kind(Kept{C}(d)) === :dynamic
        @test cm_kind(Dynamic{Callable{Tuple{Int}, Int}}(sq)) === :dynamic   # another signature: the same function
        @test cm(Dynamic{Callable{Tuple{Int}, Int}}(sq), 3.0) == 9.0
        @test c == d && hash(c) == hash(d)                             # one function, whatever its attribute
    end
    @testset "an attribute on a function neither exported nor public warns (rule 8)" begin
        @test_logs (:warn, r"neither exported nor public") match_mode = :any toplevel(quote
            @trait_module module AttrHidden
            using TraitWorld, ..AttrG
            hidden(s::Dynamic{AttrG.Shape}) = 1.0
            end
        end)
    end
end

# an attribute on several bounds (traits reference §5.1): `Dynamic{(X, Y)}`, `Compiled{(X, Y)}`
toplevel(quote
    @trait_module module AttrSeveral
    using TraitWorld
    export PA, pa, PB, pb, both_d, both_c, both
    @trait PA begin
        pa(x::PA)::Float64
    end
    @trait PB begin
        pb(x::PB)::Float64
    end
    both(t::(PA, PB)) = (TraitWorld.is_dynamic(t) ? :dynamic : :compiled, pa(t) + pb(t))
    both_d(t::Dynamic{(PA, PB)}) = both(t)
    both_c(t::Compiled{(PA, PB)}) = both(t)
    end
end)
using .AttrSeveral
struct PAB; a::Float64; b::Float64; end
AttrSeveral.pa(x::PAB) = x.a
AttrSeveral.pb(x::PAB) = x.b
@implement (PA, PB) PAB

@testset "an attribute on several bounds" begin
    S = Main.AttrSeveral
    fd(x::PAB) = AttrSeveral.both_d(x)           # from typed callers
    fc(x::PAB) = AttrSeveral.both_c(x)
    fb(x::PAB) = AttrSeveral.both(x)
    @test fd(PAB(1.0, 2.0)) == (:dynamic, 3.0)
    @test fc(PAB(1.0, 2.0)) == (:compiled, 3.0)
    @test fb(PAB(1.0, 2.0)) == (:compiled, 3.0)
    @test S.both_c(with_dynamic(PAB(1.0, 2.0)))[1] === :dynamic       # the cast wins
end

# an operation on a `Dynamic` is typed by the declared result at the parameters it fixes (lowering §13)
toplevel(quote
    @trait_module module DynTyped
    using TraitWorld
    export SVt, sfirst, slen, sfirst_d
    @trait SVt{T} begin
        T = eltype(Self)
        sfirst(v::SVt{T})::T
        slen(v::SVt)::Int
    end
    @implement SVt A where {A <: Vector{<:Real}} begin
        sfirst(v) = v[1]
        slen(v) = length(v)
    end
    sfirst_d(v::Dynamic{SVt{Float64}}) = sfirst(v) + 1.0
    end
end)

@testset "a Dynamic's operations typed by its fixed parameters" begin
    D = Main.DynTyped
    d = Dynamic{D.SVt{Float64}}([2.0, 3.0])
    @test D.sfirst(d) === 2.0 && D.slen(d) === 2
    @test Base.return_types(D.sfirst, (typeof(d),)) == [Float64]
    @test Base.return_types(D.slen, (typeof(d),)) == [Int]
    @test D.sfirst_d([2.0]) === 3.0
end

# a declared type that applies a type constructor bounding its parameter (`DEdge{T <: Integer}`) to the
# trait's parameter, on a `Dynamic` (traits §5.2, the same results; lowering §13): at the bound the
# operation is typed at the parameters the trait object carries; on a `Dynamic` that leaves the
# parameter open the type is unknown (`Any`), never formed with the open parameter
toplevel(quote
    module DynEdgeDecl
    using TraitWorld
    export DEdge, DEdges, dnv, dedges, dhas
    struct DEdge{T <: Integer}; s::T; d::T; end
    @trait DEdges{V <: Integer} begin
        dnv(g::DEdges{V})::V
        dedges(g::DEdges{V})::Vector{DEdge{V}}
        dhas(g::DEdges{V}, e::DEdge{V})::Bool
        e0::DEdge{V}                              # the field defines `V`
    end
    end
    using .DynEdgeDecl
    mutable struct DGraph{T <: Integer}; n::T; e0::DEdge{T}; end   # `e0` is a writable field
    DynEdgeDecl.dnv(g::DGraph) = g.n
    DynEdgeDecl.dedges(g::DGraph{T}) where {T} = [g.e0, DEdge{T}(one(T), g.n)]
    DynEdgeDecl.dhas(g::DGraph{T}, e::DEdge{T}) where {T} = e in DynEdgeDecl.dedges(g)
    @implement DEdges G where {G <: DGraph}
    @trait_module module DynEdge
    using TraitWorld, ..DynEdgeDecl
    eb(g::DEdges) = (es = dedges(g); (dnv(g), length(es), es[end].d, dhas(g, es[1]), g.e0))
    ew(g::DEdges{V}) where {V} = (es = dedges(g); (dnv(g) + one(V), es[end]))
    ef(g::DEdges{Int}) = dedges(g)
    end
end)

@testset "a Dynamic's operations: a parameter-bounded type constructor in a declared type" begin
    D, E = Main.DynEdge, Main.DynEdgeDecl
    g = Main.DGraph(3, E.DEdge(1, 2))
    g32 = Main.DGraph(Int32(3), E.DEdge{Int32}(1, 2))
    # at a bound: the same results as Compiled, typed at the parameter the trait object carries
    @test D.eb(with_dynamic(g)) == D.eb(compiled_for(g)) == (3, 2, 3, true, E.DEdge(1, 2))
    @test D.ew(with_dynamic(g32)) == D.ew(compiled_for(g32)) == (Int32(4), E.DEdge{Int32}(1, 3))
    @test D.ew(with_dynamic(g32))[2] isa E.DEdge{Int32}
    @test D.ef(with_dynamic(g)) isa Vector{E.DEdge{Int}}
    # a Dynamic fixing the parameter: typed by it
    df = Dynamic{E.DEdges{Int}}(g)
    @test E.dedges(df) == [E.DEdge(1, 2), E.DEdge(1, 3)] && df.e0 === E.DEdge(1, 2)
    @test Base.return_types(E.dedges, (typeof(df),)) == [Vector{E.DEdge{Int}}]
    @test Base.return_types(d -> d.e0, (typeof(df),)) == [E.DEdge{Int}]
    # a Dynamic leaving it open: the results, typed `Any` (the declared type names an open parameter)
    d = Dynamic{E.DEdges}(g)
    @test E.dedges(d) == [E.DEdge(1, 2), E.DEdge(1, 3)] && E.dnv(d) === 3 && d.e0 === E.DEdge(1, 2)
    @test E.dhas(d, E.DEdge(1, 3)) && !E.dhas(d, E.DEdge(2, 3))
    @test Base.return_types(E.dedges, (typeof(d),)) == [Any]
    @test Base.return_types(E.dhas, (typeof(d), E.DEdge{Int})) == [Bool]
end
