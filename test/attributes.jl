# `Compiled` and `Dynamic` (traits reference §6.6, §3.8, §9, §10; lowering §5, §8.2, §13): every value
# in trait code is one or the other, decided where a plain value enters, kept inside the trait world.
# A mode chooses speed, never results. Runs inside runtests.jl, or alone: julia --project=. test/attributes.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module AttrG
    using TraitWorld
    export Shape, area, kind, kind_d, kind_c, pass, with_dyn, comp_of, atotal, kwkind, vkind,
           Visitor, visit, doit, PF, getd, setd!, SV, first_of, first_dyn, Model, mval, mkind, MyModel,
           cm, cm_c, cm_kind, cmc_kind, AFBox
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
        @dynamic
        mval(m::Model)::Int
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
    # item positions (traits reference §10.2): each item's attribute when it is read
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
        # a bounded keyword from an untyped caller: the keyword sorter is specialized on the named tuple of
        # keywords, so `known_type` sees the value's type there (traits T-47)
        @test_broken a_kw_untyped(v) === :dynamic
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
    @testset "a trait's default, @dynamic (rule 3): not for types of the trait world" begin
        @test a_m_user(AUserModel(1)) === :dynamic
        @test a_m_tw(AttrG.MyModel(1)) === :compiled
        @test a_m_cf(AUserModel(1)) === :compiled
        @test AttrG.mval(Dynamic{AttrG.Model}(AUserModel(3))) == 3
    end
    @testset "Callable: @dynamic, Compiled{Callable}, conversions, Dynamic{Callable}" begin
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
    @testset "stored functions: the caller's conversion decides (traits §9)" begin
        C = Callable{Tuple{Float64}, Float64}
        sq(x) = x^2
        d = stored(C, sq)
        @test d isa Dynamic{C} && d(3.0) == 9.0                        # Callable's default: Dynamic
        @test stored(C, compiled_for(sq)) === sq                       # Compiled: the function itself
        @test stored(C, with_dynamic(sq)) isa Dynamic{C}
        @test stored(C, d) === d                                       # a stored function of the signature carries
        @test_throws TraitBoundError stored(C, Dynamic{Callable{Tuple{Int}, Int}}(sq))   # another signature: refused
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
