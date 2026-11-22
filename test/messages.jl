# The messages' form (traits §11.3; E-362): a result outside the declared one is not called wider; a
# method refused for a member's check says the type stays a member; a use outside the contract names
# the field; an operation's method lies at the `@trait`; a bare option of `@trait_module` is on.
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
msg(e) = sprint(showerror, e)

module MsgLib
using TraitWorld
@trait_module bounded
@trait MShape begin
    marea(s::MShape)::Float64
    mname(s::MShape)::AbstractString
end
mdouble(s::MShape) = 2 * marea(s)
end
using .MsgLib: MShape, marea, mname, mdouble

@testset "the messages' form" begin
    @eval begin
        struct MInt; n::Int; end
        MsgLib.marea(s::MInt) = s.n
        MsgLib.mname(s::MInt) = "int"
    end
    e = thrown(:(@implement MShape MInt))
    @test e isa ImplementError && occursin("infers its result as Int64, outside the declared Float64", msg(e))
    @eval begin
        struct MAny; n::Any; end
        MsgLib.marea(s::MAny) = 1.0
        MsgLib.mname(s::MAny) = s.n
    end
    e = thrown(:(@implement MShape MAny))
    @test e isa ImplementError && occursin("infers its result as Any, wider than the declared AbstractString", msg(e))

    @eval begin
        struct MOk; r::Float64; end
        MsgLib.marea(s::MOk) = s.r
        MsgLib.mname(s::MOk) = "ok"
        @implement MShape MOk
    end
    e = thrown(:(MsgLib.marea(s::MOk) = s.r > 1 ? "big" : s.r))
    @test e isa ImplementError && e.method
    @test startswith(msg(e), "ImplementError: a method is refused: ") && occursin("is a member of", msg(e))
    @test occursin("fix: return within Float64", msg(e)) && !occursin("cannot be a member", msg(e))
    @test Base.invokelatest(mdouble, MOk(2.0)) == 4.0

    e = thrown(:(module MsgOpen
                 using TraitWorld
                 @trait_module bounded
                 @trait MBox begin
                     mvol(b::MBox)::Float64
                 end
                 mdensity(b::MBox) = b.mass / mvol(b)
                 end))
    @test e isa TraitWorld.TraitUseError && occursin("the field `mass` is no declared field of", msg(e))   # read at the box (D-3)

    # the code a declaration makes lies at the declaration: the kept forms' forwarding methods (lowering §2)
    ms = [m for m in methods(marea) if TraitWorld._is_trait_method(m)]
    @test length(ms) == 2 && all(m -> endswith(string(m.file), "messages.jl"), ms)
end

@testset "a signature prints as a call" begin
    cf = TraitWorld._callform
    @test cf(Tuple{typeof(sum), Vector{Int8}}) == "sum(::Vector{Int8})"
    @test (c = cf(Tuple{typeof(push!), Vector{T}, T} where T); startswith(c, "push!(::") && endswith(c, ", ::T) where {T}"))
    @test cf(Tuple{Type{Int}, Float64}) == "Int64(::Float64)"
    @test !occursin("Tuple{typeof", cf(Tuple{typeof(marea), MShape}))
end

# the bounded check's refusal names the method as its signature is written and each argument read in a box, by its
# name: never the compiler's tuple type, nor a keyword body's or a closure's generated name (traits §7.3, §11.3)
@testset "the bounded check names the method as written" begin
    # (`marea`, the trait's operation, imported: at its module's end a call of a name the module never defines is a
    # fault, the next testset)
    bmsg(code) = (e = thrown(Meta.parse("module MB$(rand(UInt32))\nusing TraitWorld\nusing ..MsgLib: MShape, marea\n@trait_module\n$code\nend")); e isa TraitWorld.TraitUseError ? msg(e) : string(e))
    Q = raw"(\w+\.)*"                        # a type's module, where the test's module does not see it
    m = bmsg("msum(t::MShape) = sum(t)")
    @test occursin(Regex("^TraitUseError: `msum\\(t::$(Q)MShape\\)` is declared bounded, and is not bounded: read with `t` in a box, `$(Q)Dynamic\\{$(Q)MShape\\}`:"), m)
    @test occursin(Regex("sum\\(t\\) reaches iterate\\(::$(Q)Dynamic\\{$(Q)MShape\\}\\), which has no method"), m)
    m = bmsg("mboth(a::MShape, b::MShape, k::Int) = length(a) + length(b) + k")
    @test occursin(Regex("`mboth\\(a::$(Q)MShape, b::$(Q)MShape, k::$Int\\)` is declared bounded"), m)
    @test occursin(Regex("read with `a` in a box, `$(Q)Dynamic\\{$(Q)MShape\\}`, and `b` in a box, `$(Q)Dynamic\\{$(Q)MShape\\}`:"), m)
    @test occursin("length(a) has no method", m)
    m = bmsg("mkw(t::MShape; k::Float64 = 1.0) = k * length(t)")
    @test occursin(Regex("`mkw\\(t::$(Q)MShape; k::Float64\\)` is declared bounded"), m)
    m = bmsg("mclo() = (t::MShape) -> length(t)")
    @test occursin(Regex("`\\(t::$(Q)MShape\\) -> …` in `mclo` is declared bounded"), m)
    m = bmsg("mwhere(t::C) where {C <: MShape} = length(t)")
    @test occursin(Regex("`mwhere\\(t::C\\) where C<:$(Q)MShape` is declared bounded"), m)
    # a vararg of members is read with each of its elements in a box (traits §7.3, §6.6; T-158)
    m = bmsg("mva(ts::MShape...) = sum(t -> length(t), ts)")
    @test occursin(Regex("^TraitUseError: `mva\\(ts::$(Q)MShape...\\)` is declared bounded, and is not bounded: read with each of `ts` in a box, `$(Q)Dynamic\\{$(Q)MShape\\}`:"), m)
    @test occursin("sum((t) -> …, ts)", m)
    @test bmsg("mvaok(ts::MShape...) = sum(marea, ts)") == "nothing"
    m = bmsg("mfv(a::MShape, ts::MShape...) = marea(a) + sum(t -> length(t), ts)")
    @test occursin(Regex("`mfv\\(a::$(Q)MShape, ts::$(Q)MShape...\\)` is declared bounded, and is not bounded: read with `a` in a box, `$(Q)Dynamic\\{$(Q)MShape\\}`, and each of `ts` in a box, `$(Q)Dynamic\\{$(Q)MShape\\}`:"), m)
    @test bmsg("mfvok(a::MShape, ts::MShape...) = marea(a) + sum(marea, ts)") == "nothing"
    m = bmsg("mvw(ts::T...) where {T <: MShape} = first(ts[1])")
    @test occursin("read with each of `ts` in a box", m) && occursin(Regex("first\\(::$(Q)Dynamic\\{$(Q)MShape\\}\\) reaches iterate"), m)
    # what a closure over a vararg of boxes reaches, at a tuple of no fixed length and at a fixed count (the chain
    # below Base's `sum` deeper than 20 calls): the operation that has no method, named (traits §7.3; T-159)
    m = bmsg("mva5(ts::MShape...) = sum(t -> length(t), ts)")
    @test occursin(Regex("sum\\(\\(t\\) -> …, ts\\) reaches length\\(::$(Q)Dynamic\\{$(Q)MShape\\}\\), which has no method"), m)
    for code in ("mva3(ts::MShape...) = sum(t -> sum(t), ts)", "mva4(ts::Vararg{MShape, 2}) = sum(t -> sum(t), ts)")
        m = bmsg(code)
        @test occursin(Regex("sum\\(\\(t\\) -> …, ts\\) reaches iterate\\(::$(Q)Dynamic\\{$(Q)MShape\\}\\), which has no method \\(through [^)]*\\(t\\) -> … → sum\\)"), m)
        @test !occursin("Pairs", m) && !occursin("kw::", m)       # the chain by the functions' names: no keyword body
    end
    mv(ts::MShape...) = 0
    @test TraitWorld.box_signature(only(methods(mv))) == Tuple{typeof(mv), Dynamic{MShape}, Vararg{Dynamic{MShape}}}
    for code in ("msum2(t::MShape) = sum(t)", "mkw2(t::MShape; k::Float64 = 1.0) = k * length(t)", "mclo2() = (t::MShape) -> length(t)",
                 "mva2(ts::MShape...) = sum(t -> length(t), ts)")
        m = bmsg(code)
        @test startswith(m, "TraitUseError: ") && !occursin("Tuple{", m) && !occursin("var\"#", m) && !occursin(r"#\w+#\d", m)
    end
end

# At its module's end a call of a name the module never defines is a fault (traits §7.3, "When"; T-161): the report
# names the name, its module and the line; a name defined later in the module, by `@eval` or a macro at its end, is
# read once defined. A call with no value at the box is not the check's; nor a name of another module, `N.name`.
@testset "the bounded check at a name its module never defines" begin
    umsg(code; opts = "") = (e = thrown(Meta.parse("module MU$(rand(UInt32))\nusing TraitWorld\nusing ..MsgLib: MShape\n@trait_module $opts\n$code\nend")); e isa TraitWorld.TraitUseError ? msg(e) : string(e))
    m = umsg("mnot(a::MShape) = nothere(a)")
    @test occursin(r"nothere\(a\): `nothere` is not defined in Main\.(\w+\.)*MU\d+, at line 5", m)
    # the trait's operation not imported: each call that names it, and where to import it from
    m = umsg("mfv(a::MShape, ts::MShape...) = marea(a) + sum(marea, ts)")
    @test occursin(r"marea\(a\): `marea` is not defined in [\w.]+; `marea` is an operation of [\w.]*MShape: `using [\w.]*MsgLib: marea` imports it, at line 5", m)
    @test occursin("sum(marea, ts): `marea` is not defined in", m)
    @test occursin("nothere(a): `nothere` is not defined", umsg("using ..MsgLib: marea\nmbr(a::MShape) = marea(a) > 0 ? nothere(a) : 0.0"))
    @test occursin("`nothere` is not defined", umsg("global nothere\nmdecl(a::MShape) = nothere(a)"))
    # defined in `__init__`: after the module's end
    @test occursin("later(a): `later` is not defined", umsg("mini(a::MShape) = later(a)\n__init__() = @eval later(x) = 1.0"))
    # defined later: waits, then read (no method at the box: refused; a method: accepted)
    @test occursin("later(a) has no method", umsg("mlate(a::MShape) = later(a)\nlater(x::Int) = 1.0"))
    @test umsg("mlate(a::MShape) = later(a)\nlater(x) = 1.0") == "nothing"
    @test umsg("mlate(a::MShape) = later(a)\n@eval later(x) = 1.0") == "nothing"
    @test umsg("macro deflater(); esc(:(later(x) = 1.0)); end\nmlate(a::MShape) = later(a)\n@deflater") == "nothing"
    # a global that is not a function: its call has no method; an untyped global's value is not known: run time
    @test occursin("K(a) has no method", umsg("const K = 3\nmk(a::MShape) = K(a)"))
    @test occursin("K(a) has no method", umsg("K::Int = 3\nmk(a::MShape) = K(a)"))
    @test umsg("K = 3\nmk(a::MShape) = K(a)") == "nothing"
    # not the check's: no value at the box; another module's name
    @test umsg("using ..MsgLib: marea\nmnb(a::MShape) = nothere(1) + marea(a)") == "nothing"
    @test umsg("using ..MsgLib\nmqual(a::MShape) = MsgLib.nothere(a)") == "nothing"
    # a scope that does not declare `bounded` accepts it; `check_definitions` lists it
    M = Core.eval(@__MODULE__, Meta.parse("module MU$(rand(UInt32))\nusing TraitWorld\nusing ..MsgLib: MShape\n@trait_module bounded = false\nmnot(a::MShape) = nothere(a)\nend"))
    @test occursin("nothere(a): `nothere` is not defined in", only(check_definitions(M)))
end

# A call is read as written, at the types the code knows (traits §7.3; open issue 249). Julia's optimizer compiles a
# call at an abstract argument whose methods cover a part of it as a test of the argument's type, the method's call,
# and else `Core.throw_methoderror`: that other branch is the call as written, which has a method there. A call
# that finds no method at the types the code knows stays a fault, split or not.
@testset "the bounded check reads a split as the call as written" begin
    bmsg(code) = (e = thrown(Meta.parse("module MS$(rand(UInt32))\nusing TraitWorld\n@trait_module\n$code\nend")); e isa TraitWorld.TraitUseError ? msg(e) : string(e))
    traits = """
        struct GSol{T}; u::Vector{T}; end
        struct GOpts; a::Float64; n::Int; end
        @trait GProb{T} begin
            @const u0::Vector{T}
        end
        @trait GAlg begin
            grun(a::GAlg, x::Vector{Float64})::GSol
        end
        gwith(s::GSol{T}, p::GProb{T}) where {T} = (s.u, p.u0)
        ginner(p::GProb{Float64}, a::GAlg, o::GOpts) = grun(a, p.u0)
        """
    # the operation's result of an abstract type, passed where one method takes a part of it (`isa(s, GSol{Float64})`)
    @test bmsg(traits * "gcase(p::GProb{Float64}, a::GAlg) = gwith(grun(a, p.u0), p)") == "nothing"
    # a keyword of a type the code does not know: its options' type unknown, the call split on it
    @test bmsg(traits * "gkw(p::GProb{Float64}, a::GAlg; tol = 1e-8, n = 10) = ginner(p, a, GOpts(Float64(tol), Int(n)))") == "nothing"
    # no method at the types known: a fault, named by the function's name
    m = bmsg(traits * "gno(x::Int) = x\ngref(p::GProb{Float64}) = gno(p)")
    @test occursin("gno(p) has no method", m)
    # an abstract argument that no method covers: a fault, though the argument's type is abstract
    m = bmsg(traits * "gint(x::Int, p::GProb{Float64}) = 1.0\ngref2(p::GProb{Float64}, a::GAlg) = gint(grun(a, p.u0), p)")
    @test occursin(Regex("gint\\(::(\\w+\\.)*GSol, p\\) has no method"), m)
    # the box's own argument outside every method, beside an argument of a type the code does not know
    m = bmsg(traits * "gtwo(x::Int, y::Int) = x\ngref3(p::GProb{Float64}, k) = gtwo(k, p)")
    @test occursin("gtwo(k, p) has no method", m)
    # Julia's own form, as the check reads it: the split's test and its other branch are in the instance at the box
    @eval module MSplit
    using TraitWorld
    @trait_module bounded = false
    struct SSol{T}; u::Vector{T}; end
    @trait SAlg begin
        srun(a::SAlg)::SSol
    end
    swith(s::SSol{Float64}, a::SAlg) = 1.0
    scase(a::SAlg) = swith(srun(a), a)
    end
    src = Base.code_typed_by_type(TraitWorld.box_signature(only(methods(MSplit.scase))); optimize = true)[1][1]
    @test any(st -> st isa Expr && st.head === :call && st.args[1] == GlobalRef(Core, :throw_methoderror), src.code)
    @test TraitWorld.check_at_box(only(methods(MSplit.scase))) == TraitWorld.BoxFault[]
end

@testset "no hint at an operation that is another owner's function" begin
    e = try getindex(nothing, 1); nothing catch err; err end
    m = sprint(showerror, e)
    @test e isa MethodError && !occursin("Indexable", m) && !occursin("Keyed", m)
    # an operation of the trait's own module keeps its hints, where the argument at its receiver's position is a
    # member (traits §11.4)
    e = try marea(MOk(1.0), 2); nothing catch err; err end
    @test occursin("`marea` is declared", sprint(showerror, e))
    e = try marea(1, 2); nothing catch err; err end
    @test e isa MethodError && !occursin("`marea` is declared", sprint(showerror, e))
    e = try mdouble(3); nothing catch err; err end
    @test occursin("is not a member of `MShape`", sprint(showerror, e))
end

# a check's error is raised at the user's line: the first frame of its backtrace is the `@implement`
# or the method's definition, not the library (traits §11.3)
function first_frame(code::String)
    try
        Base.include_string(@__MODULE__, code, "user_code.jl")
        return nothing
    catch e
        st = stacktrace(catch_backtrace())
        while e isa LoadError; e = e.error; end
        return e, st[1]
    end
end

@testset "a check's error has the user's line as its first frame" begin
    @eval struct MNoArea; end
    e, fr = first_frame("\n\n@implement MShape MNoArea\n")
    @test e isa ImplementError
    @test string(fr.file) == "user_code.jl" && fr.line == 3
    # a method that breaks a member's contract, refused by the definition hook
    @eval begin
        struct MGood; end
        MsgLib.marea(::MGood) = 1.0
        MsgLib.mname(::MGood) = "good"
        @implement MShape MGood
    end
    e, fr = first_frame("\nMsgLib.marea(::MGood) = 1\n")
    @test e isa ImplementError
    @test string(fr.file) == "user_code.jl" && fr.line == 2
end

@trait MScalable begin
    mscale(s::MScalable, k::Float64)::Float64
end
struct MSC; end
mscale(::MSC, k::Float64) = k
@implement MScalable MSC

# an operation is an entry of the contract and no method at the trait (traits §4.1): a call outside its declared
# signature is Julia's MethodError, with the contract's hint (traits §11.4)
@testset "an operation called outside its declared signature" begin
    e = try mscale(MSC(), 2); nothing catch err; err end
    @test e isa MethodError
    m = msg(e)
    @test occursin("no method matching mscale(::", m) && occursin("MSC, ::$Int)", m)
    @test occursin("`mscale` is declared `mscale(s::MScalable, k::Float64)::Float64` by MScalable", m)
    @test occursin("MSC, !Matched::Float64)", m)                   # Julia's closest candidate: the member's method
    @test isempty([mm for mm in methods(mscale) if mm.sig isa DataType && mm.sig.parameters[2] === MScalable])
end
