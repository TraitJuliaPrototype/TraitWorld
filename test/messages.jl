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
    @test e isa TraitWorld.TraitUseError && occursin("the field `mass` of a", msg(e))

    m = only(m for m in methods(marea) if m.sig == Tuple{typeof(marea), MShape})
    @test endswith(string(m.file), "messages.jl")
end

@testset "a signature prints as a call" begin
    cf = TraitWorld._callform
    @test cf(Tuple{typeof(sum), Vector{Int8}}) == "sum(::Vector{Int8})"
    @test (c = cf(Tuple{typeof(push!), Vector{T}, T} where T); startswith(c, "push!(::") && endswith(c, ", ::T) where {T}"))
    @test cf(Tuple{Type{Int}, Float64}) == "Int64(::Float64)"
    @test !occursin("Tuple{typeof", cf(Tuple{typeof(marea), MShape}))
end

@testset "no hint at an operation that is another owner's function" begin
    e = try getindex(nothing, 1); nothing catch err; err end
    m = sprint(showerror, e)
    @test e isa MethodError && !occursin("Indexable", m) && !occursin("Keyed", m)
    # an operation of the trait's own module keeps its hints
    e = try marea(1, 2); nothing catch err; err end
    @test occursin("`marea` is declared", sprint(showerror, e))
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

@testset "an operation called outside its declared signature" begin
    e = try mscale(MSC(), 2); nothing catch err; err end
    @test e isa OperationError
    m = msg(e)
    @test occursin("no method of `mscale` takes (::MSC, ::Int64)", m)
    @test occursin("`mscale` is declared `mscale(s::MScalable, k::Float64)::Float64` by MScalable", m)
    @test occursin("MSC's methods of `mscale`: mscale(::MSC, ::Float64)", m)
    @test !occursin("manually thrown", m)
end
