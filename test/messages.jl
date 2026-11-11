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
