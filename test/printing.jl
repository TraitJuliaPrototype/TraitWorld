# Printing by bound and representation (findings §16, §17): a trait object's type prints as
# `StateVector{Float64} at Vector{Float64}`, a function bound as `Callable{…} at …`, in stack
# traces and messages, instead of the machinery's TObj{…View{…Impl{…}…}} types.
# Runs inside runtests.jl, or alone: julia --project=. test/printing.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module PrintLib
    using TraitWorld

    @trait PVec{T, R} begin
        T = eltype(R)
        plen(r::R)::Int
    end
    @implement PVec{T, Vector{T}} where {T <: Real} begin
        plen(r) = length(r)
    end

    boom(s::PVec) = plen(s) > 0 ? error("boom") : 0
    apply(f::Callable{Tuple{Float64}, Float64}, s::PVec) = plen(s) > 0 ? error("apply") : f(1.0)
    end
end)

frames(f) = try f(); "" catch; sprint(Base.show_backtrace, catch_backtrace()) end
# every frame, the machinery's included (the tiny workers here are inlined into TraitWorld's `checked_call`)
allframes(f) = withenv(() -> frames(f), "JULIA_TW_ALL_FRAMES" => "1")

# Readable types need Julia's type-printer registry (patched build); without it types print as
# Julia prints them, and TraitWorld must not widen `show(::IO, ::Type)` to get there.
const HAS_PRINTERS = isdefined(Base.Experimental, :register_type_printer)

@testset "TraitWorld adds no method of show at types of types" begin
    widening = [m for m in methods(Base.show) if parentmodule(m) === TraitWorld &&
                any(p -> p isa Type && p <: Type && p !== Union{}, Base.unwrap_unionall(m.sig).parameters[2:end])]
    @test isempty(widening)
end

HAS_PRINTERS && @testset "Printing by bound and representation" begin
    P = Main.PrintLib
    # the function by a constant path: through a local variable (`P.boom`) the call is dispatched at run
    # time, and the value is `Dynamic` there (traits reference §6.6)
    bt = allframes(() -> Main.PrintLib.boom([1.0, 2.0]))
    @test occursin("PVec{Float64} at Vector{Float64}", bt)
    @test occursin("PVec{Float64} at Dynamic", allframes(() -> P.boom([1.0, 2.0])))
    @test !occursin("TraitWorld.View{", bt) && !occursin("Impl{", bt)
    bt2 = allframes(() -> Main.PrintLib.apply(x -> 2x, [1.0]))
    @test occursin("Callable{Tuple{Float64}, Float64} at ", bt2)
    T = TraitWorld.TObj{TraitWorld._encode_traits(Any[P.PVec{Float64, Vector{Float64}}]),
                        Tuple{TraitWorld.View{P.PVec{Float64, Vector{Float64}}, TraitWorld.Impl{()}, Vector{Float64}, 0, Tuple{Vector{Float64}}}}}
    @test sprint(show, T) == "$(sprint(show, P.PVec)){Float64} at Vector{Float64}"
    @test sprint(show, TraitWorld.TObj) == "TraitWorld.TObj" || sprint(show, TraitWorld.TObj) == "TObj"   # not concrete: as Julia prints it
    E = TraitWorld.CObj{Tuple{Float64}, Float64, TraitWorld.Erased{Tuple{Float64}, Float64}}
    @test sprint(show, E) == "Callable{Tuple{Float64}, Float64} at Dynamic"
end

@testset "conforms(T, X): membership as a function" begin
    P = Main.PrintLib
    @test conforms(Vector{Float64}, P.PVec)
    @test conforms(Vector{Float64}, P.PVec{Float64})
    @test !conforms(Vector{Int}, P.PVec{Float64})               # conforms, at another parameter
    @test conforms(Vector{Int}, P.PVec)
    @test !conforms(String, P.PVec)
    @test conforms(Dynamic{P.PVec}, P.PVec)
end

@testset "Stack traces hide the machinery's frames" begin
    bt = frames(() -> Main.PrintLib.boom([1.0, 2.0]))
    @test occursin("boom", bt) && !occursin("TraitWorld/src/", bt) && !occursin("checked_call", bt)
    @test occursin("checked_call", allframes(() -> Main.PrintLib.boom([1.0, 2.0])))
end

