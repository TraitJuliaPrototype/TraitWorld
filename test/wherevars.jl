# `where` variables in bounds (traits reference §5.1): a bound may leave a parameter open with a `where`
# variable, read in the body; a variable shared between bounds, or with an ordinary argument, requires
# equal values. A `Callable` bound naming one is refused when the method is defined (§5.8).
# Runs inside runtests.jl, or alone: julia --project=. test/wherevars.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))

toplevel(quote
    @trait_module module WV
    using TraitWorld
    export KV, klen, kget, firstof2, samesum, withvec, posfirst
    @trait KV{T} begin
        T = eltype(Self)
        klen(v::KV)::Int
        kget(v::KV{T}, i::Int)::T
    end
    @implement KV A where {A <: Vector{<:Real}} begin
        klen(v) = length(v)
        kget(v, i) = v[i]
    end
    firstof2(v::KV{T}) where {T} = (T, kget(v, 1))
    samesum(a::KV{T}, b::KV{T}) where {T} = kget(a, 1) + kget(b, 1)
    withvec(v::KV{T}, w::Vector{T}) where {T} = (kget(v, 1), w[1])
    posfirst(v::KV{T}) where {T <: Integer} = kget(v, 1)
    end
end)

@testset "where variables in bounds" begin
    W = Main.WV
    @test W.firstof2([1.0, 2.0]) == (Float64, 1.0)
    @test W.firstof2([1, 2]) == (Int, 1)
    tf(v::Vector{Float32}) = W.firstof2(v)                       # from a typed caller: Compiled
    @test tf(Float32[3]) == (Float32, 3.0f0)
    @test W.firstof2(with_dynamic([1.0])) == (Float64, 1.0)       # Dynamic: the parameter is carried
    @test W.samesum([1.0], [2.0]) == 3.0
    @test_throws TraitBoundError W.samesum([1.0], [2])           # a shared variable: equal values
    @test W.withvec([1.0], [2.0]) == (1.0, 2.0)
    @test_throws TraitBoundError W.withvec([1.0], [2])           # shared with an ordinary argument
    @test W.posfirst([3]) == 3
    @test_throws TraitBoundError W.posfirst([3.0])               # the variable's bound
    # a Callable's argument types may follow the other arguments (traits reference §5.8)
    toplevel(quote
        @trait_module module WVFollows
        using TraitWorld
        cmapT(f::Callable{Tuple{T}, T}, x::Vector{T}) where {T} = map(f, x)
        end
    end)
    @test Base.invokelatest(Main.WVFollows.cmapT, x -> 2x, [1, 2]) == [2, 4]
    @test Base.invokelatest(Main.WVFollows.cmapT, x -> 2x, [1.5]) == [3.0]
    # a variable only the Callable names is refused when the method is defined
    err = try
        toplevel(quote
            @trait_module module WVBad
            using TraitWorld
            cmapS(f::Callable{Tuple{S}, S}, x::Int) where {S} = f(x)
            end
        end)
        nothing
    catch e
        e
    end
    @test err isa LoadError && occursin("no other argument fixes", sprint(showerror, err))
end

# lowering L-49 (retired): a bound's `where` variable shadows a global of the module of the same name, as in
# plain Julia (ODECore has LinearAlgebra's `I`; `IndexProvider{I}` was read as `IndexProvider{LinearAlgebra.I}`)
toplevel(quote
    @trait_module module WVShadow
    using TraitWorld
    using LinearAlgebra: I
    export ixdyn
    @trait SIx{K} begin
        skey(x::Self)::Int
    end
    @trait SNamed begin
        sname(x::Self)::String
    end
    struct SA; end
    @implement SIx{Symbol} SA begin
        skey(a) = 1
    end
    @implement SNamed SA begin
        sname(a) = "a"
    end
    ixof(x::SIx{I}) where {I} = I
    ixboth(x::(SIx{I}, SNamed)) where {I} = (I, sname(x))
    ixdyn(x::Dynamic{SIx{I}}) where {I} = I
    plainof(x::Vector{I}) where {I} = I
    end
end)
@testset "lowering L-49: a where variable shadows a module global" begin
    S = Main.WVShadow
    @test S.plainof([1.0]) === Float64
    @test S.ixof(S.SA()) === Symbol
    @test S.ixboth(S.SA()) === (Symbol, "a")
    @test S.ixdyn(S.SA()) === Symbol
end
