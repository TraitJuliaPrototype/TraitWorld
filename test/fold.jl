# A family member's builder fixed in its callers' code (W-40; traits reference §4.7, lowering §4.6;
# the design note writeup/plans/2026-10-26-w40-member-builder-fold.md §4, §11). Needs the patched
# Julia's `Compiler.fold_call`. Runs inside runtests.jl, or alone: julia --project=. test/fold.jl
using Test, TraitWorld
isdefined(Main, :toplevel) || (toplevel(ex) = Core.eval(Main, ex isa Expr && ex.head === :block ? Expr(:toplevel, ex.args...) : ex))
if !TraitWorld._HAS_FOLD
    @info "fold: no Compiler.fold_call in this Julia; skipped"
else
toplevel(quote
    @trait_module module FoldF
    using TraitWorld
    export FV, fval, fsum, FW, fw1
    @trait FV begin
        fval(v::FV)::Float64
    end
    struct Cell{T}; x::T; end
    fval(c::Cell) = Float64(c.x)
    @implement FV C where {C <: Cell}
    fsum(v::FV, n::Int) = (s = 0.0; for _ in 1:n; s += fval(v); end; s)
    # a trait with many fields: a builder over 256 bytes (N1)
    @trait FW begin
        a1::Float64; a2::Float64; a3::Float64; a4::Float64; a5::Float64; a6::Float64
        a7::Float64; a8::Float64; a9::Float64; a10::Float64; a11::Float64; a12::Float64
        a13::Float64; a14::Float64; a15::Float64; a16::Float64; a17::Float64; a18::Float64
        fw1(w::FW)::Float64
    end
    mutable struct Wide{T}
        a1::Float64; a2::Float64; a3::Float64; a4::Float64; a5::Float64; a6::Float64
        a7::Float64; a8::Float64; a9::Float64; a10::Float64; a11::Float64; a12::Float64
        a13::Float64; a14::Float64; a15::Float64; a16::Float64; a17::Float64; a18::Float64
        t::T
    end
    fw1(w::Wide) = w.a1 + w.a18
    @implement FW W where {W <: Wide}
    wsum(w::FW) = w.a1 + w.a9 + w.a18 + fw1(w)
    struct Bad{T}; x::T; end           # Bad{String} does not conform: fval returns a String
    fval(b::Bad) = b.x
    @implement FV B where {B <: Bad}
    end
end)
const FF = Main.FoldF
typed_loop(c::FF.Cell{Int}, n) = FF.fsum(c, n)
@testset "W-40: a family member's builder folded in a typed caller" begin
    c = FF.Cell(2)
    @test typed_loop(c, 10) == 20.0
    allocs = @allocated typed_loop(c, 1000)
    @test allocs == 0                                                  # no registry lookup, no boxed builder
    src = string(only(code_typed(typed_loop, (FF.Cell{Int}, Int)))[1])
    @test !occursin("_conf_family", src)
    # the member is fixed: its own declaration after the fold is refused (L-23)
    e = try toplevel(:(Core.eval(FoldF, :(@implement FV Cell{Int} begin fval(c) = 9.0 end)))); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    @test e isa ImplementError
end
@testset "W-40: a builder over 256 bytes (N1)" begin
    w = FF.Wide(ntuple(i -> Float64(i), 18)..., 0)
    f(w::FF.Wide{Int}) = FF.wsum(w)
    @test f(w) == 1.0 + 9.0 + 18.0 + 19.0
    @test sizeof(typeof(TraitWorld._conformance_builder(FF.FW, typeof(w)))) > 256 ||
          @warn "the wide builder is not over 256 bytes; N1 not exercised"
end
@testset "W-40: not folded where the type is unknown; a member that does not conform" begin
    @test FF.fsum(Any[FF.Cell(1.5)][1], 2) == 3.0                     # untyped: the run-time path
    bad(b::FF.Bad{String}) = FF.fsum(b, 1)
    @test_throws ImplementError bad(FF.Bad("x"))                      # refused at the call, as decided
end
end
