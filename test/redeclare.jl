# A second declaration of an implementation in a session is refused, in every form (traits
# reference §5.9): which operations a type's own methods and the defaults serve is fixed by the
# declaration. Runs inside runtests.jl (it uses `Columns` and `ColTable` from there).
using Test, TraitWorld

function _thrown_ie(ex)
    e = try toplevel(ex); nothing catch err; err end
    while e isa LoadError; e = e.error; end
    return e
end

@testset "a redeclaration is refused in every form" begin
    toplevel(quote
        struct RD1; data::Vector{Vector{Float64}}; end
        @implement ColTable RD1 by data
        struct RD2; n::Int; end
        Columns.ncols(r::RD2) = r.n
        Columns.col(r::RD2, i::Int) = fill(Float64(i), 2)
        @implement ColTable RD2
    end)
    for ex in (:(@implement ColTable RD1 by data),
               :(@implement ColTable RD2),
               :(@implement ColTable RD2 begin ncols(t) = 1; col(t, i) = [1.0] end))
        e = _thrown_ie(ex)
        @test e isa ImplementError && occursin("already conforms", e.msg)
    end
    @test colmean(Main.RD1([[1.0, 3.0]]), 1) == 2.0 && colmean(Main.RD2(2), 2) == 2.0   # the first declarations stand
end
