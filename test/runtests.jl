# The library's tests, on Julia's unified build. Each file runs in a module of its own: files
# that declare a trait of the same name and the same struct would make it a member of both.
for f in ("overview.jl", "core.jl", "acceptance.jl", "attribute.jl", "callable.jl", "fullytyped.jl", "ownership.jl", "hints.jl", "verify.jl", "basetraits.jl", "strict.jl", "strict_membership.jl", "recheck.jl")
    @info "TraitWorld: $f"
    Base.include(Module(Symbol(splitext(f)[1])), joinpath(@__DIR__, f))
end
