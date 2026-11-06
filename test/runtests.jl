# The library's tests, on Julia's unified build.
for f in ("overview.jl", "core.jl", "acceptance.jl")
    @info "TraitWorld: $f"
    include(f)
end
