"""
    TraitWorld

Traits as abstract types, on Julia's unified build (branch `unified` of the julia repository):
a trait is an open abstract type with a contract, a membership an entry of the type system.
The references: `writeup/reference/traits.md`, `lowering.md` and `compiler.md` of the design
repository. What the library does is to declare, to check and to report (lowering §1).
"""
module TraitWorld

isdefined(Core, :MembershipEntry) ||
    error("TraitWorld needs Julia's unified build, whose type system has memberships")

export @trait, @implement, Dynamic, unwrap, like, withfields, ImplementError, TraitUseError

# Intersections All{X, Y, …} (traits §3.6): Core does not export the name, and the library does,
# so a module that also uses DataAPI's `All` qualifies one of them (open issue 148)
@static if isdefined(Core, :All)
    const All = Core.All
    export All
end

include("contract.jl")
include("runtime.jl")
include("errors.jl")
include("dynamic.jl")
include("trait.jl")
include("check.jl")
include("implement.jl")
include("like.jl")

function __init__()
    # the member hook (compiler §10.4): a member of a pattern is checked at its first use
    ccall(:jl_set_member_hook, Cvoid, (Any,), _member_hook)
end

end # module
