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

export @trait, @implement, Dynamic, unwrap, like, withfields, ImplementError, TraitUseError,
       @bounded, @open, check_definitions, classify, @trait_module, compiled_for, with_dynamic, keep,
       detect_dynamic_fallbacks, detect_unused_casts, Callable,
       @enforce_fully_typed, @warn_not_fully_typed, fully_typed, isfullytyped, FullyTypedReport,
       NotFullyTypedError, AbstractTypeError, @enforce_concrete_only, @warn_on_abstract,
       OwnershipError, @joint_owners, PirateError, verify_main, VerifyReport

# the casts and `keep` (traits §7.6, §7.8): Julia's own, re-exported; the casts' names are reserved,
# so they are imported, never assigned
import Core: compiled_for, with_dynamic, keep

# Intersections All{X, Y, …} (traits §3.6): Core does not export the name, and the library does,
# so a module that also uses DataAPI's `All` qualifies one of them (open issue 148)
@static if isdefined(Core, :All)
    const All = Core.All
    export All
end

include("contract.jl")
include("runtime.jl")
include("errors.jl")
include("ownership.jl")
include("dynamic.jl")
include("trait.jl")
include("check.jl")
include("implement.jl")
include("like.jl")
include("classify.jl")
include("scope.jl")
include("callable.jl")
include("fullytyped.jl")
include("hints.jl")
include("strict.jl")
include("ahead.jl")

# BaseTraits (traits §10): a module of the library, its names exported with the library's
include("BaseTraits.jl")
using .BaseTraits
export HasLength, Iterable, Indexable, MutableIndexable, Resizable, Keyed, Solvable,
       LinearOp, apply!, BoundedText, textbound, asvector, IndexableVector, retain!

function __init__()
    # the member hook (compiler §10.4): a member of a pattern is checked at its first use
    ccall(:jl_set_member_hook, Cvoid, (Any,), _member_hook)
    # the definition and module-end hooks (compiler §10.1): the override rule, a missing `@implement`
    ccall(:jl_set_method_definition_hook, Cvoid, (Any,), _definition_hook)
    ccall(:jl_set_module_end_hook, Cvoid, (Any,), _module_end_hook)
    ccall(:jl_set_image_methods_hook, Cvoid, (Any,), _image_methods_hook)
    # fully typed mode's hook (compiler §2.7): code that fails it reports through the library
    ccall(:jl_set_fully_typed_hook, Cvoid, (Any,), _fully_typed_hook)
    # the hints on MethodError where a trait is involved (traits §11.4)
    Base.Experimental.register_error_hint(_method_error_hint, MethodError)
    # strict mode (traits §12.3): JULIA_TW_STRICT=1, the report after each package load
    _strict_init!()
    ccall(:jl_set_method_deletion_hook, Cvoid, (Any,), _deletion_hook)
end

end # module
