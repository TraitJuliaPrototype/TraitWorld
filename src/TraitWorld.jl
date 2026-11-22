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

# The library's own code is compiled by facts, as trait modules are (the other options off). Its
# image holds the code its run-time sites reach whatever the values (compiler §9; E-326).
Base.Experimental.@compiler_options facts = true

export @trait, @implement, Dynamic, unwrap, like, withfields, ImplementError, TraitUseError,
       @bounded, @unbounded, check_definitions, classify, @trait_module, compiled_for, Callable,
       @enforce_fully_typed, @warn_not_fully_typed, fully_typed, isfullytyped, FullyTypedReport,
       NotFullyTypedError, AbstractTypeError, @enforce_concrete_only, @warn_on_abstract,
       OwnershipError, @joint_owners, @owner_only, delete_membership, PirateError, verify_main, VerifyReport, add_entrypoints, make_executable, make_library, BuildError,
       Compiled, erases, check_at_box

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
include("compiled.jl")
include("trait.jl")
include("check.jl")
include("implement.jl")
include("like.jl")
include("classify.jl")
include("erasing.jl")
include("atbox.jl")
include("scope.jl")
include("callable.jl")
include("fullytyped.jl")
include("hints.jl")
include("strict.jl")
include("report.jl")
include("delete.jl")
include("ahead.jl")
include("build.jl")
include("buildbase.jl")

# BaseTraits (traits §10): a module of the library, its names exported with the library's
include("BaseTraits.jl")
using .BaseTraits
export HasLength, Iterable, Indexable, MutableIndexable, Resizable, Keyed, Solvable,
       LinearOp, apply!, BoundedText, textbound, HasProperty, asvector, IndexableVector, retain!

# The hooks the runtime and Base call through `invokelatest` or `jl_apply`: precompiled, so that no session
# compiles them at its first package load (W-121, E-286: `_strict_at_load!` took half of TraitWorld's load)
precompile(_strict_at_load!, (Base.PkgId,))
precompile(_report_at_load!, (Base.PkgId,))
precompile(_report_endings!, (Vector{Any},))
precompile(_member_hook, (Any, Any))
precompile(_definition_hook, (Method, Bool))
precompile(_expand_definition, (Core.SimpleVector, Core.CodeInfo, Module))
precompile(_image_methods_hook, (Vector{Any}, String))
precompile(_module_end_hook, (Module,))
precompile(_deletion_hook, (Method,))
precompile(_fully_typed_hook, (Core.SimpleVector,))
precompile(_sig_alternatives, (Any,))           # the image hook's, at each package load
precompile(_records_from_entry!, (Any,))       # the records of each membership an image activates
precompile(_records_at, (Any, Any, Any, How))
precompile(_record_checks!, (Any, Any, Vector{Any}, Vector{Any}))
precompile(_forget_records!, (Any, Any))
precompile(_record_forwarders!, (Any, Any, Symbol))

function __init__()
    # the member hook (compiler §10.4): a member of a pattern is checked at its first use
    ccall(:jl_set_member_hook, Cvoid, (Any,), _member_hook)
    # the definition and module-end hooks (compiler §10.1): the override rule, a missing `@implement`
    ccall(:jl_set_method_definition_hook, Cvoid, (Any,), _definition_hook)
    # the expansion hook (compiler §10.1; lowering §5): a method at a trait that erases by default is defined at
    # the kept forms, with a forwarder that boxes a plain member
    ccall(:jl_set_method_expansion_hook, Cvoid, (Any,), _expand_definition)
    ccall(:jl_set_module_end_hook, Cvoid, (Any,), _module_end_hook)
    ccall(:jl_set_image_methods_hook, Cvoid, (Any,), _image_methods_hook)
    _ENTRY_CURSOR[] = 0                  # the image's records are made again from the runtime's list
    # fully typed mode's hook (compiler §2.7): code that fails it reports through the library
    ccall(:jl_set_fully_typed_hook, Cvoid, (Any,), _fully_typed_hook)
    # the hints on MethodError where a trait is involved (traits §11.4)
    _runtime_site(Base.Experimental.register_error_hint, _method_error_hint, MethodError)
    # strict mode (traits §12.3): JULIA_TW_STRICT=1, the report after each package load
    _strict_init!()
    # the pirate's report (traits §12.2): by default, after a definition, a declaration and a load
    _report_init!()
    ccall(:jl_set_method_deletion_hook, Cvoid, (Any,), _deletion_hook)
end

# A trimmed build (traits §16; compiler §7.6) defines its program while it loads it, as a session does, but Julia
# runs every package's `__init__` only when the binary starts (an output that is not incremental). The library's
# hooks, which make a definition's methods (the kept forms, the forwarders) and check it, are installed at its load
# there too.
Base.JLOptions().trim != 0 && ccall(:jl_generating_output, Cint, ()) == 1 && __init__()

end # module
