# TraitWorld on the unified build

Traits as abstract types: a trait is an open abstract type with a contract, a membership an
entry of Julia's type system. This branch (`unified`) is the library for Julia's unified build,
branch `unified` of the julia repository; it starts fresh and shares no code with the prototype
on branch `main`, which runs on `trait-world-1.13`.

The design is in the design repository's references: `writeup/reference/traits.md` (the
language), `lowering.md` (what this library does), `compiler.md` (Julia's side). Where the code
falls short of them, the references' Deviations tables say so.

## What is built (stage W-106, the first slice)

- `@trait X{P…} <: (A, …) begin … end`: operations with declared results, defaults, declared
  fields (`@const` for read-only), parameters by fields, equations of `Self` or statement,
  `@input`; the trait's method for each operation; the contract on the trait's `TypeName`;
  `Dynamic{X}`'s membership.
- `@implement X S`, with a block of methods, `by f`, several traits, stated parameters,
  families (`S{T} where {T}`), closed abstract types and traits as members, `struct S <: X`.
- The checks at a declaration (completeness, results, fields, parameters, supertraits), with
  `ImplementError`; a member of a pattern checked at its first use, through the runtime's member
  hook at dispatch.
- `Dynamic{X}`, `unwrap`, `like`, `withfields`.

## What later stages added

- W-109: the classification of methods as fully bounded or open; `check_definitions`.
- W-111: the attribute (`Compiled`, `Dynamic`), the casts and `keep` (Julia's), `@trait_module`,
  `detect_dynamic_fallbacks`, `detect_unused_casts`.
- W-113: `Callable{A, S}` (Julia's), `Dynamic{Callable{A, S}}`.
- W-114: fully typed mode (`@enforce_fully_typed`, `@warn_not_fully_typed`, `fully_typed`,
  `isfullytyped`), concrete parts (`@enforce_concrete_only`, `@warn_on_abstract`); ownership
  (`@joint_owners`, `OwnershipError`) and pirates; strict mode (`TraitWorld.strict!`,
  `JULIA_TW_STRICT=1`, `PirateError`); hints on `MethodError`; compiling ahead while a package is
  precompiled (`JULIA_TW_AHEAD=0` turns it off); `verify_main`; BaseTraits (`HasLength`,
  `Iterable`, `Indexable`, `MutableIndexable`, `Resizable`, `Keyed`, `Solvable`, `LinearOp`,
  `BoundedText`, `asvector`, `retain!`).
- W-151 (stage 1 of the next iteration; a prototype of D-1 and D-3, not in force: traits T-113, T-114,
  lowering L-59): the wrapper `Compiled` that `TraitWorld.ByType.compiled_for(x)` returns, a member of
  every trait its object is in; `@erasing` (a trait's default as the method at the kept forms and a
  forwarder that boxes a plain member; `@default_dynamic` sets no compiler bit); `convert` into
  `Dynamic{X}`; `check_at_box` (the method read at the box), which `check_definitions` and `bounded` use.

## Running

```sh
source env.sh
julia-unified/julia --startup-file=no --project=TraitWorld TraitWorld/test/runtests.jl
```

The workloads that gate the first slice are in the experiments repository,
`experiments/implementation/workloads/`.
