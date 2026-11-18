# TraitWorld

The library of trait-bound Julia. A trait is an open abstract type with a contract; a membership is an entry of Julia's type system. The library declares, checks and reports; the type system, dispatch and the compiler's side are Julia's, in `julia-next/`. It refuses to load on a Julia without memberships.

## What it provides

- **Declaring** (`src/trait.jl`, `src/implement.jl`, `src/contract.jl`):
  - `@trait X{P…} <: (A, …) begin … end`: operations with declared results, defaults, declared fields (`@const` for read-only), parameters by fields, equations of `Self`, `@input`, supertraits; `@default_dynamic` for a trait that erases by default.
  - `@implement X S`: a block of methods, `by f`, several traits, stated parameters, families (`S{T} where {T}`), closed abstract types and traits as members, `struct S <: X`.
- **Checking:** the checks at a declaration (completeness, results, fields, parameters, supertraits), with `ImplementError`; a member of a pattern checked at its first use; bounded methods (`@bounded`, `@unbounded`, `check_definitions`, `classify`, `check_at_box`), with `TraitUseError` (`src/check.jl`, `src/classify.jl`, `src/atbox.jl`).
- **The kept forms:** the box `Dynamic{X}` and the wrapper `Compiled` (Julia's `Core.Dynamic` and `Core.Compiled`), `compiled_for(x)` that makes the wrapper, `unwrap`, `like`, `withfields`; a trait that erases by default gets its methods at the kept forms and a forwarder that boxes a plain member (`src/dynamic.jl`, `src/compiled.jl`, `src/erasing.jl`).
- **`Callable{A, S}`** and `Dynamic{Callable{A, S}}` (`src/callable.jl`); intersections `All{X, Y, …}`.
- **Scopes:** `@trait_module`, with the options `facts`, `bounded`, `no_pirates`, `owner_only` (`src/scope.jl`).
- **Ownership and strict mode:** `@joint_owners`, `@owner_only`, `OwnershipError`, `PirateError`, `delete_membership`; `TraitWorld.strict!` and `JULIA_TW_STRICT=1` (`src/ownership.jl`, `src/strict.jl`, `src/report.jl`, `src/delete.jl`).
- **Fully typed mode and closed builds:** `@enforce_fully_typed`, `@warn_not_fully_typed`, `fully_typed`, `isfullytyped`, `@enforce_concrete_only`, `@warn_on_abstract`; `verify_main`, `add_entrypoints`, `make_executable`, `make_library` (`src/fullytyped.jl`, `src/build.jl`, `src/buildbase.jl`).
- **Compiling ahead** while a package is precompiled (`src/ahead.jl`; `JULIA_TW_AHEAD=0` turns it off).
- **Hints** on `MethodError` where a trait is involved (`src/hints.jl`).
- **BaseTraits** (`src/BaseTraits.jl`): `HasLength`, `Iterable`, `Indexable`, `MutableIndexable`, `Resizable`, `Keyed`, `Solvable`, `LinearOp`, `BoundedText`, `HasProperty`, with `asvector`, `IndexableVector`, `retain!`, `apply!`, `textbound`.

The library's own code is compiled by facts, as a trait module's is.

## Where it deviates from the design

- Every deviation, with its ID: the Deviations tables of the design repository's references.

## Running

From the workspace root:

```sh
source env.sh
julia-next/julia --startup-file=no --project=TraitWorld TraitWorld/test/runtests.jl
```

`test/runtests.jl` runs each test file in a module of its own. The workloads that gate the library are in the experiments repository, `experiments/implementation/workloads/`.

## Results

The current numbers, each against plain Julia or Python, are in the design repository's `writeup/design/evidence.md`. The suite's last result is in its `writeup/state.md` §3; on `julia-next` the suite has 93 testsets.

## The design

- The design: the design repository's `writeup/reference/`: `traits.md` (the language), `lowering.md` (what this library does), `compiler.md` (Julia's side), `facts.md`.
- Teaching: `writeup/intro/traits-for-julia.md`; the lessons of the ports: `writeup/intro/porting.md`.
