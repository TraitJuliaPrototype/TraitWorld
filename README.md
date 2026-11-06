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

## Running

```sh
source env.sh
julia-unified/julia --startup-file=no --project=TraitWorld-unified TraitWorld-unified/test/runtests.jl
```

The workloads that gate the first slice are in the experiments repository,
`experiments/unification/workloads/`.
