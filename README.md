# TraitWorld

TraitWorld is the trait language of trait-bound Julia, as a package. It provides traits (`@trait`), implementations (`@implement`), trait modules (`@trait_module`), values in trait code (`Compiled`, `Dynamic`, `Kept`), functions at a declared signature (`Callable`), definition checking, fully typed mode, `verify_main` and strict mode.

It runs only on the patched Julia of the design repository (`../julia-1.13/`). That build adds the facts mode, which compiles trait modules, and hooks the library uses: method definitions, image loads and type printers.

## Where the design is

The design repository's references are the source of truth. Each one has a Deviations table, which lists where this package falls short of it.
- [`traits.md`](../writeup/reference/traits.md): the language, its rules and its messages.
- [`lowering.md`](../writeup/reference/lowering.md): how TraitWorld builds the language, file by file.
- [`facts.md`](../writeup/reference/facts.md): what code compiled by facts may assume, and strict mode.
- [`compiler.md`](../writeup/reference/compiler.md): the interfaces of the patched Julia that TraitWorld uses.

For a tutorial, read [`../writeup/intro/`](../writeup/intro/). Its examples run in `../experiments/docs-examples/`.

## How to run

```bash
J=../julia-1.13/julia
$J --project=. -e 'using Pkg; Pkg.test()'                                  # the product setting
$J -J ../julia-1.13/usr/lib/julia/facts/sys.so --project=. -e 'using Pkg; Pkg.test()'   # the test bed `all`
```

Every suite of the design repository, with this package's under both settings, runs through `../experiments/checks/run_all.sh <tag>`. Its logs are in `../experiments/checks/logs/<tag>/`.

## Switches

| Variable | Effect |
|---|---|
| `JULIA_TW_STRICT=1` | strict mode on ([facts §10](../writeup/reference/facts.md#10-pirates-and-strict-mode)); also `TraitWorld.strict!()` |
| `JULIA_TW_ALL_FRAMES=1` | error backtraces keep TraitWorld's own frames |
| `JULIA_TW_DEBUG=1` | the machinery's slow paths print as they run |
| `JULIA_TW_DEFCHECK=0` | no definition checking at a trait module's end (for measurement) |
| `JULIA_TW_AHEAD=0` | nothing compiled ahead from declarations (for measurement) |
| `JULIA_TW_KEEP_COMPILED=0` | package images do not keep upstream code compiled by facts (for measurement) |
| `JULIA_TW_HOOKS=0` | the runtime's hooks are not installed: no checks at definitions and loads, no lowering front (for diagnosis) |

## Layout

- `src/TraitWorld.jl`: the module, its `__init__` and its precompile workload.
- `src/trait.jl`, `src/implement.jl`: `@trait` and `@implement`.
- `src/trait_module.jl`: `@trait_module`, bounded functions, the module's end, and the front before Julia's lowering for statements evaluated after it.
- `src/core.jl`, `src/entry.jl`, `src/checks.jl`: trait objects, kept values, entries and workers, the first-call check.
- `src/defcheck.jl`, `src/concrete.jl`, `src/verify.jl`, `src/certificate.jl`: definition checking, fully typed mode, `verify_main`.
- `src/ownership.jl`, `src/strict.jl`, `src/hooks.jl`: ownership, strict mode, the runtime's hooks.
- `src/ahead.jl`, `src/untyped.jl`: compiling ahead from declarations; entries for untyped callers.
- `src/BaseTraits.jl`: collection traits for Base's concepts.
