# F* backend (experimental)

The F* backend verifies a pure, total subset of LemmaScript. It supports functions returning functions, arbitrary function application such as `makeAdder(n)(x)`, immutable captures, and generic composition. Function `requires` and `ensures` become checked F* `Pure` signatures, so callers can use the postcondition directly. This backend does not yet implement the full fragment in [SPEC.md](SPEC.md); unsupported constructs fail generation.

## Running it

Install F* using its [official installer](https://github.com/FStarLang/FStar/blob/master/INSTALL.md); the tested release and CI pin are [v2026.09.20](https://github.com/FStarLang/FStar/releases/tag/v2026.09.20), with bundled Z3 4.13.3. If already installed, check discovery with `fstar.exe --version`. Set `FSTAR_EXE` to an absolute executable path if it is not on PATH.

From this checkout:

```sh
npm run build
node tools/dist/lsc.js gen   --backend=fstar examples/fstarClosures.ts
node tools/dist/lsc.js check --backend=fstar examples/fstarClosures.ts
node tools/dist/lsc.js regen --backend=fstar examples/fstarClosures.ts
```

An installed package exposing `lsc` uses the same arguments. `gen` needs no F* installation; `check` and `regen` do. `gen-check` checks the additions-only diff without verification, and `regen --no-verify` merges without verification. With no file argument, `gen`, `gen-check`, and `check` use the existing `LemmaScript-files.txt` batch mechanism. `tools/check.sh fstar` is also available.

Put `//@ backend fstar` at the top of a source to skip it when running the Dafny and Lean backends. Pass `--backend=fstar` explicitly: Dafny remains the default. The repository's F* CI job verifies all four `examples/fstar*.ts` files and checks generated-file drift; the reusable external `verify.yml` workflow has not yet been extended to F*.

## Examples

| Source | What is checked |
| --- | --- |
| [fstarClosures.ts](examples/fstarClosures.ts) | A returned adder's pointwise law, direct application of returned closures, repeated application of a captured closure. |
| [fstarComposition.ts](examples/fstarComposition.ts) | Composition over three arbitrary types, a concrete caller's arithmetic postcondition, a callback's quantified guarantee. |
| [fstarArrays.ts](examples/fstarArrays.ts) | A closure capturing a generic array; map preserves length and filtering cannot increase it. Its working `.fst` also proves map fusion by induction, as a hand-written proof addition. |
| [fstarIteration.ts](examples/fstarIteration.ts) | A decreasing recursive iterator preserves a callback guarantee; returning and applying the iterator retains its postcondition. |

These examples use general application that the current Dafny/Lean lowering rejects. They demonstrate the implemented F* path, not an inherent inability of Dafny or Lean to reason about these programs. See [DESIGN_FSTAR.md](DESIGN_FSTAR.md) for the comparison and subsequent milestones.

## Supported fragment

| Construct | Representation and limits |
| --- | --- |
| Integer `number`, `bigint`, `nat`, boolean | F* `int`, `int`, `nat`, `bool`. Integer `+`, `-`, `*`, ordering and numeric/boolean equality; boolean operations and conditions. Number literals must be safe integers. |
| Generic parameters, simple aliases | Implicit F* type parameters and expanded non-generic aliases. Constrained/defaulted generics and generic parameters shadowing aliases are rejected. |
| Function values | Total, pure arrows; typed arrow lambdas and immutable captures, including arrays. Zero-argument functions take F* `unit`. No function reference equality. |
| Control flow | Immutable local bindings, returns, conditional expressions, and `if` branches that are empty or return. Nonempty fallthrough branches, loops, and mutation are rejected. |
| Arrays | Finite dense lists, literals, length, indexing with proven bounds. Runtime reference equality is rejected; specifications use mathematical equality. |
| Array combinators | Unary `map`, `filter`, `every`, `some`; binary `reduce` with an explicit initial accumulator, preserving left-fold direction. No index/array callback parameters or `thisArg`. |
| Specifications | `requires`, `ensures`, `decreases`, checked `assert`, `forall`, `exists`, implication/equivalence, array membership. `\result` is a real result binder, including function-valued results. Contracts belong on top-level functions; nested lambda contracts are rejected. |
| Recursion | Same-function recursion with F* termination checking; optional explicit `decreases`. Mutual recursion is rejected. |

Use explicit parameter types on lambdas. Explicit lambda return types are advisable where shared inference cannot determine them. Only the listed array methods are recognized; there is no general method dispatch. Optional values, strings, records, tagged unions, classes, mutable captures, division/remainder, floats, async, exceptions, externs/cross-file calls, `assume`, `havoc`, `autohavoc`, and statement-level `skip` are outside this first subset. Destructured parameters and standalone lexical blocks are rejected. Module constants must be scalar; arrays are supported as parameters and locals, since escaped module arrays could be mutated before a verified call. Executable module-level statements are also rejected. Use `requires`/`ensures`; the existing `contract` annotation is not supported here.

## Proof ownership and regeneration

For `examples/fstarClosures.ts`, generation creates `LS.MfstarClosures_f14fb73fccf0.fst.gen` and `LS.MfstarClosures_f14fb73fccf0.fst` beside the TS file. The name combines an escaped stem and a digest of the path relative to the nearest config/tsconfig directory (or the source directory if neither exists). It is stable across checkout relocation with the same project layout; changing that root or moving/renaming a file may change the name. `proof-dir` currently applies only to Dafny.

The `.fst.gen` is generated and must never be hand-edited. The working `.fst` contains generated lines plus hand-written proofs; `check` enforces an additions-only diff and verifies that working file. After changing TS, use `regen` to preserve additions through a three-way merge. `.fst.base` and `.fst.merged` are recovery artifacts: a conflict restores the proof and keeps the old anchor, while a clean merge followed by verification failure advances the anchor to the generation actually merged. A successful regen clears the anchor, including with `--no-verify`. Do not delete the proof or recovery state to make regeneration pass.

Proof additions must preserve program behavior: add checked lemmas, assertions and ghost reasoning. As with the Dafny workflow, an additions-only textual diff alone cannot establish that arbitrary inserted code is a semantics-preserving proof. This remains a reviewed trust boundary.

## Verification and trust boundary

The runner verifies a fresh copy of the working module in a temporary directory with `--force --report_assumes error`. It does not load adjacent `.checked` caches or project modules, and rejects `.fsti` companions. This initial single-module backend only relies on the installed F* standard library. Missing executables, nonzero exits, and timeouts fail the command; a printed “Verified module” line is not treated as success on its own.

`--time-limit=30` sets a 30-second process deadline. Resource tuning through `--extra-flags` is restricted to non-negative integer values for `--fuel`, `--ifuel`, `--max_fuel`, `--max_ifuel`, `--z3rlimit`, `--z3rlimit_factor`, and `--z3seed`. Z3 resource limits are not seconds. Source option directives, declaration attributes, admissions and unsafe casts are rejected in working proofs. This conservative policy can be relaxed deliberately when richer proof automation is supported.

TypeScript still executes the program. Numbers use LemmaScript's idealized integer model, not JavaScript IEEE-754 arithmetic; overflow, NaN and infinities are not established by these proofs. Arrays must be dense, standard arrays and stay immutable during the verified computation. Function arguments from unverified TS callers are assumed pure, terminating, and compliant with their specifications; a TS arrow type cannot establish those properties. The translator, model assumptions, proof additions, installed F* libraries/verifier, and SMT solver are trusted. Named dependent callback types, domain-restricted callbacks, recursive tree combinators, and effectful callbacks remain future work.
