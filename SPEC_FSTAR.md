# F* backend (experimental)

The F* backend verifies LemmaScript's mathematical value model, including higher-order functions, local mutation, loops, records, tagged unions, classes, arrays, strings, maps and sets. Function `requires` and `ensures` become checked F* `Ghost` signatures; function values use `GTot` arrows, so callers can use returned-closure guarantees directly. TypeScript remains the executable program. The F* model is for verification, not code extraction.

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

Put `//@ backend fstar` at the top of a source to select only F*, or `//@ backend dafny,fstar` to allow both backends. Pass `--backend=fstar` explicitly: Dafny remains the default. The repository's F* CI job verifies every top-level `examples/*.ts` file and checks generated-file drift; the reusable external `verify.yml` workflow has not yet been extended to F*.

`./regen-fstar.sh` builds the compiler, regenerates every example while preserving proof additions, and verifies each working proof. It reports failures and backend skips as errors. `./regen-fstar.sh --no-verify` only regenerates; resource options such as `--time-limit=120` are forwarded to `lsc regen`.

## Examples

| Source | What is checked |
| --- | --- |
| [fstarClosures.ts](examples/fstarClosures.ts) | A returned adder's pointwise law, direct application of returned closures, repeated application of a captured closure. |
| [fstarComposition.ts](examples/fstarComposition.ts) | Composition over three arbitrary types, a concrete caller's arithmetic postcondition, a callback's quantified guarantee. |
| [fstarArrays.ts](examples/fstarArrays.ts) | A closure capturing a generic array; map preserves length and filtering cannot increase it. Its working `.fst` also proves map fusion by induction, as a hand-written proof addition. |
| [fstarIteration.ts](examples/fstarIteration.ts) | A decreasing recursive iterator preserves a callback guarantee; returning and applying the iterator retains its postcondition. |
| [fstarCompiler.ts](examples/fstarCompiler.ts) | An optimizing compiler returns continuation-passing closures, with semantic preservation for every environment and continuation. It checks constant folding, zero multiplication and lexical `let` bindings using exact `bigint` values. |

All 76 top-level examples generate and verify with F*. The other examples exercise the shared language fragment; the working [F* companions](#proof-ownership-and-regeneration) include proofs of binary search, sorting, permutation invariance, stack traversal and collection algorithms. Source contracts and explicit trust annotations are preserved.

The five examples above use general application that the current Dafny/Lean lowering rejects. They demonstrate the implemented F* path, not an inherent inability of Dafny or Lean to reason about these programs. See [DESIGN_FSTAR.md](DESIGN_FSTAR.md) for the comparison and subsequent milestones.

## Supported fragment

| Construct | Representation and limits |
| --- | --- |
| Numbers | Mathematical `int`, `nat`, `real`; `bigint` retains signed truncating division/remainder semantics. Bare numeric division is real division; `Math.floor(a/b)` rounds downward. Unsafe integer literals are rejected. |
| Strings | Sequences of UTF-16 code units, including indexing, slicing, concatenation, searching and trimming. Unicode case conversion is a deterministic unconstrained library abstraction. |
| Arrays | `FStar.Sequence`, with checked indexing, value updates, slicing, searching, map/filter/fold and sorting. Sorting requires a total preorder and preserves multiplicities. Runtime array identity comparison is rejected. |
| Maps and sets | F* finite maps/sets. String keys use a proved sequence-to-list encoding to obtain decidable key equality. Iteration follows the existing unordered collection model. |
| Data types | Options, tuples, records, tagged unions, enums, aliases and generics. Optional record fields default to `None`. Opaque values have no observable constructors. |
| Functions | Pure, total ghost arrows, immutable captures, general application, function-valued records and returned functions. No captured-state mutation or function identity comparison. |
| Control flow | Mutable locals and collection updates become fresh value bindings; conditionals and switches preserve scope. Loops become total recursive continuations, including break, continue and early return. |
| Classes | Methods receive an explicit record representing `this` and return a result/state pair. Postconditions observe the updated state. This is not a shared-heap or aliasing model. |
| Specifications | `requires`, `ensures`, `assert`, quantifiers, implication/equivalence, membership, loop invariants and decreases. Postconditions retain a result binder, including function-valued results. |
| Explicit trust | `extern`, `impure`, `havoc`, `autohavoc` and `assume` retain their source meaning. See the trust boundary below. |

Loop invariants are preconditions of the recursive continuation. The emitter infers simple counter decreases; other loops expose a named `<function>_loopN_measure` helper to define and prove in the working `.fst`. Self recursion uses an explicit decreases clause or a suitable size/structural measure checked by F*. `preorder` demonstrates a hand-written pending-work measure. Termination obligations are never admitted.

Use explicit lambda parameter types where inference cannot recover them. Array callbacks are unary except initialized `reduce` and sort comparators, which are binary. Index/array callback parameters and `thisArg` are rejected. Generic parameters shadowing aliases, constrained/defaulted generics, default/rest parameters, named-function parameter destructuring, nested lambda contracts, statement-level `skip`, `contract`, mutual recursion and `await` remain unsupported. An async inline handler without `await` is modeled synchronously; Promise scheduling is outside the model. Module constants must be scalar, and executable module statements need an explicit extraction boundary.

## Proof ownership and regeneration

For `examples/fstarClosures.ts`, generation creates `examples/fstarClosures.fst.gen` and `examples/fstarClosures.fst` beside the source, keeping its basename. The internal module declaration still combines an escaped stem and a digest of the source path relative to the nearest config/tsconfig directory (or the source directory if neither exists). The verifier copies the proof to a temporary filename matching that declaration; use `lsc check --backend=fstar` to verify repository companions. `proof-dir` currently applies only to Dafny.

Commands automatically move companions from the previous `fstar/` subdirectory or `LS.M<stem>_<digest>.fst` filenames, preserving their contents and any baseline, recovery or interface files. If multiple layouts contain artifacts for a source, the command stops before changing any set; reconcile them before rerunning. The internal module name survives checkout relocation with the same layout, but changing the config root or moving/renaming the TS source may change it.

The `.fst.gen` is generated and must never be hand-edited. The working `.fst` contains generated lines plus hand-written proofs; `check` enforces an additions-only diff and verifies that working file. After changing TS, use `regen` to preserve additions through a three-way merge. `.fst.base` and `.fst.merged` are recovery artifacts: a conflict restores the proof and keeps the old anchor, while a clean merge followed by verification failure advances the anchor to the generation actually merged. A successful regen clears the anchor, including with `--no-verify`. Do not delete the proof or recovery state to make regeneration pass.

Both companions are tracked: `.fst.gen` supplies the previous generation for merging, while `.fst` retains proof additions. They are identical when automatic verification needs no additions. A separate generated-program/handwritten-proof format is future design work; the current layout still uses this pair.

Proof additions must preserve program behavior: add checked lemmas, assertions and ghost reasoning. As with the Dafny workflow, an additions-only textual diff alone cannot establish that arbitrary inserted code is a semantics-preserving proof. This remains a reviewed trust boundary.

## Verification and trust boundary

The runner copies the working module and packaged [LS.Runtime.fst](tools/fstar/LS.Runtime.fst) into a fresh temporary directory. It explicitly verifies the runtime with `--force --cache_checked_modules --report_assumes error`, then verifies the working module against that newly checked dependency. This matters: merely including an unchecked F* dependency can load it laxly. Adjacent project caches, unchecked project modules and `.fsti` companions cannot replace the implementation. Missing executables, nonzero exits and timeouts fail the command.

Deterministic source externs become explicit `assume val` declarations with their contracts. Impure calls and havoc sites receive invocation/call-site/iteration traces so separate evaluations cannot be equated by extensionality. Source `assume` remains an explicit assumption and is reported by F*; it is not a discharged obligation. Unicode case conversion has an explicit uninterpreted deterministic declaration with no assumed output properties. The runtime's classical decision helper relies on F*'s foundational standard library. None of these abstractions establish the behavior of unverified external implementations.

Proof additions may not add assumptions, admissions, unsafe casts, declaration attributes or source option directives. The sole allowed attribute is `opaque_to_smt`, which hides a checked body from automatic unfolding while retaining its checked contract. The checker compares generated and working trust declarations and enforces an additions-only diff. `--extra-flags` accepts only non-negative integer resource values for `--fuel`, `--ifuel`, `--max_fuel`, `--max_ifuel`, `--z3rlimit`, `--z3rlimit_factor` and `--z3seed`. Z3 resource limits are not seconds; `--time-limit` bounds each verifier process.

Numbers use LemmaScript's idealized arithmetic, not JavaScript IEEE-754 overflow, NaN or infinities. Arrays must be dense standard arrays. Updates use value semantics; alias-visible mutation, sparse arrays, shared heap effects and scheduling are not established. Callback arguments from unverified TS callers must be pure, terminating and compliant with their contracts. The compiler, model assumptions, reviewed proof additions, installed F* libraries/verifier and SMT solver remain trusted. Named dependent callback types and domain-restricted recursive combinators remain future work.
