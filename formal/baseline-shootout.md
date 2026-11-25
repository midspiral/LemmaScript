# Baseline Narrowing and Mutation Fuzzer Shootout (`midspiral/main` vs. PR #379)

This document compares two versions of LemmaScript on a shared set of 40 generated TypeScript programs where type narrowing interacts with imperative code (reassignment, in-place array/map/record mutation, loops, shadowing, discriminated unions, `null` vs. `undefined`, aliasing, and precondition-bearing calls). The goal is to measure which bugs the checked-reads prototype in PR #379 already fixes and which soundness or compilation gaps still need to be solved by the rewrite planned in midspiral/LemmaScript#387.

For each generated program and concrete input, the harness runs the TypeScript in Node to observe JavaScript's actual behavior, compiles the same program to Dafny, and asks Dafny two soundness checks:

- **False-proof check (`soundness-refuted`):** When JavaScript returns a value `v`, the harness asks Dafny to prove `result != v`. If Dafny verifies that claim, the translation silently contradicts JavaScript semantics.
- **Dropped-precondition check (`precondition-dropped`):** Some programs call a helper `guard(false, v)` carrying `//@ requires ok` inside comparisons or boolean chains. When JavaScript executes that call, Dafny must reject it; if Dafny verifies with zero errors, the translation dropped an operand JavaScript still evaluates.

Both branches ran the exact same 40-program seed (`--seed 1 --runs 40`). Three findings stand out before the detailed tables below:

1. **PR #379 fixes two critical soundness bugs present on `midspiral/main`:** mutating a narrowed optional array (`if (arr !== undefined) arr.push(v)`, midspiral/LemmaScript#350) and skipping the right-hand side of `x === guard(false, v)` when `x` is `undefined` (midspiral/LemmaScript#349). It also fixes compilation errors on reassignment narrowing (midspiral/LemmaScript#340) and `while`-loop presence checks (midspiral/LemmaScript#339).
2. **Two critical false-proof bugs remain on both branches:** mutating an array through an alias while the original variable is still read (`const b = a; b.push(v); return a.length`, where Dafny models arrays as independent values and proves the old length), and distinguishing `null` from `undefined` in `number | null | undefined` (midspiral/LemmaScript#304, where both encode as `Option.None`).
3. **PR #379 has a new write-back bug on optional array indexing:** writing `arr[0] = 10` inside `if (arr !== undefined && arr.length > 0)` emits `arr := arr.value[0 := 10]` without re-wrapping `Some(...)`, producing a Dafny type error.

## Run metadata

- **Tracking:** robertpenner/LemmaScript#47 (part of robertpenner/LemmaScript#43; Milestone 0 baseline scorecard for midspiral/LemmaScript#387).
- **Branches evaluated:**
  - `midspiral/main` (`f991de5`, current `someMatch` pipeline)
  - `midspiral/redesign-narrowing` (`261609a`, midspiral/LemmaScript#379 checked-reads prototype)
- **Harness revision for scorecard table:** `29d0636` (captured in `f1bbb2e`, 25 variants, single-sample `opt`-stage run). Subsequent hardening in `1201487` expanded the generator to 33 variants (adding empty-string/false/empty-array falsy traps, `!==`/`<=`/`||`/`?.`/call-arg guard positions, real nested-field reassignment, and post-branch reads on `nested-box-push` and `union-switch-mutate`), switched campaigns to stage-locked `fc.check` shrinking, and defaulted evaluation and `--case` replay to both `pre` and `opt` stages; the saved `.semantic.json` artifacts under `formal/shootout-artifacts/{main,pr379}/` were re-recorded with `pre`+`opt` checks (`stage: "both"`) and verified to replay deterministically.
- **Toolchain:** Node `v24.17.0`, Dafny `4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2`.
- **Exact CLI command (run at harness revision `29d0636`, identical on both branches):**

```sh
cd tools
npx tsx fuzz/narrowing-fuzz.ts --imperative --seed 1 --runs 40 --verify-timeout 15 --out <out-dir>
```

All 7 families were enabled: `reassign`, `mutation`, `loop-shadow`, `union`, `nullish-falsy`, `aliasing`, `guard-eval`.

## 1. Scorecard Summary

| Metric | `midspiral/main` (`f991de5`) | `midspiral/redesign-narrowing` (`261609a`) | Notes |
| --- | ---: | ---: | --- |
| Programs generated | 40 | 40 | Identical fixed-seed sample (`--seed 1 --runs 40`) |
| `dafny verify` calls | 111 | 127 | Specialized refutation + positive/precondition checks |
| Wall time | 156.0s | 259.8s | Local macOS arm64 |
| **Passed (refutation rejected + positive verified)** | **24** | **27** | +3 passing on PR #379 |
| **CRITICAL: `soundness-refuted`** | **6** (3 classes) | **5** (2 classes) | PR #379 fixes `#350`; both still prove false postconditions on live-alias mutation and `#304` |
| **CRITICAL: `precondition-dropped`** | **1** (1 class) | **0** | PR #379 fixes `#349` (`x === guard(false, v)`) |
| `semantic-mismatch` (unproved, not refuted) | 0 | 6 (1 class) | PR #379 compiles `#339` `while` loops that `main` rejected at resolve; unannotated loop cannot prove concrete sum |
| `dafny-resolve` (invalid Dafny emitted) | 9 (3 classes) | 1 (1 class) | PR #379 fixes `#340` and `#339` resolve; both fail `array-index-assign` (new PR #379 missing `Some(...)` wrap) |
| `rejected` (explicit compiler rejection) | 0 | 0 | Neither branch explicitly rejects live-alias mutation yet |
| `timeout` (`15s` cap) | 0 | 1 | `reassign/nested-field-reassign` timed out once on PR #379 |
| `invalid-ts` / `tool-error` | 0 / 0 | 0 / 0 | Zero generator or harness errors |

## 2. Failure Classes and Upstream Mapping

### `midspiral/main` (`f991de5`): 7 distinct failure classes

| Class | Severity / Oracle | Family / Label | Upstream tracking | Saved artifact |
| --- | --- | --- | --- | --- |
| #3 | **CRITICAL** (`precondition-dropped`) | `guard-eval/eq-rhs-guard-false` | Tracked: midspiral/LemmaScript#349 | [`main/3.ts`](./shootout-artifacts/main/3.ts), [`main/3.semantic.json`](./shootout-artifacts/main/3.semantic.json) |
| #5 | **CRITICAL** (`soundness-refuted`) | `aliasing/live-alias-mutation` | Related: midspiral/LemmaScript#267 (**new concrete refutation**: `const b = a; b.push(v); return a.length`) | [`main/5.ts`](./shootout-artifacts/main/5.ts), [`main/5.semantic.json`](./shootout-artifacts/main/5.semantic.json) |
| #6 | **CRITICAL** (`soundness-refuted`) | `mutation/opt-array-push` | Tracked: midspiral/LemmaScript#350 | [`main/6.ts`](./shootout-artifacts/main/6.ts), [`main/6.semantic.json`](./shootout-artifacts/main/6.semantic.json) |
| #7 | **CRITICAL** (`soundness-refuted`) | `nullish-falsy/null-vs-undefined-eq` | Tracked: midspiral/LemmaScript#304 | [`main/7.ts`](./shootout-artifacts/main/7.ts), [`main/7.semantic.json`](./shootout-artifacts/main/7.semantic.json) |
| #1 | `dafny-resolve` | `reassign/absent-to-present` | Tracked: midspiral/LemmaScript#340 (`v + 6` sees `Option<int>`) | (fixed in PR #379) |
| #2 | `dafny-resolve` | `loop-shadow/while-presence-countdown` | Tracked: midspiral/LemmaScript#339 (`total + cur` sees `Option<int>`) | (fixed at resolve in PR #379) |
| #4 | `dafny-resolve` | `mutation/array-index-assign` | **Newly surfaced:** `arr := i_arr_val[0 := 10]` (`LHS of assignment must denote a mutable variable`) | (still broken in PR #379) |

### `midspiral/redesign-narrowing` (`261609a`, PR #379): 5 distinct failure classes

| Class | Severity / Oracle | Family / Label | Upstream tracking | Saved artifact |
| --- | --- | --- | --- | --- |
| #4 | **CRITICAL** (`soundness-refuted`) | `aliasing/live-alias-mutation` | Related: midspiral/LemmaScript#267 (**still proves false postcondition on PR #379**) | [`pr379/4.ts`](./shootout-artifacts/pr379/4.ts), [`pr379/4.semantic.json`](./shootout-artifacts/pr379/4.semantic.json) |
| #5 | **CRITICAL** (`soundness-refuted`) | `nullish-falsy/null-vs-undefined-eq` | Tracked: midspiral/LemmaScript#304 (**still proves false postcondition on PR #379**) | [`pr379/5.ts`](./shootout-artifacts/pr379/5.ts), [`pr379/5.semantic.json`](./shootout-artifacts/pr379/5.semantic.json) |
| #3 | `dafny-resolve` | `mutation/array-index-assign` | **New PR #379 bug:** emits `arr := arr.value[0 := 10];` (`RHS of type seq<int> not assignable to LHS of type Option<seq<int>>`, missing `Some(...)` write-back wrapper) | [`pr379/3.ts`](./shootout-artifacts/pr379/3.ts), [`pr379/3.semantic.json`](./shootout-artifacts/pr379/3.semantic.json) |
| #2 | `semantic-mismatch` | `loop-shadow/while-presence-countdown` | Expected unannotated loop behavior (no false proof; Dafny cannot prove concrete loop sum without loop invariants) | (none) |
| #1 | `timeout` | `reassign/nested-field-reassign` | 15s cap exceeded once on PR #379 | (none) |

## 3. Deterministic Replay Verification

Every saved artifact in `formal/shootout-artifacts/` was replayed without reshrinking using:

```sh
cd tools
npx tsx fuzz/narrowing-fuzz.ts --case ../formal/shootout-artifacts/<branch>/<N>.semantic.json --verify-timeout 15
```

- On `midspiral/main` (`f991de5`): `main/3.semantic.json` (`precondition-dropped`), `main/5.semantic.json` (`soundness-refuted`), `main/6.semantic.json` (`soundness-refuted`), and `main/7.semantic.json` (`soundness-refuted`) all reproduced their exact original oracle verdicts (`exit 1`).
- On `midspiral/redesign-narrowing` (`261609a`): `pr379/3.semantic.json` (`dafny-resolve`, missing `Some(...)` wrap on `arr[0] = 10`), `pr379/4.semantic.json` (`soundness-refuted`, live-alias mutation), and `pr379/5.semantic.json` (`soundness-refuted`, `#304`) all reproduced their exact original oracle verdicts (`exit 1`).

## 4. Implications for Milestones 3 through 5

1. **Unified `Place` write-back (Milestone 3):** PR #379 fixed optional `.push` (`#350`) with a dedicated special case, yet missed optional index assignment (`arr[0] = v`, omitting the `Some(...)` wrapper). Routing all in-place updates through `Place` (`PIndex(PUnwrap(PVar("arr")), 0)`) enforces wrapper preservation across every mutation form (proved in `formal/narrowing-model.dfy` Theorem 3c).
2. **Precise live-alias rejection (Milestone 3):** Both branches silently prove `res != 1` for `const b = a; b.push(v); return a.length`, while `dead-source-move` (`return b.length`) and `read-only-alias` verify soundly. Implementing `alias-check.ts` eliminates this false-proof class without breaking read-only sharing or dead-source moves.
3. **`Nullish<T>` representation (Milestone 5):** Both branches still prove false postconditions on `number | null | undefined` (`#304`), confirming `Nullish<T>` (proved injective in `formal/narrowing-model.dfy` Theorem 4) is needed to close the remaining critical soundness gap.
