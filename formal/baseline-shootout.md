# Narrowing and Mutation Fuzzer Shootout (`midspiral/main` vs. PR #379 vs. Hybrid M0–M4)

This document compares three versions of LemmaScript on a shared fixed-seed corpus of generated TypeScript programs where type narrowing interacts with imperative code (reassignment, in-place array/map/record mutation, loops, shadowing, discriminated unions, `null` vs. `undefined`, aliasing, and precondition-bearing calls):

- `midspiral/main` (`f991de5`, baseline `someMatch` pipeline)
- `midspiral/redesign-narrowing` (`261609a`, midspiral/LemmaScript#379 checked-reads prototype)
- **Hybrid rewrite Milestones 0–4** (`4fb1af6`: self-verified `Place` write-back, live-alias mutation rejection, checked reads, and precondition-preserving optional comparisons; midspiral/LemmaScript#387)

For each generated program and concrete input, the harness runs the TypeScript in Node to observe JavaScript's actual behavior, compiles the same program to Dafny, and asks Dafny two soundness checks:

- **False-proof check (`soundness-refuted`):** When JavaScript returns a value `v`, the harness asks Dafny to prove `result != v`. If Dafny verifies that claim, the translation silently contradicts JavaScript semantics.
- **Dropped-precondition check (`precondition-dropped`):** Some programs call a helper `guard(false, v)` carrying `//@ requires ok` inside comparisons or boolean chains. When JavaScript executes that call, Dafny must reject it; if Dafny verifies with zero errors, the translation dropped an operand JavaScript still evaluates.

Four findings stand out before the detailed tables below:

1. **PR #379 fixed `#350` and `#349` relative to `midspiral/main`,** plus compilation errors on `#340` and `#339`, while introducing a missing `Some(...)` write-back bug on optional array index assignment (`arr[0] = 10`).
2. **Both `midspiral/main` and PR #379 left two critical false-proof bugs open:** mutating an array through a live alias (`const b = a; b.push(v); return a.length`, where Dafny proves the old length), and distinguishing `null` from `undefined` in `number | null | undefined` (midspiral/LemmaScript#304).
3. **Hybrid Milestones 0–4 (`4fb1af6`) eliminate every `precondition-dropped` (`0`), `dafny-resolve` (`0`), and `timeout` (`0`) failure on the hardened 33-variant `pre`+`opt` corpus,** convert `aliasing/live-alias-mutation` from a silent false proof to an explicit fail-closed compiler rejection (`rejected`), and pass 37/47 generated/shrunk runs (306 `dafny verify` calls, 0 IR violations).
4. **Only one critical soundness class remains:** `nullish-falsy/null-vs-undefined-eq` (midspiral/LemmaScript#304), intentionally deferred to Milestone 5 (`Nullish<T>`).

## Run metadata

- **Tracking:** robertpenner/LemmaScript#47 (part of robertpenner/LemmaScript#43; baseline and post-rewrite scorecard for midspiral/LemmaScript#387).
- **Branches evaluated:**
  - `midspiral/main` (`f991de5`, baseline `someMatch` pipeline)
  - `midspiral/redesign-narrowing` (`261609a`, midspiral/LemmaScript#379 checked-reads prototype)
  - `hybrid-m0-m4` (`4fb1af6`, Milestones 0–4)
- **Harness revisions:** The baseline `main` and PR #379 columns ran at `29d0636` (25 variants, single-sample `opt`-stage run). Subsequent hardening in `1201487` expanded the generator to 33 variants (adding empty-string/false/empty-array falsy traps, `!==`/`<=`/`||`/`?.`/call-arg guard positions, real nested-field reassignment, and post-branch reads on `nested-box-push` and `union-switch-mutate`), switched campaigns to stage-locked `fc.check` shrinking, and defaulted evaluation and `--case` replay to both `pre` and `opt` stages. The `hybrid-m0-m4` column ran on this hardened 33-variant `pre`+`opt` harness, and all 7 saved baseline artifacts under `formal/shootout-artifacts/{main,pr379}/` were replayed directly against `4fb1af6`.
- **Toolchain:** Node `v24.17.0`, Dafny `4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2`.
- **Exact CLI command (identical across all three runs):**

```sh
cd tools
npx tsx fuzz/narrowing-fuzz.ts --imperative --seed 1 --runs 40 --verify-timeout 15 --out <out-dir>
```

All 7 families were enabled: `reassign`, `mutation`, `loop-shadow`, `union`, `nullish-falsy`, `aliasing`, `guard-eval`.

## 1. Scorecard Summary

| Metric | `midspiral/main` (`f991de5`, 25 variants / `opt`) | `PR #379` (`261609a`, 25 variants / `opt`) | `Hybrid M0–M4` (`4fb1af6`, 33 variants / `pre`+`opt`) | Notes |
| --- | ---: | ---: | ---: | --- |
| Programs evaluated (incl. shrink steps) | 40 | 40 | 47 | `--seed 1 --runs 40` (hardened harness runs `fc.check` shrink steps on failing classes) |
| `dafny verify` calls | 111 | 127 | 306 | Specialized refutation + positive/precondition checks (`pre`+`opt` on M0–M4) |
| Wall time | 156.0s | 259.8s | 1795.1s | Local macOS arm64 (`pre`+`opt` runs 2x stages + shrink) |
| **Passed (refutation rejected + positive verified)** | **24** | **27** | **37** | Every non-`#304`, non-live-alias, non-unannotated-loop program passes on both `pre` and `opt` |
| **CRITICAL: `soundness-refuted`** | **6** (3 classes) | **5** (2 classes) | **2** (1 class) | Only `#304` (`null-vs-undefined-eq`) remains; `#350` passes, live-alias mutation fails closed |
| **CRITICAL: `precondition-dropped`** | **1** (1 class) | **0** | **0** | `#349` fixed across `===`, `!==`, and relational comparisons (`pre`+`opt`) |
| `semantic-mismatch` (unproved, not refuted) | 0 | 6 (1 class) | 6 (1 class) | Expected unannotated `#339` `while` loop without loop invariants |
| `dafny-resolve` (invalid Dafny emitted) | 9 (3 classes) | 1 (1 class) | **0** | `#340`, `#339`, and `array-index-assign` all emit valid, verifying Dafny |
| `rejected` (explicit compiler rejection) | 0 | 0 | **2** (1 class) | Live-alias mutation rejected soundly by `alias-check.ts` instead of proving false postconditions |
| `timeout` (`15s` cap) | 0 | 1 | **0** | Zero timeouts across all 306 Dafny calls |
| `invalid-ts` / `tool-error` | 0 / 0 | 0 / 0 | **0 / 0** | Zero generator, IR-invariant, or harness errors |

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

### `hybrid-m0-m4` (`4fb1af6`, Milestones 0–4): 3 non-passing classes (0 unexpected regressions)

| Class | Severity / Oracle | Family / Label | Status | Saved artifact |
| --- | --- | --- | --- | --- |
| #2 | **CRITICAL** (`soundness-refuted`) | `nullish-falsy/null-vs-undefined-eq` | Deferred to Milestone 5 (midspiral/LemmaScript#304, `Nullish<T>`) | [`hybrid-m4/2.ts`](./shootout-artifacts/hybrid-m4/2.ts), [`hybrid-m4/2.semantic.json`](./shootout-artifacts/hybrid-m4/2.semantic.json) |
| #3 | `rejected` (sound fail-closed) | `aliasing/live-alias-mutation` | **Fixed** (was `soundness-refuted` on both `main` and PR #379; now explicitly rejected by `alias-check.ts`) | [`hybrid-m4/3.ts`](./shootout-artifacts/hybrid-m4/3.ts), [`hybrid-m4/3.semantic.json`](./shootout-artifacts/hybrid-m4/3.semantic.json) |
| #1 | `semantic-mismatch` | `loop-shadow/while-presence-countdown` | Expected unannotated loop behavior (no false proof; Dafny cannot prove concrete loop sum without loop invariants) | (none) |

## 3. Deterministic Replay Verification

Every saved artifact in `formal/shootout-artifacts/` was replayed without reshrinking using:

```sh
cd tools
npx tsx fuzz/narrowing-fuzz.ts --case ../formal/shootout-artifacts/<branch>/<N>.semantic.json --verify-timeout 15
```

- On `midspiral/main` (`f991de5`): `main/3.semantic.json` (`precondition-dropped`), `main/5.semantic.json` (`soundness-refuted`), `main/6.semantic.json` (`soundness-refuted`), and `main/7.semantic.json` (`soundness-refuted`) all reproduced their exact original oracle verdicts (`exit 1`).
- On `midspiral/redesign-narrowing` (`261609a`): `pr379/3.semantic.json` (`dafny-resolve`, missing `Some(...)` wrap on `arr[0] = 10`), `pr379/4.semantic.json` (`soundness-refuted`, live-alias mutation), and `pr379/5.semantic.json` (`soundness-refuted`, `#304`) all reproduced their exact original oracle verdicts (`exit 1`).
- On `hybrid-m0-m4` (`4fb1af6`):
  - `main/3.semantic.json` (`#349` `precondition-dropped`): **passed** (`exit 0`, 2 checks verified).
  - `main/6.semantic.json` (`#350` `opt-array-push` `soundness-refuted`): **passed** (`exit 0`, 4 checks verified).
  - `pr379/3.semantic.json` (`array-index-assign` `dafny-resolve`): **passed** (`exit 0`, 4 checks verified).
  - `main/5.semantic.json` and `pr379/4.semantic.json` (`live-alias-mutation` `soundness-refuted`): **explicitly rejected** (`rejected: Live-alias mutation in target`, sound fail-closed).
  - `main/7.semantic.json` and `pr379/5.semantic.json` (`#304` `null-vs-undefined-eq`): still `soundness-refuted` (deferred to Milestone 5).

## 4. Remaining Work (Milestone 5)

1. **Completed in Milestones 3–4 (`4fb1af6`):** Unified `Place` write-back (`places.ts`, `place-lowering.ts`, `transform.ts`), precise live-alias mutation rejection (`alias-check.ts`, `alias-check-pass.ts`), checked reads (`checked-reads.ts`, Dafny `.value` and Lean dependent `if _h :` + `.get (by grind)`), and precondition-preserving optional comparisons (`#349`). Together these close 9 of 10 open upstream narrowing/mutation issues (`#268`, `#339`, `#340`, `#342`, `#349`, `#350`, `#352`, `#353`, `#354`) with 0/91 example drift and 35/35 case studies passing.
2. **Deferred to Milestone 5 (`Nullish<T>`):** Both baseline branches and `4fb1af6` still prove false postconditions on `number | null | undefined` (midspiral/LemmaScript#304), confirming `Nullish<T>` (proved injective in `formal/narrowing-model.dfy` Theorem 4) as the final soundness milestone.
