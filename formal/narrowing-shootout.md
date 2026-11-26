# Narrowing and Mutation Fuzzer Shootout (`v0.6.12` vs. PR #379 vs. PR #388 vs. Milestone 5)

This document compares four versions of LemmaScript on a shared fixed-seed corpus of generated TypeScript programs where type narrowing interacts with imperative code (reassignment, in-place array/map/record mutation, loops, shadowing, discriminated unions, `null` vs. `undefined`, aliasing, and precondition-bearing calls):

- `v0.6.12` (`f991de5`, pre-rewrite `someMatch` pipeline)
- `PR #379` (`261609a`, midspiral/LemmaScript#379 checked-reads prototype)
- **PR #388 / Hybrid Milestones 0–4** (`0d96885`, measured on `4fb1af6`: self-verified `Place` write-back, live-alias mutation rejection, checked reads, and precondition-preserving optional comparisons; midspiral/LemmaScript#387)
- **PR #391 / Milestone 5 (`Nullish<T>`)** (`57aaf21` / `v0.6.14` `59e3366`, measured on `3ddd9d9` and hardened in `3540adc`: selective three-case `Nullish<T>` datatype for `T | null | undefined`, preserving `null !== undefined` while keeping `Option<T>` for single-sentinel `T | undefined` and `T | null`; midspiral/LemmaScript#304, example in [`examples/nullish.ts`](../examples/nullish.ts))

For each generated program and concrete input, the harness runs the TypeScript in Node to observe JavaScript's actual behavior, compiles the same program to Dafny, and asks Dafny two soundness checks:

- **False-proof check (`soundness-refuted`):** When JavaScript returns a value `v`, the harness asks Dafny to prove `result != v`. If Dafny verifies that claim, the translation silently contradicts JavaScript semantics.
- **Dropped-precondition check (`precondition-dropped`):** Some programs call a helper `guard(false, v)` carrying `//@ requires ok` inside comparisons or boolean chains. When JavaScript executes that call, Dafny must reject it; if Dafny verifies with zero errors, the translation dropped an operand JavaScript still evaluates.

Four findings stand out before the detailed tables below:

1. **PR #379 fixed `#350` and `#349` relative to `v0.6.12`,** plus compilation errors on `#340` and `#339`, while introducing a missing `Some(...)` write-back bug on optional array index assignment (`arr[0] = 10`).
2. **Both `v0.6.12` and PR #379 left two critical false-proof bugs open:** mutating an array through a live alias (`const b = a; b.push(v); return a.length`, where Dafny proves the old length), and distinguishing `null` from `undefined` in `number | null | undefined` (midspiral/LemmaScript#304).
3. **PR #388 (`0d96885`) eliminated every `precondition-dropped` (`0`), `dafny-resolve` (`0`), and `timeout` (`0`) failure on the hardened 33-variant `pre`+`opt` corpus,** converted `aliasing/live-alias-mutation` from a silent false proof to an explicit fail-closed compiler rejection (`rejected`), and left only `#304` (`null-vs-undefined-eq`).
4. **Milestone 5 (`Nullish<T>`, `3ddd9d9`) drives `soundness-refuted` to `0` across the entire 40-run fixed-seed shootout** (324 `dafny verify` calls, `0` critical failures, `0` resolve errors, `0` timeouts, `0` IR violations), with all 10 open upstream narrowing/mutation issues (`#268`, `#304`, `#339`, `#340`, `#342`, `#349`, `#350`, `#352`, `#353`, `#354`) now verified fixed.

## Run metadata

- **Tracking:** midspiral/LemmaScript#387, midspiral/LemmaScript#388, midspiral/LemmaScript#304.
- **Revisions evaluated (artifact directories use immutable `<label>-<sha>` names):**
  - `v0.6.12-f991de5` (`f991de5`, pre-rewrite `someMatch` pipeline)
  - `pr379-261609a` (`261609a`, midspiral/LemmaScript#379 checked-reads prototype)
  - `pr388-0d96885` (merged as `0d96885`, measured on compiler head `4fb1af6`)
  - `pr391-57aaf21` (merged as `57aaf21` / released in `v0.6.14` `59e3366`; shootout measured on `3ddd9d9`, review-hardened in `3540adc`)
- **Harness revisions:** The `v0.6.12` and `PR #379` columns ran at `29d0636` (25 variants, single-sample `opt`-stage run). Subsequent hardening in `1201487` expanded the generator to 33 variants (adding empty-string/false/empty-array falsy traps, `!==`/`<=`/`||`/`?.`/call-arg guard positions, real nested-field reassignment, and post-branch reads on `nested-box-push` and `union-switch-mutate`), switched campaigns to stage-locked `fc.check` shrinking, and defaulted evaluation and `--case` replay to both `pre` and `opt` stages. The `PR #388` and `Milestone 5` columns ran on this hardened 33-variant `pre`+`opt` harness, and all 7 saved baseline artifacts under `formal/shootout-artifacts/{v0.6.12-f991de5,pr379-261609a}/` were replayed directly.
- **Toolchain:** Node `v24.17.0`, Dafny `4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2`.
- **Exact CLI command (identical across all four runs):**

```sh
cd tools
npx tsx fuzz/narrowing-fuzz.ts --imperative --seed 1 --runs 40 --verify-timeout 15 --out <out-dir>
```

All 7 families were enabled: `reassign`, `mutation`, `loop-shadow`, `union`, `nullish-falsy`, `aliasing`, `guard-eval`.

## 1. Scorecard Summary

| Metric | `v0.6.12` (`f991de5`, 25 variants / `opt`) | `PR #379` (`261609a`, 25 variants / `opt`) | `PR #388` (`4fb1af6`, 33 variants / `pre`+`opt`) | `Milestone 5` (`3ddd9d9`, 33 variants / `pre`+`opt`) | Notes |
| --- | ---: | ---: | ---: | ---: | --- |
| Programs evaluated (incl. shrink steps) | 40 | 40 | 47 | 45 | `--seed 1 --runs 40` (`fc.check` shrinks only failing classes) |
| `dafny verify` calls | 111 | 127 | 306 | 324 | Specialized refutation + positive/precondition checks (`pre`+`opt` on PR #388 and M5) |
| Wall time | 156.0s | 259.8s | 1795.1s | 1274.4s | Local macOS arm64 |
| **Passed (refutation rejected + positive verified)** | **24** | **27** | **37** | **37** | Every non-unannotated-loop program passes (or fails closed on live-alias mutation) |
| **CRITICAL: `soundness-refuted`** | **6** (3 classes) | **5** (2 classes) | **2** (1 class) | **0** | `#304` fixed via `Nullish<T>`; zero silent false proofs remain |
| **CRITICAL: `precondition-dropped`** | **1** (1 class) | **0** | **0** | **0** | `#349` fixed across `===`, `!==`, and relational comparisons (`pre`+`opt`) |
| `semantic-mismatch` (unproved, not refuted) | 0 | 6 (1 class) | 6 (1 class) | 8 (1 class) | Expected unannotated `#339` `while` loop without loop invariants |
| `dafny-resolve` (invalid Dafny emitted) | 9 (3 classes) | 1 (1 class) | **0** | **0** | `#340`, `#339`, and `array-index-assign` all emit valid, verifying Dafny |
| `rejected` (explicit compiler rejection) | 0 | 0 | **2** (1 class) | **0** | Live-alias mutation still fails closed (seed 1 M5 sample drew no live-alias-mutation shrink; verified via replay & `alias-check.test.ts`) |
| `timeout` (`15s` cap) | 0 | 1 | **0** | **0** | Zero timeouts across all 324 Dafny calls |
| `invalid-ts` / `tool-error` | 0 / 0 | 0 / 0 | **0 / 0** | **0 / 0** | Zero generator, IR-invariant, or harness errors |

## 2. Failure Classes and Upstream Mapping

### `v0.6.12` (`f991de5`): 7 distinct failure classes

| Class | Severity / Oracle | Family / Label | Upstream tracking | Saved artifact |
| --- | --- | --- | --- | --- |
| #3 | **CRITICAL** (`precondition-dropped`) | `guard-eval/eq-rhs-guard-false` | Tracked: midspiral/LemmaScript#349 | [`v0.6.12-f991de5/3.ts`](./shootout-artifacts/v0.6.12-f991de5/3.ts), [`v0.6.12-f991de5/3.semantic.json`](./shootout-artifacts/v0.6.12-f991de5/3.semantic.json) |
| #5 | **CRITICAL** (`soundness-refuted`) | `aliasing/live-alias-mutation` | Related: midspiral/LemmaScript#267 (**new concrete refutation**: `const b = a; b.push(v); return a.length`) | [`v0.6.12-f991de5/5.ts`](./shootout-artifacts/v0.6.12-f991de5/5.ts), [`v0.6.12-f991de5/5.semantic.json`](./shootout-artifacts/v0.6.12-f991de5/5.semantic.json) |
| #6 | **CRITICAL** (`soundness-refuted`) | `mutation/opt-array-push` | Tracked: midspiral/LemmaScript#350 | [`v0.6.12-f991de5/6.ts`](./shootout-artifacts/v0.6.12-f991de5/6.ts), [`v0.6.12-f991de5/6.semantic.json`](./shootout-artifacts/v0.6.12-f991de5/6.semantic.json) |
| #7 | **CRITICAL** (`soundness-refuted`) | `nullish-falsy/null-vs-undefined-eq` | Tracked: midspiral/LemmaScript#304 | [`v0.6.12-f991de5/7.ts`](./shootout-artifacts/v0.6.12-f991de5/7.ts), [`v0.6.12-f991de5/7.semantic.json`](./shootout-artifacts/v0.6.12-f991de5/7.semantic.json) |
| #1 | `dafny-resolve` | `reassign/absent-to-present` | Tracked: midspiral/LemmaScript#340 (`v + 6` sees `Option<int>`) | (fixed in PR #379) |
| #2 | `dafny-resolve` | `loop-shadow/while-presence-countdown` | Tracked: midspiral/LemmaScript#339 (`total + cur` sees `Option<int>`) | (fixed at resolve in PR #379) |
| #4 | `dafny-resolve` | `mutation/array-index-assign` | **Newly surfaced:** `arr := i_arr_val[0 := 10]` (`LHS of assignment must denote a mutable variable`) | (still broken in PR #379) |

### `PR #379` (`261609a`): 5 distinct failure classes

| Class | Severity / Oracle | Family / Label | Upstream tracking | Saved artifact |
| --- | --- | --- | --- | --- |
| #4 | **CRITICAL** (`soundness-refuted`) | `aliasing/live-alias-mutation` | Related: midspiral/LemmaScript#267 (**still proves false postcondition on PR #379**) | [`pr379-261609a/4.ts`](./shootout-artifacts/pr379-261609a/4.ts), [`pr379-261609a/4.semantic.json`](./shootout-artifacts/pr379-261609a/4.semantic.json) |
| #5 | **CRITICAL** (`soundness-refuted`) | `nullish-falsy/null-vs-undefined-eq` | Tracked: midspiral/LemmaScript#304 (**still proves false postcondition on PR #379**) | [`pr379-261609a/5.ts`](./shootout-artifacts/pr379-261609a/5.ts), [`pr379-261609a/5.semantic.json`](./shootout-artifacts/pr379-261609a/5.semantic.json) |
| #3 | `dafny-resolve` | `mutation/array-index-assign` | **New PR #379 bug:** emits `arr := arr.value[0 := 10];` (`RHS of type seq<int> not assignable to LHS of type Option<seq<int>>`, missing `Some(...)` write-back wrapper) | [`pr379-261609a/3.ts`](./shootout-artifacts/pr379-261609a/3.ts), [`pr379-261609a/3.semantic.json`](./shootout-artifacts/pr379-261609a/3.semantic.json) |
| #2 | `semantic-mismatch` | `loop-shadow/while-presence-countdown` | Expected unannotated loop behavior (no false proof; Dafny cannot prove concrete loop sum without loop invariants) | (none) |
| #1 | `timeout` | `reassign/nested-field-reassign` | 15s cap exceeded once on PR #379 | (none) |

### `PR #388` (`0d96885`, Hybrid Milestones 0–4): 3 non-passing classes (0 unexpected regressions)

| Class | Severity / Oracle | Family / Label | Status | Saved artifact |
| --- | --- | --- | --- | --- |
| #2 | **CRITICAL** (`soundness-refuted`) | `nullish-falsy/null-vs-undefined-eq` | Deferred to Milestone 5 (midspiral/LemmaScript#304, `Nullish<T>`) | [`pr388-0d96885/2.ts`](./shootout-artifacts/pr388-0d96885/2.ts), [`pr388-0d96885/2.semantic.json`](./shootout-artifacts/pr388-0d96885/2.semantic.json) |
| #3 | `rejected` (sound fail-closed) | `aliasing/live-alias-mutation` | **Fixed** (was `soundness-refuted` on both `v0.6.12` and PR #379; now explicitly rejected by `alias-check.ts`) | [`pr388-0d96885/3.ts`](./shootout-artifacts/pr388-0d96885/3.ts), [`pr388-0d96885/3.semantic.json`](./shootout-artifacts/pr388-0d96885/3.semantic.json) |
| #1 | `semantic-mismatch` | `loop-shadow/while-presence-countdown` | Expected unannotated loop behavior (no false proof; Dafny cannot prove concrete loop sum without loop invariants) | (none) |

### `Milestone 5` (`3ddd9d9`, `Nullish<T>`): 1 non-passing class (0 critical soundness failures)

| Class | Severity / Oracle | Family / Label | Status | Saved artifact |
| --- | --- | --- | --- | --- |
| #1 | `semantic-mismatch` | `loop-shadow/while-presence-countdown` | Expected unannotated loop behavior (no false proof; Dafny cannot prove concrete loop sum without loop invariants) | (none) |

## 3. Deterministic Replay Verification

Every saved artifact in `formal/shootout-artifacts/` was replayed without reshrinking using:

```sh
cd tools
npx tsx fuzz/narrowing-fuzz.ts --case ../formal/shootout-artifacts/<revision>/<N>.semantic.json --verify-timeout 15
```

- On `v0.6.12` (`f991de5`): `v0.6.12-f991de5/{3,5,6,7}.semantic.json` all reproduced their exact original oracle verdicts (`exit 1`).
- On `PR #379` (`261609a`): `pr379-261609a/{3,4,5}.semantic.json` all reproduced their exact original oracle verdicts (`exit 1`).
- On `PR #388` (`0d96885`, measured on `4fb1af6`):
  - `v0.6.12-f991de5/3.semantic.json` (`#349` `precondition-dropped`): **passed** (`exit 0`, 2 checks verified).
  - `v0.6.12-f991de5/6.semantic.json` (`#350` `opt-array-push` `soundness-refuted`): **passed** (`exit 0`, 4 checks verified).
  - `pr379-261609a/3.semantic.json` (`array-index-assign` `dafny-resolve`): **passed** (`exit 0`, 4 checks verified).
  - `v0.6.12-f991de5/5.semantic.json` and `pr379-261609a/4.semantic.json` (`live-alias-mutation` `soundness-refuted`): **explicitly rejected** (`rejected: Live-alias mutation in target`, sound fail-closed).
  - `v0.6.12-f991de5/7.semantic.json` and `pr379-261609a/5.semantic.json` (`#304` `null-vs-undefined-eq`): still `soundness-refuted` (deferred to Milestone 5).
- On `Milestone 5` (`3ddd9d9` / `3540adc`):
  - `v0.6.12-f991de5/7.semantic.json`, `pr379-261609a/5.semantic.json`, and `pr388-0d96885/2.semantic.json` (`#304` `null-vs-undefined-eq`): **passed** (`exit 0`, 6 checks verified).
  - All previously passing (`#349`, `#350`, `array-index-assign`) and fail-closed (`live-alias-mutation`) replays keep their exact results.

## 4. Summary of Milestones 0–5

All 5 milestones of midspiral/LemmaScript#387 are complete:

1. **Milestones 0–4 (`0d96885`, PR #388):** Standalone Dafny core calculus (`formal/narrowing-model.dfy`), expanded imperative differential fuzzer, self-verified `Place` write-back (`places.ts`), self-verified live-alias mutation rejection (`alias-check.ts`), checked reads (`checked-reads.ts`), and executable-only `#349` precondition preservation.
2. **Milestone 5 (`Nullish<T>`, midspiral/LemmaScript#304):** Selective three-case `Nullish<T>` datatype (`Undefined | Null | Value(value: T)` in Dafny, `LemmaScript/Nullish.lean` in Lean) emitted only for `T | null | undefined`, keeping single-sentinel `T | undefined` and `T | null` on `Option<T>` while distinguishing their absent sentinels. Closes the 10th and final open narrowing/mutation issue (`#268`, `#304`, `#339`, `#340`, `#342`, `#349`, `#350`, `#352`, `#353`, `#354`) with zero critical soundness failures on the shootout corpus.
