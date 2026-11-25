# Diagnostic Report: Proof Timeouts, Churn, and Lean Friction in PR #379

- **Tracking:** robertpenner/LemmaScript#44 (part of robertpenner/LemmaScript#43; Milestone 2 / Open Decision 2 of midspiral/LemmaScript#387).
- **Revisions compared:** `midspiral/main` (`f991de5`) vs. `midspiral/redesign-narrowing` (`261609a`, midspiral/LemmaScript#379) and the three PR #379 case-study staging branches:
  - `midspiral/pi-lemmascript`: `lemmascript` vs. `lemmascript-redesign-narrowing`
  - `midspiral/balanced-match-lemmascript`: `lemmascript` vs. `lemmascript-redesign-narrowing`
  - `CHARM-BDF/charmchat`: `lemma` vs. `lemma-redesign-narrowing`
- **Toolchain:** Dafny `4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2`, Lean `4.34.0` (arm64-apple-darwin24.6.0).

## 1. Reproducible Timing Table

All Dafny timings were measured on local macOS arm64 with explicit `--verification-time-limit` caps.

| Case study & target | Variant | Command flags | Wall time | Result |
| --- | --- | --- | --- | --- |
| `pi-lemmascript` (`truncate.dfy`) | Base (`lemmascript`) | `--verification-time-limit:30` | 6.27s (cold) | 5 verified, 0 errors |
| `pi-lemmascript` (`truncate.dfy`) | PR #379 (`lemmascript-redesign-narrowing`) | `--verification-time-limit:30` | 2.06s | 5 verified, 0 errors (+2 `i_compareN` churn lines) |
| `pi-lemmascript` (`truncate.dfy`) | Clean (`res.truncatedBy == Some("bytes")`) | `--verification-time-limit:30` | 1.29s | 5 verified, 0 errors (0 temporaries, 0 `match`) |
| `balanced-match` (`src/index.dfy`, `range`) | Base (`lemmascript`) | `--isolate-assertions --filter-position=...:1078 --verification-time-limit:20` | 53.67s | 301 verified, 0 errors, 2 timeouts (`line 1168`, `line 1187`) |
| `balanced-match` (`src/index.dfy`, `range`) | PR #379 (`lemmascript-redesign-narrowing`) | `--isolate-assertions --filter-position=...:1078 --verification-time-limit:20` | 54.38s | 302 verified, 0 errors, **3 timeouts** (`line 1168`, `line 1187`, **new regression `line 1189`**) |
| `balanced-match` (`src/index.dfy`, `range`) | Hypothesis (single `if (beg.Some? && beg.value < left)`) | `--isolate-assertions --filter-position=...:1078 --verification-time-limit:20` | **32.59s** | **304 verified, 0 errors, 2 timeouts** (`line 1189` regression eliminated; -40% wall time vs. PR #379) |
| `charmchat` (`workflow.dfy`, `topologicalSort`) | Base (`lemma`) | `--isolate-assertions --filter-symbol=topologicalSort --verification-time-limit:15` | 51.78s | 514 verified, 0 errors, 6 timeouts (pre-existing near-limit proof; `CASE_STUDIES.md` documents 600s limit) |
| `charmchat` (`workflow.dfy`, `topologicalSort`) | PR #379 (`lemma-redesign-narrowing`) | `--isolate-assertions --filter-symbol=topologicalSort --verification-time-limit:15` | 58.54s | 513 verified, 0 errors, 7 timeouts (adds `line 561`, `line 715`; drops `line 629`) |
| `charmchat` (`workflow.dfy`, `topologicalSort`) | Negative test A (`workflow-hypothesis`: drop `i_logic1/2`, keep `Option<T>` & `i_neighbor_seq` + added `assert id in nodeMap`) | `--isolate-assertions --filter-symbol=topologicalSort --verification-time-limit:15` | 69.96s | 508 verified, 0 errors, 11 timeouts |
| `charmchat` (`workflow.dfy`, `topologicalSort`) | Negative test B (`workflow-no-option`: drop `Option<T>` & `i_logic1/2`, keep hoisted `i_neighbor_seq` & `i_key0`) | `--isolate-assertions --filter-symbol=topologicalSort --verification-time-limit:15` | 78.02s | 504 verified, 0 errors, 13 timeouts |
| Lean 4 probe (`formal/lean-checked-reads-probe.lean`) | Clean pure dependent `Option.get` + `#guard_msgs` | `lean formal/lean-checked-reads-probe.lean` | 0.73s | Verified (0 errors; unguarded read rejected by Lean) |

Note on `balanced-match` without `--isolate-assertions`: both `balanced-base.dfy` and `balanced-pr379.dfy` exceed 45s on `range` and `range_spec_loop_inner` (`48.68s` and `52.04s` at `--verification-time-limit:45`), confirming `balanced-match` is already an expensive proof on `main` that is sensitive to extra control-flow splits.

## 2. Root-Cause Diff Excerpts and Findings

### A. `pi-lemmascript`: unconditional comparison-temporary lifting

PR #379 wraps pure optional comparisons inside `var i_compareN` (Dafny) and `let _compareN` (Lean) even inside `ensures` contracts where both operands are pure:

```dafny
// Base (lemmascript):
ensures ((match res.truncatedBy { case Some(i_value) => (i_value == "bytes") case None => false }) ==> ...)

// PR #379 (lemmascript-redesign-narrowing):
ensures ((var i_compare0: Option<string> := res.truncatedBy;
  (match i_compare0 { case Some(i_value) => (i_value == "bytes") case None => false })) ==> ...)

// Clean Milestone 4 lowering (1.29s, 5 verified):
ensures ((res.truncatedBy == Some("bytes")) ==> ...)
```

For `pi-lemmascript`, this unnecessary temp lifting accounts for 100% of the diff on both Dafny and Lean.

### B. `balanced-match`: sequential `if i_branch0` splits + lifted `i_compare0`/`i_compare1`

In `src/index.dfy` (Branch 3 of the `range` loop, right after `poppedCount` is incremented), PR #379 replaced one `match` with two sequential `if i_branch0` statements and two comparison temporaries:

```dafny
// Base (lemmascript):
match beg {
  case Some(i_beg_val) =>
    if (i_beg_val < left) {
      left := i_beg_val;
      right := Some(bi);
    }
  case None =>
}

// PR #379 (lemmascript-redesign-narrowing):
var i_branch0 := (beg).Some?;
if i_branch0 {
  var i_compare0 := beg;
  var i_compare1 := left;
  i_branch0 := (match i_compare0 { case Some(i_value) => (i_value < i_compare1) case None => false });
}
if i_branch0 {
  left := beg.value;
  right := Some(bi);
}
```

The sequential `if i_branch0` pair multiplies Boogie control-flow paths inside a loop carrying a recursive `range_spec_loop` refinement invariant, pushing `invariant |begs| > 0 ==> poppedCount == CountAll(...)` (`line 1189`) past the 20s per-VC budget. Replacing that single block with one short-circuiting guard:

```dafny
if (beg.Some? && beg.value < left) {
  left := beg.value;
  right := Some(bi);
}
```

verified `line 1189` immediately (restoring the baseline 2 timeouts at 20s) and cut total `range` wall time from `54.38s` to `32.59s` (-40%).

### C. `charmchat` (`workflow.dfy`): pre-existing near-limit SMT proof perturbed by hoisted loop temporaries and `Option<T>` round-tripping

PR #379 made three changes to `workflow.dfy`:
1. Introduced `datatype Option<T> = None | Some(value: T)` into a file that previously did not declare `Option`.
2. Replaced direct map reads with `Option` wrap/match/unwrap round-trips (`(if id in nodeMap then Some(nodeMap[id]) else None).value`, `var i_logic1 := ...; var i_neighbor_seq := (if !((match i_logic1 { ... })) then i_logic1.value else []);`, and `var i_logic2 := ...`).
3. Hoisted `var i_neighbor_seq` outside the inner neighbor loop (whose handwritten invariants still refer to `adjacency[id]` directly rather than `i_neighbor_seq`) and added `var i_key0 := dep;` in the earlier loop.

**Negative finding from A/B tests A and B:** Removing `Option<T>` and `i_logic1`/`i_logic2` while leaving `var i_neighbor_seq` hoisted and `var i_key0` present did **not** recover `topologicalSort` (timeouts increased from 7 to 11 and 13 at 15s cap, concentrated on the inner loop invariants `lines 715–723`). This shows that `workflow.dfy` is already close to Z3's resource envelope on `lemma` (6 timeouts at 15s cap; 600s required even on base) and is sensitive to extra hoisted loop variables (`i_neighbor_seq`) that break direct syntactic alignment with handwritten `adjacency[id]` loop invariants.

### D. Lean 4 pure-mirror friction

Inspecting `examples/spec.def.lean`, `examples/spec.proof.lean`, `examples/toposort.def.lean`, and `examples/toposort.proof.lean` on `midspiral/redesign-narrowing` (`261609a`) shows two contrasting effects:

1. **Regression on pure functions (`examples/spec.def.lean`):** PR #379 lowered every checked read in a method body to a monadic Velvet call `let _tN ← LemmaScript.optionValue x`. Because `optionValue` is monadic, six previously pure functions (`deepAccess`, `negVar`, `negField`, `truthyVar`, `nestedAndTernary`, `ternarySpecOpt`) lost their `Pure.<fn>` companions, forcing `examples/spec.proof.lean` to switch from `Pure.<fn>` unfolding to method-level verification, and generating nested dependent `if _present0 : Option.isSome o then ... ((o).get (by grind))` expressions in `ensures` alongside `let _compareN` temporaries.
2. **Win on mutating Velvet methods (`examples/toposort.def.lean` / `toposort.proof.lean`):** For imperative methods with loops and map lookups, `LemmaScript.optionValue` plus `LemmaScript.hashmap_get?_eq_some` simplified `examples/toposort.proof.lean`, removing the custom `topo_solve` tactic macro and lowering `maxHeartbeats` from `16000000` to `2000000`.

The standalone verified probe [`formal/lean-checked-reads-probe.lean`](./lean-checked-reads-probe.lean) (`lean` 4.34.0, 0.73s) demonstrates that pure TypeScript functions whose own guards establish presence can emit a total pure `def` using dependent `if h : x.isSome then ... (x.get h) ... else ...`:
- Preserves a genuine Lean compile-time presence proof obligation (verified via `#guard_msgs` rejecting `bad_unguarded_read`);
- Keeps `Pure.<fn>` companions total and pure (`Tree -> Int` rather than `Option Int`) so Velvet methods can still `return Pure.<fn> ...`;
- Lowers pure comparisons (`res === "bytes"`) directly to `res == some "bytes"` without `let _compareN` churn.

## 3. Concrete Lowering Recommendations for Milestone 4

1. **Direct pure optional comparisons (both backends):** When `a: Option<T>` is compared with pure `b: T` via `===`/`!==`, emit `a == Some(b)` (Dafny) / `a == some b` (Lean) directly. Lift `i_compareN` temporaries only when an operand is impure/monadic or requires single evaluation (such as `?.`, `??`, or calls that may have preconditions/effects).
2. **Avoid sequential `i_branch0` splits for pure `&&` guards:** Lower `if (x !== undefined && P(x))` with pure `x` and pure `P` to a single short-circuiting `if (x.Some? && P(x.value))` instead of two sequential `if i_branch0` statements. This eliminates the `balanced-match` `line 1189` regression and cuts `range` verification time by 40%.
3. **Avoid `Option<T>` round-trips and unnecessary hoisted loop iterables on pure map lookups:** For pure `m.get(k)!` and `m.get(k) || fallback` (including `for..of` over a pure map lookup with a fallback), emit direct map-membership checks (`if k in m then m[k] else fallback`) rather than wrapping into `Some`/`None`, negating a `match`, and unwrapping `.value`. Only hoist a `for..of` iterable temporary when the iterable expression is impure or mutated inside the loop.
4. **Split Lean checked reads between pure functions and mutating Velvet methods:**
   - Pure TS functions (no mutation/reassignment, self-guarded reads): emit pure `Pure.<fn>` using dependent `if h : x.isSome then ... (x.get h) ...` (preserving pure companions and proof scripts).
   - Imperative/mutating Velvet methods (such as `toposort`): retain `LemmaScript.optionValue` + `hashmap_get?_eq_some` (preserving the 8x heartbeat reduction on `toposort.proof.lean`).
