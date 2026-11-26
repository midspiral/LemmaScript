# LemmaScript — Lean Backend Specification

This document covers the Lean backend using Velvet 2 from the `lemma2` branch of `namin/velvet`. See [README.md](README.md#setup) for setup, and [SPEC.md](SPEC.md) for the shared annotation language, translation rules, type mapping, and pipeline.

---

## 1. Project Structure

LemmaScript is a Lean library. Each user project depends on it.

```
my-app/
  src/
    binarySearch.ts              ← TypeScript source
    binarySearch.types.lean      ← Lean types from TS (generated)
    binarySearch.spec.lean       ← ghost definitions, lemmas (user-written)
    binarySearch.def.lean        ← method definition (generated)
    binarySearch.proof.lean      ← prove_correct + tactics (user/LLM-written)
  lakefile.lean                  ← requires LemmaScript
  lean-toolchain
  package.json                   ← depends on lemmascript
```

### 1.1 The Four Lean Files

For each verified TS function `foo.ts`, there are up to four Lean files:

| File | Who writes it | Purpose |
|------|--------------|---------|
| `foo.types.lean` | `lsc gen` | Lean type definitions derived from TS types |
| `foo.spec.lean` | User | Ghost definitions, helper lemmas |
| `foo.def.lean` | `lsc gen` | Velvet method definition (generated from TS) |
| `foo.proof.lean` | User / LLM | `prove_correct` with proof tactics |

**Key property:** `foo.types.lean` and `foo.def.lean` are always regeneratable from `foo.ts`. The user only writes `.spec.lean` and `.proof.lean`.

### 1.2 Import Chain

```
foo.types.lean         ← generated: Lean inductives/structures from TS types
foo.spec.lean          ← imports foo.types.lean, user-written ghost definitions
foo.def.lean           ← imports foo.spec.lean, generated method definition
foo.proof.lean         ← imports foo.def.lean, user-written proof
```

Each file imports the previous. Lean checks the full chain.

`foo.def.lean` imports `foo.spec.lean`, which imports `foo.types.lean` (if it exists). If there is no `.spec.lean`, `foo.def.lean` imports `foo.types.lean` directly (or `LemmaScript` if there are no types either).

### 1.3 File Naming and Lake Modules

Files use dotted names: `binarySearch.spec.lean`. In Lean imports, dots in filenames are escaped:

```lean
import «binarySearch.spec»
import «binarySearch.def»
```

All files live in `src/`, which Lake is configured to scan. No nested `lean/` directory.

To set up a new project, adapt `lakefile.lean` from a Velvet 2 case study to your source directories and module roots, and use the same `lean-toolchain` as LemmaScript (currently Lean 4.34.0). Keep LemmaScript and Velvet as sibling checkouts, with Velvet on **`lemma2`**. The older `lemma` branch is incompatible with this setup. The current Lake configuration does not use the legacy solver-version file `dependencies.toml`.

### 1.4 Overriding the Module Base — `//@ lean-module`

By default the Lean module base is the file's basename, so `foo.ts` emits `foo.types.lean` / `foo.def.lean` and a `lakefile.lean` root of `«foo.types»`. Lean module names are **flat and global**: two `.ts` files with the same basename in different directories (e.g. an in-place fork that annotates two copies of `compaction.ts`) would emit colliding modules and cannot both be Lean libraries. Dafny is unaffected — each `.dfy` is verified as a standalone unit.

A file-level directive overrides the base for the **Lean backend only**:

```ts
//@ lean-module compaction-cli
```

`lsc gen --backend=lean` then emits `compaction-cli.types.lean` / `compaction-cli.def.lean` (with `import «compaction-cli.types»`), and looks for `compaction-cli.spec.lean` / `compaction-cli.proof.lean`. Wire it into `lakefile.lean` with matching roots (`` `«compaction-cli.types» ``, `` `«compaction-cli.def» ``, `` `«compaction-cli.proof» ``). The Dafny artifacts (`foo.dfy`, `foo.dfy.gen`) keep the file basename.

---

## 2. Monadic Lifting

The shared method-call lifting (SPEC.md §3.6) has specific Lean semantics. Lifted method calls use Lean's monadic `←` bind in do-notation:

```lean
x ← f a b          -- mutation: rebinds existing variable
let x ← f a b      -- new binding
```

This follows Lean's do-notation desugaring rules (Ullrich & de Moura, "'do' Unchained", 2022). The `←` carries monadic semantics that Velvet's VC generator reasons about through Lean's `Std.Internal.Do` framework.

**Monadic HOF variants:** When a lambda callback passed to a HOF calls a method, the transform selects the monadic variant of the HOF (e.g., `arr.mapM f` instead of `arr.map f`). The monadic HOF call is itself monadic — it gets `←` at the call site. The transform checks the transformed lambda body for `←` binds and selects the variant automatically.

**Short-circuit note:** As in Lean's `←`, lifting from `&&`/`||` loses short-circuit semantics (both sides execute). This matches Lean's behavior.

**Proof note:** [LemmaScript/ArrayM.lean](LemmaScript/ArrayM.lean) provides `@[spec]` rules for `mapM`, `filterM`, `allM`, and `anyM` with `Option` callbacks. These establish successful execution when each callback succeeds; the `mapM` rule also preserves array size. Stronger properties about the resulting elements may require additional lemmas.

---

## 3. Generated Lean files

For `src/foo.ts`, `lsc gen` produces `src/foo.types.lean` and `src/foo.def.lean`.

`foo.types.lean` contains Lean type definitions derived from TS `type` declarations (string literal unions, discriminated unions, records), along with any pure mirrors or opaque extern declarations (§3.1). It is omitted when none of these declarations are needed.

`foo.def.lean` contains the Velvet `method` definition:

```lean
/-
  Generated by lsc from foo.ts
  Do not edit — re-run `lsc gen` to regenerate.
-/
import «foo.spec»

set_option velvet.semantics.termination "total"

method foo (params...) returns (res : RetType)
  requires ...
  ensures ...
  do
    ...
```

The generated file contains **only the method definition**, no `prove_correct`. The proof lives in `foo.proof.lean`.

### 3.1 Pure Function Mirrors

For functions that are **pure** (see SPEC.md §5), `lsc` also generates a plain Lean `def` in `foo.types.lean`, inside a `namespace Pure`:

```lean
namespace Pure

def foo (params...) : RetType :=
  -- same logic as the Velvet method, as a plain function

end Pure
```

This enables proofs by standard Lean induction over sequences of calls. The Velvet method is also generated, but as a thin wrapper: `return Pure.foo params`. This avoids termination issues (the pure `def` handles termination natively) while keeping the method callable from other Velvet methods via `←`.

Functions containing checked min/max spreads, and their callers, remain methods without a pure mirror so their nonempty-input obligations are preserved. Use their method contracts for composition.

**Spec references:** In `//@ ensures`, `//@ requires`, and `//@ invariant` annotations, calls to pure functions are resolved as `Pure.fnName`. The resolve phase classifies these as `spec-pure` call kind, and the transform emits the qualified name. Calls to external Lean-defined spec helpers (e.g., `sumTo` in a hand-written `.spec.lean`) pass through unqualified.

Deterministic extern declarations become opaque Lean functions. Impure externs are Dafny-only and are rejected by the Lean backend, whether selected explicitly with `//@ impure` or inherited from `extern-default: impure`; add `//@ pure` to an individual extern used by a Lean file.

**Proof note:** Since the method body is `return Pure.foo ...`, supply its pure mirror to the discharger: `velvet_vcgen [foo] with finish [Pure.foo]`.

---

## 4. User-Written `.proof.lean` File

```lean
import «clamp.def»

set_option velvet.semantics.termination "total"

prove_correct clamp by
  velvet_vcgen [clamp] with finish
```

Velvet 2 generates VCs and discharges them in one shared solver state. When some goals need interactive proofs:

1. `lsc check --backend=lean path/to/foo.ts` reports unsolved goals.
2. The user (or LLM) edits `.proof.lean` to add fallback tactics:

```lean
prove_correct binarySearch by
  velvet_vcgen [binarySearch] with (expose_names; try finish)
  · -- handle remaining goal
    grind
```

3. Or the user adds helper lemmas to `.spec.lean` and supplies them to `finish` or to `simplifying_assumptions [helper_zero, helper_step]` before `with` to simplify hypotheses during VC generation.

Keep common processing inside `velvet_vcgen`, including `expose_names`, instead of following it with `all_goals` passes. The `with` clause takes grind-mode tactics; `tactic => ...` embeds a complete ordinary tactic proof when needed. Goal-specific residual proofs can remain afterward.

**Invariants** are part of the method definition (in the `//@ ` annotations), not the proof. If an invariant is missing, the user adds `//@ invariant` to the TS file and regenerates `.def.lean`.

### 4.1 Standalone Lemmas

Properties about functions can be proved as standalone Hoare triples in `.proof.lean`, separately from the function's `requires`/`ensures`. This is useful when:
- The function has no natural precondition but interesting properties hold under specific conditions
- Multiple properties should be proved about the same function
- The property involves multiple functions

```lean
-- The function has no ensures — just loop invariants
prove_correct runSession by
  velvet_vcgen [runSession] with finish

-- Property proved separately as a Hoare triple
open Std.Internal.Do in
theorem runSession_timeout_resets (events : Array Event)
    (h1 : events.size > 0) (h2 : lastEvent events = .timeout) :
    Triple (runSession events)
           (events.size > 0 ∧ lastEvent events = .timeout)
           (fun res => res = State.idle) False := by
  velvet_vcgen [runSession] with finish
```

Supply the method in the `velvet_vcgen` argument list and discharge its VCs with `with finish`.

---

## 5. LemmaScript Lean Library

The LemmaScript Lean library provides:

1. **Velvet 2 and supporting Mathlib imports.** User artifacts import `LemmaScript` to access the method syntax, VC generator, and proof support.
2. **Cross-file method specifications.** The Velvet fork persists method specifications so `prove_correct` works in a separate file from `method`.
3. **Operation specifications and helper lemmas** in [ArrayM.lean](LemmaScript/ArrayM.lean), [HashSet.lean](LemmaScript/HashSet.lean), [Range.lean](LemmaScript/Range.lean), and [MinMax.lean](LemmaScript/MinMax.lean): monadic array specifications, hash-set size and array membership lemmas, a range-to-list bridge, and checked array extrema.
4. **On-demand support modules** imported only when used: [JSString.lean](LemmaScript/JSString.lean) (scalar string indexing, `indexOf`, `slice`) and [Nullish.lean](LemmaScript/Nullish.lean) (three-case `Nullish α` datatype with `Inhabited`, `isNull`/`isUndefined`/`isValue`, `get`, and `@[grind =]` lemmas for `T | null | undefined`; see [`examples/nullish.ts`](examples/nullish.ts)).

The library depends on:
- Velvet 2 from the sibling `../velvet` checkout on `lemma2`.
- Mathlib, pinned in [lakefile.lean](lakefile.lean) to match [lean-toolchain](lean-toolchain).

Lake builds the Lean dependencies. VC generation uses Lean's `Std.Internal.Do` and grind infrastructure; Loom and external Z3/cvc5 binaries are not dependencies of this backend.

**Future: LemmaScript-native macros.** A future interface could build directly on Lean's `Std.Internal.Do` framework to support TS-specific constructs and diagnostics. The current backend generates Velvet 2 methods and uses `velvet_vcgen`.

---

## 6. Lean Verification Notes

Practical constraints for the current Velvet 2 backend.

### 6.1 Int vs Nat

- All TS `number` variables default to `Int` in Lean.
- Variables annotated `//@ type v nat` become `Nat`.
- Mixing Int and Nat in comparisons is fine — Lean coerces `Nat` to `Int`.
- Quantifier types must be consistent within a property: don't use `k : Int` in an invariant and `k : Nat` in the ensures for the same property.
- `arr.size` is `Nat`. No explicit `↑` coercion needed.
- Array indexing: `arr[i]!` for `Nat`, `arr[i.toNat]!` for `Int`.
- String indexing: `JSString.index s i` returns a one-scalar `String`. Like array reads, its Lean definition uses defaulted indexing; source-domain bounds (`0 ≤ i < s.length`) must be established by callers.
- Recursive ghost functions on array indices should take `Nat`. Calling code should use `//@ type` for the index variable.
- Bridge lemmas (e.g., `(i + 1).toNat = i.toNat + 1`) may be needed in `.spec.lean` when mixing Int and Nat.

`Math.min` / `Math.max` support one or more int/nat operands: unary calls are identity, and larger calls fold through native `Min.min` / `Max.max`. Mixed operands are promoted to `Int`. Spreads concatenate their segments as `Array Int` (mapping natural-number arrays with `Int.ofNat`) and use checked operations from [MinMax.lean](LemmaScript/MinMax.lean). Total correctness requires only the combined input to be nonempty; the result bounds every element and equals an element. Zero-argument calls and bigint operands are rejected; real arithmetic remains unsupported. [mathMinMaxInt.ts](examples/mathMinMaxInt.ts) verifies the shared behavior with both backends.

### 6.2 VC Generation and Discharging

- Start with `velvet_vcgen [methodName] with finish`; add pure mirrors or helper lemmas to `finish [...]` as needed.
- Supply recursive helpers' zero/step rewrite lemmas through `simplifying_assumptions [...]` when assumptions need simplification.
- Keep common name exposure and solving inside `with` to reuse the VC generator's shared solver state.
- Use `tactic => ...` for a complete ordinary tactic proof, or `try finish` to leave goal-specific residual proofs afterward.
- The solver cannot invent loop invariants. Missing or weak invariants produce unsolved goals.
- Mixed `Int`/`Nat` arithmetic may need explicit bounds, bridge lemmas, or `omega`.

### 6.3 Velvet Specifics

- Velvet 2 uses `method ... returns (...)`, `requires`, and `ensures`; loops support `invariant`, `done_with`, `decreasing`, `break`, and mutable variables.
- LemmaScript lowers supported returns inside outer loops to `break` plus a result variable. Loops with `break`, including lowered returns, require an explicit `//@ done_with` annotation; see [SPEC.md §4.3](SPEC.md#43-return-inside-loops).
- `done_with` captures what is true when the loop exits (by condition or by break).
- `prove_correct` works across files (with our fork's persistence fix).
- `velvet_vcgen [methodName] with (expose_names; try finish)` exposes names and leaves unsolved goals for interactive proof.
- For narrowed `Option`/`Nullish` reads lowered via `checkedUnwrap` (`(x).get (by grind)`), `lean-emit.ts` emits non-shadowing dependent guards (`if _hN : ...` in expressions and early-exit statements, and `∀ (_hN : ...), ...` in spec implications) so `grind` receives each guard hypothesis in local proof context.

### 6.4 Decreasing Clauses

- Lean accepts any well-founded relation: `Nat`, tuples (lexicographic), etc.
- `Nat` expressions work directly (e.g., `arr.size - i` where `i : Nat`).
- `Int` expressions need `.toNat` (e.g., `(hi - lo + 1).toNat`).
- Avoid mixing Nat and Int in subtraction: `(arr.size - i).toNat` where `i : Int` causes issues. Either make `i : Nat` or use `arr.size - i.toNat`.
