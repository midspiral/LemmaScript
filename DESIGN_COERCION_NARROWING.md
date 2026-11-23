# DESIGN_COERCION_NARROWING — Direct Control Flow with Checked Local Coercions

Supersedes the `someMatch` / `tagMatch` rewriting architecture documented in
[ARCHITECTURE_NARROWING.md](ARCHITECTURE_NARROWING.md).

TypeScript narrows types by control flow while preserving evaluation order,
mutable storage, and lexical scope. Previously, LemmaScript translated
narrowing by rewriting control flow into `someMatch` / `tagMatch` expressions
and statements and substituting occurrences of narrowed paths with fresh
pattern binders. That rewrite-and-substitute architecture broke down across a
cluster of soundness and usability issues (evaluation-order hazards in `#349`,
stale binders after mutation in `#342` and `#350`, shadowing capture in `#351`,
and conflating `null` with `undefined` in `#304`).

Coercion narrowing replaces control-flow rewriting with a single principle:
**keep the source control flow intact, and insert checked local coercions at
the point where a narrowed value is actually read or projected.**

---

## 1. Why `someMatch` / `tagMatch` Broke Down

Under the old architecture, narrowing had to solve four problems at once:

1. **Pattern-match every narrowing shape.** Every TypeScript guard (`if`,
   `else if`, ternary, `&&`, `||`, early return, `while`, truthiness,
   `Array.isArray`, `typeof`, `"field" in x`, `switch`) needed a dedicated
   structural rewrite rule in `narrow.ts` that converted conditionals into
   `someMatch` / `tagMatch`.
2. **Preserve short-circuit evaluation order (`#349`).** Turning
   `x !== undefined && f(y)` or `x !== at(xs, i)` into a `match` on `x`
   evaluated or hoisted `x` around guards and RHS expressions, causing
   precondition checks on later operands to be skipped or reordered.
3. **Track mutation and aliasing (`#342`, `#350`).** Once `match obj.x { Some(v) => ... }`
   introduced a binder `v` and substituted `obj.x` with `v`:
   - Reassigning `obj` (or `obj.x`) left `v` holding a stale value.
   - Mutating a narrowed optional array (`if (obj.xs) obj.xs.push(1)`) mutated
     or read the binder instead of updating `obj.xs` in place.
4. **Avoid name capture (`#351`).** Whole-subtree substitution of a path or
   field access with a match binder risked capturing shadowed inner bindings
   (now also hardened by [DESIGN_LEXICAL.md](DESIGN_LEXICAL.md)).
5. **Distinguish `null` from `undefined` (`#304`).** Collapsing `T | null | undefined`
   into a single `Option<T>` made `x === null` and `x === undefined`
   indistinguishable, allowing false proofs when a function treated `null` and
   `undefined` differently.

The common root cause was **trying to prove narrowing statically via syntax
rewriting** instead of letting the target verifier (Dafny's SMT solver and
Lean's `grind` / Velvet VCGen) verify the narrowing fact from the unchanged
control flow.

---

## 2. Core Idea: Direct Control Flow + Checked Local Coercions

Instead of rewriting `if (x !== undefined) { return x + 1; }` into
`match x { Some(v) => return v + 1; None => ... }`, LemmaScript emits the
original control flow and checks the unwrap locally at the use site:

| Source TypeScript | Dafny | Lean (pure / spec) | Lean (Velvet method) |
|---|---|---|---|
| `if (x !== undefined) return x + 1` | `if x.Some? { return x.value + 1; }` | `if _h0 : x.isSome then (x.get (by grind)) + 1` | `if x.isSome then let _v0 ← LemmaScript.optionValue x; return _v0 + 1` |
| `if (x !== undefined && x !== null) return x` (`number \| null \| undefined`) | `if !x.Undefined? && !x.Null? { return x.value; }` | `if _h0 : !x.isUndefined && !x.isNull then x.get (by grind)` | `... let _v0 ← LemmaScript.nullishValue x; return _v0` |
| `if (sh.kind === "circle") return sh.r` | `if sh.circle? { return sh.r; }` | `if _h0 : Shape.is_circle sh then (Shape.proj_circle_r sh).get (by grind)` | `if Shape.is_circle sh then let _v0 ← LemmaScript.optionValue (Shape.proj_circle_r sh); return _v0` |
| `if (Array.isArray(v)) { v.push(42); }` | `if v.ArrayBranch? { v := ArrayBranch(v.arr + [42]); }` | *(methods only)* | `if T.is_ArrayBranch v then let _v0 ← LemmaScript.optionValue (T.proj_ArrayBranch_arr v); v := T.ArrayBranch (Array.push _v0 42)` |

### Soundness by Construction

Because control flow is unchanged and every unwrap is **checked by the
verifier** at the exact point of use:

- **Evaluation order is preserved (`#349`).** Short-circuiting `&&`, `||`,
  `?:`, `if`, early returns, and comparisons with optional operands keep
  their exact left-to-right semantics. No expression is hoisted into a
  `match` scrutinee.
- **No stale binders after mutation (`#342`, `#350`).** Reads always project
  the live variable or field (`obj.x.value`, not a captured binder). If a
  program mutates `obj` or `obj.x` before a subsequent read, the verifier
  checks `obj.x.Some?` against the *new* state and rejects unsound reads.
  In-place updates like `obj.xs.push(v)` or `cur.push(42)` walk through the
  coercion wrapper and write back `Some(old + [v])` / `ArrayBranch(old + [42])`.
- **No binder substitution (`#351`).** There are no `someMatch` / `tagMatch`
  binders and no `replacePathInTExpr` / `replaceFieldAccess` passes.
- **TypeScript hints are untrusted.** Extraction passes TypeScript's narrowed
  nullishness and variant as *hints* so `resolve.ts` knows where to insert a
  coercion. If a hint were ever overly optimistic, Dafny or Lean refuses to
  verify the coercion precondition (`x.Some?`, `x.isValue`, `Shape.is_circle sh`).
  Soundness never depends on TypeScript's control-flow analyzer being bug-free.

---

## 3. Nullish Representation: `Option<T>` vs `Nullish<T>`

To model `T`, `T | undefined`, `T | null`, and `T | null | undefined` without
penalizing ordinary optionals, [nullish.ts](tools/src/nullish.ts) represents
nullishness as a 2-bit mask on `Ty`:

```ts
export const NONE      = 0; // T
export const UNDEFINED = 1; // T | undefined
export const NULL      = 2; // T | null
export const BOTH      = 3; // T | null | undefined
```

| Bitmask | Meaning | Dafny representation | Lean representation |
|---|---|---|---|
| `NONE (0)` | `T` | `T` | `T` |
| `UNDEFINED (1)` | `T \| undefined` | `Option<T>` (`None` = `undefined`) | `Option T` (`none` = `undefined`) |
| `NULL (2)` | `T \| null` | `Option<T>` (`None` = `null`) | `Option T` (`none` = `null`) |
| `BOTH (3)` | `T \| null \| undefined` | `Nullish<T>` (`Undefined \| Null \| Value(value: T)`) | `LemmaScript.Nullish T` (`Undefined \| Null \| Value (value : T)`) |

### Coercion Matrix

A single typed-IR coercion node `{ kind: "coerce", expr, fromNullish, toNullish, variant?, ty }`
handles every narrowing and widening transition between the four bitmasks:

- **Widening (always safe, no proof obligation):**
  - `NONE → UNDEFINED | NULL`: `Some(e)` / `some e`
  - `NONE → BOTH`: `Value(e)` / `Nullish.Value e`
  - `UNDEFINED → BOTH`: `if e.Some? then Value(e.value) else Undefined` / `Nullish.ofOptionUndefined e`
  - `NULL → BOTH`: `if e.Some? then Value(e.value) else Null` / `Nullish.ofOptionNull e`
- **Narrowing (checked by the verifier at the use site):**
  - `UNDEFINED | NULL → NONE`: Dafny `e.value` (checks `e.Some?`); Lean pure `e.get (by grind)`, Velvet `← LemmaScript.optionValue e`
  - `BOTH → NONE`: Dafny `e.value` (checks `e.Value?`); Lean pure `e.get (by grind)`, Velvet `← LemmaScript.nullishValue e`
  - `BOTH → NULL` (excluding `undefined`): Dafny `if e.Value? then Some(e.value) else None` (guarded by `!e.Undefined?`); Lean pure `e.excludeUndefined (by grind)`, Velvet `← LemmaScript.nullishExcludeUndefined e`
  - `BOTH → UNDEFINED` (excluding `null`): Dafny `if e.Value? then Some(e.value) else None` (guarded by `!e.Null?`); Lean pure `e.excludeNull (by grind)`, Velvet `← LemmaScript.nullishExcludeNull e`

Single-nullish types (`T | undefined` or `T | null`) remain plain `Option<T>` /
`Option T` with zero extra constructors or overhead. `Nullish<T>` is emitted
in Dafny (and `LemmaScript.Nullish` imported in Lean) only when a module
actually uses a `BOTH` type.

Both Dafny and Lean support all equality/inequality checks cleanly:
- `x === undefined` / `x !== undefined` → `nullishTest("isUndefined")` (`!x.Some?` on `UNDEFINED`, `x.Undefined?` on `BOTH`, constant `false` on `NULL`/`NONE`).
- `x === null` / `x !== null` → `nullishTest("isNull")` (`!x.Some?` on `NULL`, `x.Null?` on `BOTH`, constant `false` on `UNDEFINED`/`NONE`).
- `x == null` / `x != null` (loose equality) → `nullishTest("isNullish")` / `nullishTest("isValue")` (`!x.Some?` / `x.Some?` on `Option`, `!x.Value?` / `x.Value?` on `BOTH`).

---

## 4. Discriminated Unions and `Array.isArray` / `typeof` Unions

Phase 2 extends the exact same coercion principle to discriminated unions and
synthesized array-unions (`T[] | NonArray`, e.g., `string | number[]`):

### Tag Tests (`tagTest`)
All variant-testing expressions lower directly to `{ kind: "tagTest", expr, typeName, ctor }`:
- `x.disc === "v"` and `"v" === x.disc` (and `!==` via negation)
- Boolean discriminants: `if (x.ok)` / `if (!x.ok)`
- Property existence: `"field" in x` (resolves to the unique variant containing `field`)
- Synthesized array-unions: `Array.isArray(x)` → `ArrayBranch`, `typeof x === "string"` → `NonArrayBranch`
- `switch (x.disc) { case "v": ... }`: lowered to an `if / else if / else` chain of `tagTest`s (for both statements and pure expressions)

### Checked Variant Projections (`unionProj`)
Reads of variant-specific fields or synth array-union payloads lower to
`{ kind: "unionProj", expr, typeName, ctor, field, raw? }`:
- **Dafny**: `x.Ctor?` for `tagTest`; `x.field` for `unionProj` (Dafny
  natively checks `x.Ctor?` as the destructor precondition, respecting
  `_ctorFieldRenames` for shared/reserved names).
- **Lean**: each discriminated-union `inductive T` emits O(N) helper
  definitions and `@[grind]` lemmas in `*.types.lean`:
  ```lean
  attribute [grind cases] Shape          -- omitted for recursive inductives
  @[grind] def Shape.tag : Shape → Nat | .circle .. => 0 | .square .. => 1
  theorem Shape.tag_lt (x : Shape) : Shape.tag x < 2 := by cases x <;> simp [Shape.tag]
  grind_pattern Shape.tag_lt => Shape.tag x
  @[grind] def Shape.is_circle : Shape → Bool | .circle .. => true | _ => false
  @[grind =] theorem Shape.is_circle_eq (x : Shape) : Shape.is_circle x = (Shape.tag x == 0) := by cases x <;> rfl
  @[grind] def Shape.proj_circle_r : Shape → Option (Int) | .circle _v => some _v | _ => none
  @[grind =] theorem Shape.isSome_proj_circle_r (x : Shape) : (Shape.proj_circle_r x).isSome = Shape.is_circle x := by cases x <;> rfl
  ```
  - Why `T.tag` + `grind_pattern T.tag_lt => T.tag x`?
    `attribute [grind cases] T` alone only case-splits bare variables of type
    `T`, not compound expressions like `(sh.get (by grind))` (from
    `Shape | undefined`), array elements `shapes[i]!`, or struct fields.
    Mapping each constructor to a unique `Nat` tag `< N` gives `grind`'s
    arithmetic solver (`cutsat`) complete **exhaustiveness** and **pairwise
    disjointness** for *any* expression of type `T`, in O(N) lemmas rather
    than O(N²).
  - Pure / spec reads emit `(T.proj_ctor_field e).get (by grind)`.
  - Velvet method reads emit `let _v ← LemmaScript.optionValue (T.proj_ctor_field e)`,
    whose `@[spec]` requires `(T.proj_ctor_field e).isSome = true` (discharged
    automatically via `isSome_proj_ctor_field` + `is_ctor_eq` + `tag_lt`).
  - Unnarrowed reads of a field shared across multiple variants emit a direct
    multi-arm `match` in Lean (and `x.field` in Dafny).

---

## 5. Pipeline Architecture

```
TypeScript AST
  │
  ▼  extract.ts (+ lexical-names.ts)
RawIR  (carries optional tsNullish & tsVariant hints on var/field reads)
  │
  ▼  resolve.ts (+ condition-facts.ts)
TypedIR  (inserts coerce nodes, stamps field.ofVariant & record.ctor/ctorOf)
  │
  ▼  narrow.ts  (136 lines — array-index bounds rules ONLY)
TypedIR
  │
  ▼  transform.ts
Backend IR  (direct if/while/&&/|| + nullishTest/nullishCoerce/tagTest/unionProj)
  │
  ▼  peephole.ts  (local map-get & bool simplifications)
  │
  ▼  dafny-emit.ts / lean-emit.ts
Dafny (.dfy) / Lean 4 (.types.lean, .def.lean)
```

### Layer Responsibilities

1. **Extraction ([extract.ts](tools/src/extract.ts), [rawir.ts](tools/src/rawir.ts)):**
   - Queries TypeScript's type checker at `var` and `field` read positions for
     two lightweight hints:
     - `tsNullish`: only attached when the expression's narrowed nullishness is
       strictly narrower than the symbol/property's declared nullishness.
     - `tsVariant`: only attached when a union-typed symbol/property is
       narrowed to a single discriminated-union or synth array-union variant.
   - Emits `nullish` (`??`) and `optChain` (`?.`) as single-evaluation raw IR
     nodes (unchanged).
2. **Resolution ([resolve.ts](tools/src/resolve.ts), [condition-facts.ts](tools/src/condition-facts.ts)):**
   - In TypeScript bodies, trusts `tsNullish` / `tsVariant` hints to wrap reads
     in `coerce` or stamp `field.ofVariant`, `record.ctor`/`ctorOf`, and
     structural call projections.
   - In specification annotations (`//@ requires`, `//@ ensures`, `//@ invariant`,
     etc.) and non-TS frontends where TS hints do not exist, uses
     [condition-facts.ts](tools/src/condition-facts.ts) to propagate nullish
     and variant facts across `if`, `&&`, `==>`, `||`, ternary, `while`, and
     `switch`.
   - Does no control-flow rewriting and introduces no synthetic match binders.
3. **Narrow ([narrow.ts](tools/src/narrow.ts)):**
   - Reduced from 740 lines to **136 lines** (-82%).
   - Contains **only** the 3 array-index bounds rules (`ruleNullishIndex`,
     `ruleOptChainIndex`, `ruleOptionalIndexBinding`), which turn
     `arr[i] ?? fallback` and `arr[i]?.field` into explicit bounds checks
     `0 <= i && i < arr.length` because TypeScript treats `arr[i]` as
     `T | undefined` under `noUncheckedIndexedAccess` while Dafny/Lean require
     a bounds check before indexing.
4. **Transform ([transform.ts](tools/src/transform.ts)):**
   - Lowers control flow directly: `if`, `while`, `switch`, `?:`, `&&`, `||`.
   - Lowers `optChain` (`?.`) and `nullish` (`??`) by evaluating the receiver /
     LHS **once** into a local binding (`let _oc = ...` / `let _nc = ...`) and
     branching with `nullishTest` + `nullishCoerce`.
   - Lowers `coerce` and `unionProj` into `nullishCoerce` / `unionProj` (or
     monadic `← LemmaScript.optionValue` / `nullishValue` / `nullishExclude*`
     in Lean Velvet methods).
   - Preserves short-circuiting in imperative `&&` / `||` expressions (so
     monadic coercions on the RHS execute only when the LHS guard holds).
   - Routes in-place mutations (`obj.xs.push(v)`, `if (Array.isArray(cur)) cur.push(42)`)
     through `buildNestedUpdate`, unwrapping `coerce` layers to read and
     re-wrapping to write back.
5. **Peephole ([peephole.ts](tools/src/peephole.ts)):**
   - Local IR cleanups only, including `ruleLetIfOnMapGetExpr` (collapsing
     `let x = m.get(k) in if x.isSome then ... optionGet(x) ... else ...` into
     `if k in m then let x = m[k] in ... else ...`).
6. **Lean Runtime Support ([Option.lean](LemmaScript/Option.lean), [Nullish.lean](LemmaScript/Nullish.lean)):**
   - `LemmaScript.optionValue` + `optionValue_spec`: Velvet checked unwrap for
     `Option α` (reused for both optionals and DU `proj_*` projectors).
   - `LemmaScript.hashmap_get?_eq_some_{contains,getElem!,get!}` (`@[grind →]`):
     bridges `m.get? k = some v` (produced by `optionValue (m.get? k)`) to
     `m.contains k = true` and `m[k]! = v` for `grind` and proof scripts.
   - `LemmaScript.Nullish α` + pure (`get`, `excludeUndefined`, `excludeNull`,
     `ofOption*`, `trichotomy`) and Velvet (`nullishValue`,
     `nullishExcludeUndefined`, `nullishExcludeNull`) specs.

---

## 6. Lean Velvet Detail: Checked Coercions vs Pure `by grind`

Lean has two distinct expression contexts in LemmaScript:

- **Pure functions and specifications (`*.types.lean`, `requires`/`ensures`/`invariant`):**
  Dependent `if _h : cond then ... else ...` puts the branch hypothesis `_h`
  directly into the local Lean context. Coercions emit dependent unwraps
  `(x.get (by grind))`, `(x.excludeUndefined (by grind))`, and
  `((T.proj_ctor_field x).get (by grind))`. Lean typechecks every proof
  obligation right inside the definition.
- **Velvet imperative methods (`*.def.lean`):**
  Velvet `if cond then ... else ...` does not introduce a dependent proof term
  into the branch expression context; instead, VCGen threads branch conditions
  into verification conditions (VCs). Therefore, Velvet method bodies emit
  monadic checked projections (`let _v ← LemmaScript.optionValue e`,
  `let _v ← LemmaScript.nullishValue e`, etc.) whose `@[spec]` preconditions
  become ordinary VCs discharged by `velvet_vcgen ... with finish` (`grind`).

Loop annotations (`invariant` / `decreasing`) inside Velvet methods are pure
Lean propositions, so `if` statements that enclose a loop with a narrowed
variable in its annotations emit a dependent `if _h : cond = true then` so
`by grind` inside the invariant/decreasing clause sees the guard directly.

---

## 7. Interaction with Lexical Scoping

Coercion narrowing complements [DESIGN_LEXICAL.md](DESIGN_LEXICAL.md) (PR #377):
- `LexicalNames` guarantees that no binding in a function shadows another, so
  a variable name uniquely identifies its declaration in both runtime code and
  annotations.
- Coercion narrowing eliminates all synthetic match binders and path
  substitutions, removing the second source of accidental variable capture.
- Together, every identifier in emitted Dafny/Lean directly corresponds to its
  source declaration, and every narrowing assumption is verified locally by
  the backend.

---

## 8. Regression Coverage and Known Boundaries

- **Tests:** [coercion-narrowing.test.ts](tools/tests/coercion-narrowing.test.ts)
  verifies 18 positive cases (all 14 Phase 1 nullish/optional patterns plus
  4 Phase 2 DU/`Array.isArray`/`typeof`/`switch` patterns) and 7 negative
  soundness tests asserting that Dafny rejects false proofs for `#304`,
  `#342`, `#349`, `#350`, and `#351`.
- **Remaining boundaries:**
  - **User-defined type predicates (`x is T`)** and **`instanceof`** are still
    outside the LemmaScript subset.
  - **Compound variant narrowing** (e.g., narrowing a 3-variant union to a
    2-variant subset `A | B` without accessing a shared field) is not modeled
    as a sub-union type; reads of a field shared by all remaining variants
    work via multi-arm `match` in Lean / direct field access in Dafny, while
    variant-specific field access requires narrowing to a single variant.
  - **Complex expression narrowing** (`if (m.get(k) !== undefined) use(m.get(k))`)
    remains rejected, matching TypeScript's own rule (bind to a local first).
