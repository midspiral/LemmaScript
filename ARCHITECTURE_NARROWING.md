# Architecture: Narrowing

How LemmaScript translates TypeScript's flow-sensitive `T | undefined`
narrowing into Dafny and Lean (which require single-typed bindings).

For the implementation surface (file roles, rule tables, pipeline diagrams),
see [TOOLS.md](TOOLS.md). This doc focuses on the design choices.

---

## The Problem

TypeScript narrows types **by control flow**. After `if (x !== undefined)`,
inside the then-branch, `x` has type `T` instead of `T | undefined`. The
same identifier carries different types in different scopes.

Dafny and Lean narrow types **by binding introduction**. To use `x` as a
narrower type, you introduce a new binding via `match` or `let`, and uses
of the new type reference the new name.

Every narrowing pattern translation comes down to: **find each narrowing
site, introduce a binding, redirect uses within the narrowed scope to the
binding**. Doing this incrementally — partly in resolve, partly in
transform, sharing intermediate state through TExpr fields — was the
source of years of accumulated tangle (synthetic vars, raw-IR substitution,
duplicated logic in pure-vs-impure paths, scattered field-replacement
helpers).

The current design splits the problem along a clean boundary.

---

## The Split

**Resolve owns type narrowing.** When the type checker walks `if (e !== undefined) use(e)`, the body's `use(e)` needs to typecheck with `e` of the
unwrapped type. Following TS semantics, resolve only narrows simple shapes:

- **`env`** for simple variables. `if (x !== undefined)` extends the
  type environment with `x: T` for the then-branch.
- **`narrowedPaths`** for any pure access path (`obj.field`, `a.b.c.d`,
  any depth). Each entry pairs a path (root var + field chain) with the
  unwrapped type. The field resolver computes the path of each access and
  looks it up. `&&` chains accumulate narrowings so each premise is in
  scope for later ones, matching TS narrowing through `&&`. The same
  applies through `==>` in spec contexts (premise narrows conclusion).

Complex expressions (call results, index ops) are **not** narrowed —
matching TS, which requires the user to bind first:
`const v = m.get(k); if (v !== undefined) use(v)`. This avoids the
soundness hazard of retyping based on structural equality of impure calls.

Resolve does **no structural rewriting** for narrowing: no substitution, no
synthetic vars, no `match` generation. Its one rewriting step is
[callback binding](TOOLS.md#callback-binding-and-lowering), which uses the
lexical environment to bind callback parameters.

**Narrow owns structural narrowing.** A separate pass between resolve and
transform takes typed IR and rewrites optional-narrowing patterns into a
single IR primitive: `someMatch`. Each TS pattern (`if !== undefined`,
ternary, `&&`, `||`, early return, truthiness, let-with-impure-guard,
optional chain `?.`) is detected by a focused rule and rewritten
compositionally. The rules are positional drivers: *what* each condition
establishes lives in `condition-facts.ts`, shared with resolve so a check is
taught once. See [TOOLS.md#narrow-rules](TOOLS.md#narrow-rules) for the full
list.

**Transform owns lowering.** It receives typed IR with `someMatch` nodes
and lowers them to backend-IR `match Some/None`, performing a light
substitution for var/simple-field scrutinees (see the table below). It
has no optional-detection logic of its own.

---

## The `someMatch` Primitive

The single IR node that all narrowing rewrites produce:

```ts
| { kind: "someMatch";
    scrutinee: TExpr;     // var, field chain, or arbitrary expression
    binder: string;       // fresh name for the unwrapped value
    binderTy: Ty;         // inner (non-optional) type
    someBody: TExpr;      // (or TStmt[] for the statement-level form)
    noneBody: TExpr;      // (or TStmt[])
    ty: Ty }
```

Both expression and statement variants exist. They lower uniformly:
`match scrutinee { Some(binder) => someBody, None => noneBody }`.

For pure access path scrutinees (var or any depth of `obj.f.g.h`), the
body keeps its original references — transform substitutes the entire
path with the binder at lowering time via `replacePathInTExpr` /
`replacePathInTStmts`. The substitution walks the typed IR looking for
TExprs whose access-path shape matches the scrutinee exactly.

For complex scrutinees (only produced by the `optChain` rewrite — see
below), narrow constructs the someBody to reference the binder directly,
so transform skips substitution and lowers naively.

---

## Why a Separate Pass

Narrow is a separate pass mostly because the rewrites compose better in
isolation than they did when scattered across resolve and transform:

- **Each pattern is one rule** instead of a code path in resolve plus one
  in transform. Adding a TS narrowing pattern is one rule in narrow.
- **Narrow doesn't touch unrelated work.** Method dispatch, HOF lowering,
  loop transformation, monadic ANF — all stay in transform. Narrow only
  rewrites optional-narrowing shapes.
- **The `someMatch` primitive** is the contract between layers. Resolve
  produces conditionals (no someMatch); transform consumes someMatch
  (lowers to match Some/None). Narrow sits in between, doing the conversion.

Note: each new TS pattern still touches all three layers (resolve to type
narrowed accesses, narrow to rewrite the shape, transform to substitute the
binder). Narrow is the *structural* layer of a three-layer system, not a
hermetic component.

---

## Narrow vs Peephole

Two passes that operate on different IRs and solve different problems:

- **Narrow** runs on typed IR before transform. It eliminates flow-sensitive
  narrowing — rewrites `if (x !== undefined) use(x)` to `someMatch x { ... }`.
- **Peephole** runs on backend IR after transform. It eliminates
  wrap-then-unwrap ceremony around partial-access expressions —
  rewrites `match m.get(k) { Some(v) => v == 0, None => false }` to
  `k in m && m[k] == 0`.

Narrow is structural; peephole is local. Narrow is necessary for correctness
(without it, the IR has no narrowing); peephole is a cleanup (without
it, the verifier sees through the ceremony but the output is verbose).

They compose: narrow converts narrowing to `someMatch` → transform lowers
`someMatch` to `match` → peephole simplifies the `match` if its scrutinee
is a `Map.get` call.

---

## Optional Chaining (`?.`) and Nullish Coalescing (`??`)

TS's `obj?.field` reads the field once. Extract emits an `optChain { obj, chain }`
IR node where `chain` is a list of steps — each step is a `field`, `call`,
or `index`. So `obj?.foo()`, `obj?.[k]`, `obj?.a.b.c`, and `obj?.a?.b?.c` all
share the same IR (chained `?.` produces nested optChains). Narrow's
`ruleOptChain` rewrites by applying the chain to a fresh binder:

```
someMatch obj { Some(_oc{N}_val) => apply(chain, _oc{N}_val), None => undefined }
```

`x ?? y` (nullish coalescing) gets its own `nullish` IR node that narrow
rewrites to `someMatch x { Some(_v) => _v, None => y }`.

For both, the someBody references the binder directly (not the original
`obj`/`left`), so transform skips substitution. These are the only cases
where `someMatch` carries a complex scrutinee (call result, etc.).

The pattern `if (e !== undefined) use(e)` with a complex `e` is *not*
narrowed — per TS semantics, the user must bind: `const v = e; if (v !== undefined) use(v)`. Only `?.` and `??` get special treatment, and only
because extract emits single-evaluation IR nodes for them.

---

## Discriminated-Union Narrowing

Detected in `narrow.ts` (alongside optional narrowing) via
`ruleDiscriminantChain` and `ruleDiscriminantNegEarlyReturn`. Each emits
a `tagMatch` IR node — the multi-case analog of `someMatch` — that
transform lowers via `emitMatchStmt` / `transformPureMatch`.

Recognized patterns:

- `if (x.kind === "v") ... else if (x.kind === "w") ...` — chain of equality
  checks on a discriminator field.
- `if ('key' in x) ...` — narrows to the unique variant containing `key`.
  Looks up the variant from the type's declarations (carried in the `CondCtx`
  threaded through the pass).
- `if (x.kind !== "v") terminate; rest` — negative early-return form;
  rest becomes the variant's body, terminator becomes the fallthrough.
- `switch (x.kind) { case "v": ... }` — exhaustive variant matching
  (still handled in transform's `emitSwitchStmt` since it's a syntactic
  switch, not an if-chain).

When the chain covers all variants but one, the fallthrough `_` arm is
replaced with the remaining variant's pattern.

Pure functions (`transformPureSwitch` / `transformPureMatch`) destructure
each arm into per-field match binders (`case a(i_x_n) => ...`). Imperative
methods (`emitSwitchStmt` / `emitMatchStmt`) always match union arms with
wildcard patterns (`case a(_) => ...` / `| .a _ => ...`) and operate directly
on live scrutinee storage — avoiding stale binders when a branch reassigns
the scrutinee, mutates a field, or captures it in a callback (in Lean,
spreads and field writes on multi-constructor inductives emit
constructor-preserving `match` updates).

---

## What Narrow Does NOT Cover

- **Cross-function narrowing.** TS narrows across function calls if the
  callee is a type predicate (`function isString(x): x is string`).
  LemmaScript doesn't currently support type predicates.
- **`typeof x === "string"`** for `string | number` unions. Our subset
  uses tagged unions, so this is rare.
- **`instanceof`** — irrelevant in our subset (no class hierarchies).
- **Compound discriminants** (`x.kind === "a" || x.kind === "b" ==> use(x.shared)`).
  TS narrows to the variants that share the field; we don't.
- **Complex-expression narrowing.** `if (m.get(k) !== undefined) use(m.get(k))` is rejected (TS-faithful). Users must bind first.
- **Re-widening on mutation.** Within a function, `resolve.ts` tracks each variable's declared `storageTy` separately from its narrowed flow type and restores `storageTy` (dropping affected `narrowedPaths`) after mutating `assign`, `if`, `while`, `forof`, and `switch` statements. Cross-function mutation re-widening is not modeled.
- **Map.get ceremony elimination.** That's the peephole's job, not narrow's.
  Once narrowing lowers to `match m.get(k) { ... }`, peephole collapses
  the shape into `if k in m { ... m[k] ... }`.

---

## Hybrid Checked Reads, `Place` Write-Back, and Live-Alias Rejection

`someMatch` alone breaks down when a narrowed value is mutated in place,
cleared to `undefined` inside a branch, or narrowed across a `while`
condition, definite assignment, or `||` chain. Three additions extend the
pipeline while keeping `someMatch` for safe cases (preserving zero diff
churn on existing proofs):

1. **Checked reads (`checked-reads.ts`).** Runs at the end of `narrow` on
   any variable or field path whose declared `storageTy` is `Option<T>`
   (or `Nullish<T>`) but whose flow type was narrowed without an enclosing
   `someMatch` (such as `while (cur !== undefined)`, definite assignment
   `if (v === undefined) { v = 6; }`, `||` chains, or a branch that may
   clear the variable), wrapping those reads in `checkedUnwrap` (`.value` in
   Dafny; `.get (by grind)` in Lean, with dependent `if _h : ...` guards).
   Direct operands of `=== undefined` / `!== undefined` are never unwrapped.
   `checked-reads.ts` also projects flow-narrowed reads of synthesized
   array-unions (`ArrayBranch` / `NonArrayBranch`) to `.arr` / `.val`
   directly on live storage.
2. **Unified `Place` write-back (`places.ts`, `place-lowering.ts`, `transform.ts`).**
   In-place mutations (`arr.push`, `arr[i] = v`, nested field writes,
   optional `pop`/`shift`, `m.get(k)?.push`) inside a `someMatch` arm write
   back through the active `unwrap` frames so storage and binder stay in
   sync (re-wrapping `Option.Some(...)`). Imperative union arms do not need
   variant write-back frames because they operate directly on live storage.
   The pure `PlacePath` kernel in `tools/src/places.ts` is self-verified
   in CI (`LemmaScript-files.txt`).
3. **Live-alias mutation rejection (`alias-check.ts`, `alias-check-pass.ts`).**
   Because Dafny and Lean model arrays, maps, sets, and records as
   immutable values, mutating a container through an alias while the
   original binding is still read afterward would silently prove false
   postconditions. `alias-check-pass.ts` combines backward liveness with
   forward alias tracking and rejects live-alias mutations while allowing
   read-only sharing, dead-source moves, and explicit clones. Its conflict
   kernel in `tools/src/alias-check.ts` is also self-verified in CI.
4. **Precondition-preserving optional comparisons (`transform.ts`).**
   When an executable optional/nullish comparison (`===`, `!==`, `<`, `<=`, `>`, `>=`)
   has a precondition-bearing non-optional operand (calls, indexing,
   checked reads, `/`, `%`), `transform.ts` binds it in `let _cmpN := ...`
   before matching so its preconditions are checked even on absent values.
   Spec clauses (`requires`/`ensures`/`invariants`) skip this hoisting.
5. **Selective `Nullish<T>` (`types.ts`, `condition-facts.ts`, `resolve.ts`, `transform.ts`, `LemmaScript/Nullish.lean`).**
   Single-sentinel `T | undefined` and `T | null` stay on `Option<T>` while
   recording which absent sentinel `None` models (so strict `===` distinguishes
   `null` from `undefined` and loose `==` matches either). Types that include
   both `null` and `undefined` (`T | null | undefined`, `x?: T | null`) use a
   three-case `Nullish<T>` datatype (`Undefined | Null | Value(value: T)` in
   Dafny; on-demand `LemmaScript.Nullish` in Lean). Two-step strict narrowing
   (`nullish` → `optional(fromNullish)` → `T`) stays off `someMatch` and uses
   `checkedUnwrap` once both sentinels are ruled out.

The formal core calculus for checked reads, `Place` write-back, and
`Nullish<T>` lives in [formal/narrowing-model.dfy](formal/narrowing-model.dfy)
(verified in CI), and the 4-way fuzzer scorecard lives in
[formal/narrowing-shootout.md](formal/narrowing-shootout.md).
