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

Resolve does **no structural rewriting**. It does not substitute, does not
introduce synthetic vars, does not generate `match` constructs.

**Pe owns structural narrowing.** A separate pass between resolve and
transform takes typed IR and rewrites optional-narrowing patterns into a
single IR primitive: `someMatch`. Each TS pattern (`if !== undefined`,
ternary, `&&`, `||`, early return, truthiness, let-with-impure-guard,
optional chain `?.`) is detected by a focused rule and rewritten
compositionally. See [TOOLS.md#pe-rules](TOOLS.md#pe-rules) for the
full list.

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
below), pe constructs the someBody to reference the binder directly, so
transform skips substitution and lowers naively.

---

## Why a Separate Pass

Pe is a separate pass rather than additional resolve or transform logic
because:

- **Bounded responsibility.** Pe does one thing — convert flow-sensitive
  narrowing patterns into structural `someMatch` nodes. It can be tested
  in isolation: feed it typed IR, check the output.
- **Compositional rules.** Each TS pattern gets its own rule, all dispatched
  by a uniform bottom-up walk. Adding a pattern is one new rule, not a
  new path through resolve and a new path through transform.
- **No interaction with unrelated work.** Method dispatch, HOF lowering,
  loop transformation, monadic ANF — all stay in transform. Pe doesn't
  touch them, they don't touch pe.

The `someMatch` primitive is the contract. Resolve doesn't see it
(produces conditionals); transform sees it (lowers to match). Pe is
sandwiched in between, owning the conversion.

---

## Pe vs Peephole

Two passes that operate on different IRs and solve different problems:

- **Pe** runs on typed IR before transform. It eliminates flow-sensitive
  narrowing — rewrites `if (x !== undefined) use(x)` to `someMatch x { ... }`.
- **Peephole** runs on backend IR after transform. It eliminates
  wrap-then-unwrap ceremony around partial-access expressions —
  rewrites `match m.get(k) { Some(v) => v == 0, None => false }` to
  `k in m && m[k] == 0`.

Pe is structural; peephole is local. Pe is necessary for correctness
(without it, the IR has no narrowing); peephole is a cleanup (without
it, the verifier sees through the ceremony but the output is verbose).

They compose: pe converts narrowing to `someMatch` → transform lowers
`someMatch` to `match` → peephole simplifies the `match` if its scrutinee
is a `Map.get` call.

---

## Optional Chaining (`?.`)

TS's `obj?.field` reads the field once, yielding `field's type | undefined`
if `obj` is defined. Extract emits an `optChain { obj, field }` IR node —
a first-class single-evaluation form. Pe's `ruleOptChain` rewrites it to:

```
someMatch obj { Some(_oc{N}_val) => _oc{N}_val.field, None => undefined }
```

The someBody references the binder directly (not the original `obj`), so
transform skips substitution. This is the one case where `someMatch` is
allowed to carry a complex scrutinee (e.g. `m.get(k)`).

The pattern `if (e !== undefined) use(e)` with a complex `e` is *not*
narrowed — per TS semantics, the user must bind: `const v = e; if (v !== undefined) use(v)`. Only `?.` gets special treatment, and only because
extract emits a single-evaluation IR node for it.

---

## What Pe Does NOT Cover

- **Discriminated-union narrowing.** `if (e.kind === "lit") use(e.val)` —
  same shape as optional narrowing (a tag check followed by access to
  variant-specific data) but currently handled by transform's
  `detectDiscriminantChain`. Could fold into pe with a generalized
  `someMatch`-like primitive carrying a variant name; not done yet.
- **Cross-function narrowing.** TS narrows across function calls if the
  callee is a type predicate (`function isString(x): x is string`).
  LemmaScript doesn't currently support type predicates.
- **Complex-expression narrowing.** `if (m.get(k) !== undefined) use(m.get(k))` is rejected (TS-faithful). Users must bind first.
- **Map.get ceremony elimination.** That's the peephole's job, not pe's.
  Once narrowing lowers to `match m.get(k) { ... }`, peephole collapses
  the shape into `if k in m { ... m[k] ... }`.
