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
unwrapped type. Resolve carries narrowing information through three
mechanisms:

- **`env`** for simple variables. `if (x !== undefined)` extends the
  type environment with `x: T` for the then-branch.
- **`narrowedFields`** for simple `obj.field` chains. `if (obj.field !== undefined)` adds an entry that the field resolver consults when typing
  `obj.field` in the then-branch.
- **`narrowedExprs`** for arbitrary expressions (call results, deep field
  chains, etc.). `if (m.tags.get(tagId) !== undefined)` adds an entry
  matched structurally (via `rawExprEquals`) at the top of `resolveExpr`,
  overriding the type to the unwrapped inner.

Resolve does **no structural rewriting**. It does not substitute, does not
introduce synthetic vars, does not generate `match` constructs.

**Pe owns structural narrowing.** A separate pass between resolve and
transform takes typed IR and rewrites optional-narrowing patterns into a
single IR primitive: `someMatch`. Each TS pattern (`if !== undefined`,
ternary, `&&`, `||`, early return, truthiness, let-with-impure-guard) is
detected by a focused rule and rewritten compositionally. See
[TOOLS.md#pe-rules](TOOLS.md#pe-rules) for the full list.

**Transform owns lowering.** It receives typed IR with `someMatch` nodes
and lowers them to backend-IR `match Some/None`, performing the
appropriate substitution at lowering time (var, simple field, or
TExpr-equality for complex scrutinees). It has no optional-detection
logic of its own.

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

The body keeps its original references to the scrutinee — pe never
substitutes on the typed IR. Substitution happens once during transform's
lowering, dispatched on the scrutinee shape:

| Scrutinee shape | Substitution mechanism |
|-----------------|------------------------|
| `var(x)` | `replaceVar` after lowering — replaces `x` with `binder` in the IR. |
| `field(var(o), f)` | `replaceFieldsInTStmts` / `replaceFieldInTExpr` before lowering — replaces `o.f` with `binder` in the typed IR. |
| Complex (call, deep chain, ...) | `substTExprIn{TStmts,TExpr}` before lowering — TExpr-equality walks the body looking for structural matches. |

The three paths exist because each substitution mechanism naturally fits
its scrutinee shape. They could be unified into one TExpr-equality
substitution, but the simpler mechanisms produce smaller, cleaner output
when applicable.

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

## What Pe Does NOT Cover

- **Discriminated-union narrowing.** `if (e.kind === "lit") use(e.val)` —
  same shape as optional narrowing (a tag check followed by access to
  variant-specific data) but currently handled by transform's
  `detectDiscriminantChain`. Could fold into pe with a generalized
  `someMatch`-like primitive carrying a variant name; not done yet.
- **Cross-function narrowing.** TS narrows across function calls if the
  callee is a type predicate (`function isString(x): x is string`).
  LemmaScript doesn't currently support type predicates.
- **Map.get ceremony elimination.** That's the peephole's job, not pe's.
  Pe rewrites `if (m.get(k) !== undefined) use(m.get(k))` to a `someMatch`
  with `m.get(k)` as the scrutinee; peephole then collapses the resulting
  `match m.get(k)` shape into `if k in m { ... m[k] ... }`.
