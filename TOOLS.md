# LemmaScript Tools — Internal Architecture

The `lsc` toolchain translates annotated TypeScript to formal verification artifacts (Lean or Dafny).

## Pipeline

```
TS source (.ts)
  → extract    (ts-morph → Raw IR)
  → resolve    (Raw IR → Typed IR)
  → transform  (Typed IR → IR, configured per backend)
  → peephole   (IR → IR, local rewrites that eliminate Some/None ceremony)
  → emit       (IR → Lean text or Dafny text)
```

## Three IRs

### Raw IR (`rawir.ts`)

Structured AST from ts-morph. Expressions are nodes, not strings. Has declared type references (`tsType: "Packet"`) but no resolved types. Close to TS syntax.

- `RawExpr`: var, num, str, bool, binop, unop, call, field, index, record
- `RawStmt`: let, assign, return, break, if, while, switch
- `//@ ` annotations remain as strings (parsed by specparser in the resolve pass)

### Typed IR (`typedir.ts`)

Raw IR annotated with resolved types and classifications. Produced by a resolve pass that runs once. Still TS-shaped, not backend-shaped.

Each expression carries:
- `ty: Ty` — resolved LemmaScript type (nat, int, bool, array, user, etc.)
- Calls carry `callKind` (pure, method, spec-pure, unknown)
- Discriminant fields identified

Each statement carries type information for variables. Unsupported patterns (data-carrying variant equality, return in loop) are rejected here with source locations.

### IR (`ir.ts`)

Backend-neutral intermediate representation. Produced by the transform from Typed IR. Consumed by either emitter. Types are preserved as `Ty` objects (not converted to strings) — each emitter converts to its own type syntax.

Type names: `Expr`, `Stmt`, `Decl`, `Module`, `FnDef`, `FnMethod`, `Inductive`, `Structure`, `Namespace`, `MatchArm`, `StmtMatchArm`.

## Phases

**Extract** (`extract.ts`): ts-morph → Raw IR. Walks the TS AST, produces structured expression nodes. Only string outputs are `//@ ` annotation text.

**Resolve** (`resolve.ts`): Raw IR → Typed IR. Resolves types from ts-morph type info and `//@ type` annotations. Classifies calls. Identifies discriminants. Rejects unsupported patterns. Parses `//@ ` annotations with the specparser.

**Transform** (`transform.ts`): Typed IR → IR. Consumes resolved types and classifications. Pattern-matches on `ty` to decide: constructor vs string, `.toNat` vs direct, `if` vs `match`, pure def vs method. Configured with `TransformOptions` for backend-specific behavior (`backend`, `monadic`). No type lookups, no string parsing.

**Peephole** (`peephole.ts`): IR → IR. Local rewrite rules applied bottom-up to fixed point. Eliminates wrap-then-unwrap ceremony around partial-access expressions like `m.get(k)` (which is internally lowered to `methodCall(map, "get", [k])` and emits as `(if k in m then Some(m[k]) else None)`). See [Peephole rules](#peephole-rules) below.

**Emit** (`lean-emit.ts` / `dafny-emit.ts`): IR → text. Each emitter maps `Ty` objects to backend type syntax and method calls to backend-specific syntax.

## Method Calls

All TS `receiver.method(args)` calls produce `methodCall` IR nodes carrying the receiver, its type, the TS method name, the args, and a `monadic` flag. No renaming — the IR stores the TS name (`"map"`, `"indexOf"`, `"with"`, `"get"`, etc.) and the receiver type disambiguates.

Each emitter dispatches on `(receiverTy, method)` to decide syntax. For example, `(array, "map")` → Lean: `arr.map f`, Dafny: `Seq.Map(f, arr)`. Unsupported `(type, method)` pairs error at emit time.

`app` is reserved for receiver-less calls: user-defined functions, `Pure.fnName(...)`, `JSFloorDiv(a, b)`, `SetToSeq(s)`.

## Spec Expression Parser

The specparser (`specparser.ts`) parses `//@ ` annotation expressions into `RawExpr` nodes. Called by the resolve pass, not by extract or transform.

## Adding a New Feature

1. **Extract**: add the TS construct to Raw IR.
2. **Resolve**: add type resolution and classification for the new construct.
3. **Transform**: add an IR lowering rule that pattern-matches on the typed node.
4. **Emit**: add backend-specific rendering in each emitter if the new IR node needs special syntax.

## Scoping

The resolve pass uses linked environments (Scheme-style). Each binding is a frame with one name, one type, and a pointer to the parent:

```ts
interface Env { name: string; ty: Ty; parent: Env | null }
```

`let` extends the chain. Lookup walks it. No mutation, no maps, no copying. `resolveStmt` returns `[TStmt, Env]` so bindings thread through a block. Block-creating constructs (`if`, `while`, `forof`, `switch`) call `resolveBlock`; inner bindings don't leak out. `let x = init` resolves init before adding x to the env.

## Known Limitations

- **Data-carrying variant equality**: `//@ requires m.tag === "b"` where `b` carries data throws an error. Use `switch` to destructure instead.
- **For-of desugaring leaks index variable**: `_x_idx` is visible in `//@ invariant` and `//@ done_with` annotations.
- **Spec annotations are strings**: `//@ ` expressions are parsed by the specparser, not extracted from ts-morph. They don't benefit from the structured raw IR.

## Lean Backend

### Pipeline

```
TS source (.ts)
  → extract    (ts-morph → Raw IR)
  → resolve    (Raw IR → Typed IR)
  → transform  (Typed IR → IR, with LEAN_OPTIONS)
  → peephole   (IR → IR)
  → emit       (IR → Lean text)
```

### Commands (`lean-commands.ts`)

- `lsc gen foo.ts` — generate `.types.lean` + `.def.lean`
- `lsc check foo.ts` — gen + `lake build`

## Dafny Backend

### Pipeline

```
TS source (.ts)
  → extract    (ts-morph → Raw IR)
  → resolve    (Raw IR → Typed IR)
  → transform  (Typed IR → IR, with DAFNY_OPTIONS)
  → peephole   (IR → IR)
  → dafny-emit (IR → Dafny text)
```

### Two-File System

Each TS source produces two Dafny files:

- **`foo.dfy.gen`** — always regeneratable from TS. The merge base.
- **`foo.dfy`** — source of truth. Starts as a copy of `.dfy.gen`, then accumulates user/LLM proof additions. The diff between `.dfy.gen` and `.dfy` must be additions-only.

### Commands (`dafny-commands.ts`)

- `lsc gen --backend=dafny foo.ts` — generate `.dfy.gen` + seed `.dfy`
- `lsc regen --backend=dafny foo.ts` — regenerate `.dfy.gen`, three-way merge, verify
- `lsc check --backend=dafny foo.ts` — gen + additions-only check + `dafny verify`

## Peephole Rules

Local IR-to-IR rewrites applied bottom-up to fixed point at each node, in `peephole.ts`. They eliminate Some/None ceremony that comes from `Map.get(k)` and `Record<K,V>` index access (both lowered to `methodCall(map, "get", [k])`, which `dafny-emit` renders as `(if k in m then Some(m[k]) else None)`).

Each rule is local and semantics-preserving. The pass takes a `backend` parameter — some rules are Dafny-only (see below).

### Map.get rules (both backends)

**Expression rules**

| Pattern | Rewrites to |
|---------|-------------|
| `match m.get(k) { Some(v) => sb, None => nb }` | `if k in m then (let v = m[k] in sb) else nb` |
| `let x = m.get(k) in match x { Some(v) => sb, None => nb }` (when `x` not used in arms) | `if k in m then (let v = m[k] in sb) else nb` |

**Statement rules**

| Pattern | Rewrites to |
|---------|-------------|
| `match m.get(k) { Some(v) => sb, None => nb }` (statement-level) | `if k in m { var v := m[k]; sb } else { nb }` |
| `let x = m.get(k); match x { Some(v) => sb, None => nb }` (when `x` not used after) | `if k in m { var v := m[k]; sb } else { nb }` |

The let-collapse rules require the bound variable to not be referenced after the match (conservative use-count check, no shadowing analysis). When the variable is referenced elsewhere, the `let` is preserved and only the inline `match` rule fires.

The bound value `m[k]` is captured once via `let` (expression form) or `var` (statement form). Substitution would re-evaluate `m[k]` at every use, which changes semantics if the body mutates `m`.

### Boolean simplification rules (Dafny only)

| Pattern | Rewrites to |
|---------|-------------|
| `if c then false else true` | `¬c` |
| `if c then true else false` | `c` |
| `if c then b else false` | `c && b` |
| `if c then true else b` | `c \|\| b` |

These apply only for the Dafny backend. They emit `∧`/`∨` in the IR, which:
- Dafny renders as `&&`/`||` — short-circuit Bool, sound for termination analysis when the right operand contains a recursive call.
- Lean renders as `∧`/`∨` — Prop conjunction/disjunction, which evaluate both arguments. For recursive functions like `if n = 0 then true else f(n - 1) ∧ ...`, the recursive call appears unconditionally in the term and Lean's structural-termination check fails.

For Lean we keep the original `if-then-else` form, which preserves the conditional structure and lets Lean see that the recursive branch is reachable only when the guard holds.

### Emitter precedence

The Dafny emitter wraps `if-then-else` and `let` (var-binding) expressions in parentheses (alongside `match`). Without the parens, an outer `arr[idx]` post-fix would parse into the else branch — e.g., `if c then a else []` followed by `[i]` becomes `... else [][i]` which type-checks against the `[]` rather than the whole if. Always wrapping is verbose but safe.

## Current State

| File | Phase | Role |
|------|-------|------|
| `rawir.ts` | Types | Raw IR type definitions |
| `extract.ts` | Extract | ts-morph → Raw IR |
| `specparser.ts` | (parser) | Parses `//@ ` annotations → RawExpr |
| `resolve.ts` | Resolve | Raw IR → Typed IR |
| `typedir.ts` | Types | Typed IR type definitions |
| `ir.ts` | Types | Backend-neutral IR type definitions |
| `transform.ts` | Transform | Typed IR → IR |
| `peephole.ts` | Peephole | IR → IR (Some/None ceremony elimination) |
| `types.ts` | (shared) | TypeDeclInfo, parseTsType |
| `lean-emit.ts` | Emit | IR → Lean text |
| `dafny-emit.ts` | Emit | IR → Dafny text |
| `lean-commands.ts` | CLI | Lean gen/check commands |
| `dafny-commands.ts` | CLI | Dafny gen/regen/check commands |
| `lsc.ts` | CLI | Wires the pipeline, dispatches to backend |
