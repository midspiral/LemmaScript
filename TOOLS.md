# LemmaScript Tools — Internal Architecture

The `lsc` toolchain translates annotated TypeScript to Lean.

## Pipeline

```
TS source (.ts)
  → extract    (ts-morph → Raw IR)
  → resolve    (Raw IR → Typed IR)
  → transform  (Typed IR → Lean IR)
  → emit       (Lean IR → text)
```

## Three IRs

### Raw IR (`rawir.ts`)

Structured AST from ts-morph. Expressions are nodes, not strings. Has declared type references (`tsType: "Packet"`) but no resolved types. Close to TS syntax.

- `RawExpr`: var, num, str, bool, binop, unop, call, field, index, record
- `RawStmt`: let, assign, return, break, if, while, switch
- `//@ ` annotations remain as strings (parsed by specparser in the resolve pass)

### Typed IR (`typedir.ts`)

Raw IR annotated with resolved types and classifications. Produced by a resolve pass that runs once. Still TS-shaped, not Lean-shaped.

Each expression carries:
- `ty: Ty` — resolved LemmaScript type (nat, int, bool, array, user, etc.)
- Calls carry `callKind` (pure, method)
- Discriminant fields identified

Each statement carries type information for variables. Unsupported patterns (data-carrying variant equality, return in loop) are rejected here with source locations.

### Lean IR (`ir.ts`)

Lean-shaped. Produced by the transform from typed IR. Consumed by the emitter. Has Lean syntax concepts: `∀`, `∃`, `→`, match arms, `let mut`, `←`.

## Phases

**Extract** (`extract.ts`): ts-morph → Raw IR. Walks the TS AST, produces structured expression nodes. Only string outputs are `//@ ` annotation text.

**Resolve** (`resolve.ts`): Raw IR → Typed IR. Resolves types from ts-morph type info and `//@ type` annotations. Classifies calls. Identifies discriminants. Rejects unsupported patterns. Parses `//@ ` annotations with the specparser.

**Transform** (`transform.ts`): Typed IR → Lean IR. Consumes resolved types and classifications. Pattern-matches on `ty` to decide: constructor vs string, `.toNat` vs direct, `if` vs `match`, pure def vs method. No type lookups, no string parsing.

**Emit** (`emit.ts`): Lean IR → text. Trivial pretty-printer.

## Spec Expression Parser

The specparser (`specparser.ts`) parses `//@ ` annotation expressions into `RawExpr` nodes. Called by the resolve pass, not by extract or transform.

## Adding a New Feature

1. **Extract**: add the TS construct to Raw IR.
2. **Resolve**: add type resolution and classification for the new construct.
3. **Transform**: add a Lean IR lowering rule that pattern-matches on the typed node.
4. **Emit**: usually nothing.

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

## Current State

| File | Phase | Role |
|------|-------|------|
| `rawir.ts` | Types | Raw IR type definitions |
| `extract.ts` | Extract | ts-morph → Raw IR |
| `specparser.ts` | (parser) | Parses `//@ ` annotations → RawExpr |
| `resolve.ts` | Resolve | Raw IR → Typed IR |
| `typedir.ts` | Types | Typed IR type definitions |
| `ir.ts` | Types | Lean IR type definitions |
| `transform.ts` | Transform | Typed IR → Lean IR |
| `emit.ts` | Emit | Lean IR → text |
| `types.ts` | (shared) | Type mapping helpers |
| `lsc.ts` | CLI | Wires the pipeline |
