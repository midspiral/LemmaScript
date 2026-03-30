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
