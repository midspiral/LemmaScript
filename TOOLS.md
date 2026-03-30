# LemmaScript Tools — Internal Architecture

The `lsc` toolchain translates annotated TypeScript to Lean. This document describes the internal architecture for contributors.

## Three Phases

```
TS source (.ts)
  → extract    (ts-morph → raw IR)
  → transform  (raw IR → Lean IR)
  → emit       (Lean IR → .types.lean + .def.lean text)
```

**Extract** parses TypeScript using ts-morph. Produces a raw IR that mirrors the TS AST: functions, statements, expressions, type declarations, `//@ ` annotations. No Lean-specific decisions.

**Transform** converts the raw IR to a Lean IR. This is where all the intelligence lives:
- Type resolution (`number` → `Int`, user types → pass-through, `//@ type` overrides)
- Spec expression translation (`===` → `=`, `\result` → `res`, `forall` → `∀`, `.toNat` insertion)
- Discriminant if-chain detection → `match` nodes
- Conjunction splitting in ensures/requires/invariants
- Implication flattening (`(A && B) ==> C` → curried)
- Ensures-to-match for discriminated unions
- Pure function detection and mirror generation
- Method call detection (`x = f(a, b)` → monadic bind)

**Emit** serializes the Lean IR to text. Trivial pretty-printer — indentation, keywords, no logic.

## Lean IR

The transform phase produces a Lean IR with these node types:

### Top-level declarations

```typescript
type LeanDecl =
  | LeanInductive   // inductive Foo where | a | b ...
  | LeanStructure   // structure Foo where field : Type ...
  | LeanDef         // def foo_pure (params) : RetType := body
  | LeanMethod      // method foo (params) return (res : T) require ... ensures ... do ...
```

### Expressions (used in pure defs, ensures, requires, invariants)

```typescript
type LeanExpr =
  | { kind: "var"; name: string }
  | { kind: "num"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "constructor"; name: string }           // .idle, .allow
  | { kind: "app"; fn: string; args: LeanExpr[] }   // f a b
  | { kind: "binop"; op: string; left: LeanExpr; right: LeanExpr }
  | { kind: "unop"; op: string; expr: LeanExpr }
  | { kind: "if"; cond: LeanExpr; then: LeanExpr; else: LeanExpr }
  | { kind: "match"; scrutinee: string; arms: MatchArm[] }
  | { kind: "record"; fields: { name: string; value: LeanExpr }[] }
  | { kind: "field"; obj: LeanExpr; field: string }  // x.res
  | { kind: "index"; arr: LeanExpr; idx: LeanExpr }  // arr[i]!
  | { kind: "forall"; var: string; type: string; body: LeanExpr }
  | { kind: "exists"; var: string; type: string; body: LeanExpr }
  | { kind: "let"; name: string; value: LeanExpr; body: LeanExpr }
  | { kind: "implies"; premises: LeanExpr[]; conclusion: LeanExpr }

type MatchArm = { pattern: string; bindings: string[]; body: LeanExpr }
```

### Statements (used in Velvet method bodies)

```typescript
type LeanStmt =
  | { kind: "let"; name: string; type: string; mutable: boolean; value: LeanExpr }
  | { kind: "assign"; target: string; value: LeanExpr }
  | { kind: "bind"; target: string; call: LeanExpr }  // x ← f a b
  | { kind: "return"; value: LeanExpr }
  | { kind: "break" }
  | { kind: "if"; cond: LeanExpr; then: LeanStmt[]; else: LeanStmt[] }
  | { kind: "match"; scrutinee: string; arms: { pattern: string; bindings: string[]; body: LeanStmt[] }[] }
  | { kind: "while"; cond: LeanExpr; invariants: LeanExpr[]; decreasing: LeanExpr | null;
      doneWith: LeanExpr | null; body: LeanStmt[] }
```

## Adding a New Feature

1. **Extract**: add the TS construct to the raw IR (new node type or field).
2. **Transform**: add a rule that converts the raw IR node to the appropriate Lean IR node. This is where type-directed decisions happen.
3. **Emit**: usually nothing — if the Lean IR nodes are already supported, the printer handles them.

The emit phase should rarely need changes. If it does, it's adding a new Lean IR node type and its trivial serialization.

## Current State

The three-phase architecture is implemented:

| File | Phase | Role |
|------|-------|------|
| `extract.ts` | Extract | ts-morph → raw IR |
| `specparser.ts` | (parser) | Parses `//@ ` expression language → AST |
| `types.ts` | (shared) | Type mapping helpers (`tsTypeToLean`, `TypeDeclInfo`) |
| `ir.ts` | IR | Lean IR type definitions |
| `transform.ts` | Transform | Raw IR → Lean IR (all intelligence) |
| `emit.ts` | Emit | Lean IR → text (trivial printer) |
| `lsc.ts` | CLI | Wires extract → transform → emit |

