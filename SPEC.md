# LemmaScript — Implementation Specification

**Version:** 0.2
**Date:** March 2026
**Status:** Specification for rewrite, informed by Phase 0 findings

---

## 1. Overview

LemmaScript is a verification toolchain for TypeScript. The user writes TypeScript with `//@ ` annotations. Ghost definitions and proofs live in Lean 4 files alongside the TS source. The toolchain generates a Lean method definition; Lean checks it against the user's proof.

The toolchain has three components:
1. **`lsc` CLI** (Node.js) — parses TS, generates Lean method definitions
2. **LemmaScript Lean library** — re-exports Velvet/Loom, provides any needed macros
3. **Pre-built oleans** — so user projects don't recompile the dependency chain

---

## 2. User Project Structure

LemmaScript is a library. Each user project depends on it.

```
my-app/
  src/
    binarySearch.ts              ← TypeScript source
    binarySearch.types.lean      ← Lean types from TS (generated, gitignored)
    binarySearch.spec.lean       ← ghost definitions, lemmas (user-written)
    binarySearch.def.lean        ← method definition (generated, gitignored)
    binarySearch.proof.lean      ← prove_correct + tactics (user/LLM-written)
  lakefile.lean                  ← requires LemmaScript
  lean-toolchain
  package.json                   ← depends on @lemmascript/tools
```

### 2.1 The Four Lean Files

For each verified TS function `foo.ts`, there are up to four Lean files:

| File | Who writes it | Version-controlled? | Purpose |
|------|--------------|-------------------|---------|
| `foo.types.lean` | `lsc gen` | No (gitignored) | Lean type definitions derived from TS types |
| `foo.spec.lean` | User | Yes | Ghost definitions, helper lemmas |
| `foo.def.lean` | `lsc gen` | No (gitignored) | Method definition (generated from TS) |
| `foo.proof.lean` | User / LLM | Yes | `prove_correct` with proof tactics |

**Key property:** `foo.types.lean` and `foo.def.lean` are always regeneratable from `foo.ts`. The user only writes `.spec.lean` and `.proof.lean`.

### 2.2 Import Chain

```
foo.types.lean         ← generated: Lean inductives/structures from TS types
foo.spec.lean          ← imports foo.types.lean, user-written ghost definitions
foo.def.lean           ← imports foo.spec.lean, generated method definition
foo.proof.lean         ← imports foo.def.lean, user-written proof
```

Each file imports the previous. Lean checks the full chain.

### 2.3 File Naming and Lake Modules

Files use dotted names: `binarySearch.spec.lean`. In Lean imports, dots in filenames are escaped:

```lean
import «binarySearch.spec»
import «binarySearch.def»
```

All files live in `src/`, which Lake is configured to scan. No nested `lean/` directory.

**`lsc init`** scaffolds `lakefile.lean`, `lean-toolchain`, and the LemmaScript dependency.

---

## 3. The `//@ ` Annotation Language

### 3.1 Annotation Kinds

Annotations are TypeScript comments of the form `//@ <keyword> <expression>`.

| Keyword | Placement | Meaning |
|---------|-----------|---------|
| `requires` | Before first statement of function body | Precondition |
| `ensures` | Before first statement of function body | Postcondition (`\result` refers to return value) |
| `invariant` | Before first statement of loop body | Loop invariant |
| `decreases` | Before first statement of loop body | Termination metric |
| `type` | Before first statement of function body | Type override for a variable (see §3.3) |

### 3.2 Spec Expression Grammar

The expression language is a subset of TypeScript with verification extensions.

```
expr     := implies
implies  := or ('==>' implies)?          // right-associative
or       := and ('||' and)*
and      := compare ('&&' compare)*
compare  := add (cmpOp add)?
cmpOp    := '===' | '!==' | '>=' | '<=' | '>' | '<'
add      := mul (('+' | '-') mul)*
mul      := unary (('*' | '/' | '%') unary)*
unary    := '!' unary | '-' unary | postfix
postfix  := atom ('.' ident | '[' expr ']' | '(' args ')')*
atom     := NUMBER | IDENT | 'true' | 'false' | '\result'
          | 'forall' '(' IDENT (':' TYPE)? ',' expr ')'
          | 'exists' '(' IDENT (':' TYPE)? ',' expr ')'
          | '(' expr ')'
TYPE     := 'nat' | 'int'
```

**`\result`** refers to the function's return value (following Frama-C/ACSL convention). It is only valid in `ensures` annotations. The `\` prefix distinguishes it from any TS variable named `result`.

**`forall(k, P)`** quantifies `k` as `Int` by default. **`forall(k: nat, P)`** quantifies as `Nat`.

### 3.3 Type Annotations

The codegen reads TS types from ts-morph and maps them to Lean (see §8). For `number` variables, the default mapping is `Int`. The `type` annotation overrides this to `Nat`:

```
//@ type <varname> nat
```

Use `nat` for non-negative loop counters and array indices.

User-defined types (string literal unions, discriminated unions) are generated automatically in `.types.lean` with the same name as the TS type. No annotation needed or supported for these.

When a variable is `Nat`-typed:
- `arr[i]!` instead of `arr[i.toNat]!`
- Ghost function calls pass the variable directly

---

## 4. Spec Expression → Lean Translation

The translation is purely syntactic. The codegen does not infer types beyond what `//@ type` annotations provide.

### 4.1 Operator Mapping

| Spec | Lean |
|------|------|
| `===` | `=` |
| `!==` | `≠` |
| `>=` | `≥` |
| `<=` | `≤` |
| `>` | `>` |
| `<` | `<` |
| `&&` | `∧` |
| `\|\|` | `∨` |
| `!` | `¬` |
| `==>` | `→` |
| `+`, `-`, `*`, `/`, `%` | `+`, `-`, `*`, `/`, `%` |

No normalization of operators. Lean and `loom_solve` handle all comparison directions.

### 4.2 Special Forms

| Spec | Lean | Notes |
|------|------|-------|
| `arr.length` | `arr.size` | Always `Nat`. Lean coerces to `Int` in mixed contexts. |
| `arr[e]` where `e` is Nat-typed | `arr[e]!` | Direct Nat index. |
| `arr[e]` where `e` is Int-typed | `arr[e.toNat]!` | Int-to-Nat conversion for indexing. |
| `f(a, b)` | `f a b` | Ghost function call or Velvet method call. |
| `x = f(a, b)` (in body) | `x ← f a b` | Velvet method call uses monadic bind. |
| `Math.floor(e)` | `e` | Int division in Lean is already floor. |
| `\result` | `res` | Only valid in `ensures`. |
| `"foo"` (string literal, enum context) | `.foo` | Constructor. Lean infers type from context. |
| `x.tag === "foo"` (discriminant check) | `match` arm | See §5.4 and §8.3. |
| `x.field` (in narrowed branch) | bound variable | From match pattern. See §5.4. |
| `forall(k, P)` | `∀ k : Int, P'` | Default Int quantification. |
| `forall(k: nat, P)` | `∀ k : Nat, P'` | Nat quantification. |

### 4.3 Nat-Typing Rules

An expression is Nat-typed if:
- It's a variable declared with `//@ type <v> nat`
- It's a quantified variable with `: nat` in the quantifier
- It's `arr.length` (i.e., `arr.size`)
- It's an arithmetic expression (`+`, `-`, `*`, `/`, `%`) where both operands are Nat-typed
- It's a non-negative numeric literal

The Nat-typing determines whether `.toNat` is needed for array indexing.

### 4.4 Implication Flattening

`(A && B) ==> C` is emitted as `A → B → C` (curried). This is standard Lean idiom.

### 4.5 Conjunction Splitting

Top-level `&&` in `requires`, `ensures`, and `invariant` annotations is split into separate clauses:

```
//@ ensures \result >= -1 && \result < arr.length
```

generates:

```lean
ensures res ≥ -1
ensures res < arr.size
```

---

## 5. Statement Translation (TS → Lean)

### 5.1 Basic Statements

| TypeScript | Lean | Notes |
|-----------|------|-------|
| `let x = e` | `let mut x : T := e'` | Mutable. `T` from type map (§3.3). |
| `const x = e` | `let x := e'` | Immutable. No type annotation. |
| `x = e` | `x := e'` | Assignment. |
| `return e` | `return e'` | Not supported inside loops — see §5.3. |
| `if (c) { ... }` | `if c' then ...` | |
| `if (c) { ... } else { ... }` | `if c' then ... else ...` | |
| `if (c) { ... } else if ...` | `if c' then ... else if ...` | Chained. |
| `while (c) { ... }` | `while c' invariant ... decreasing ... do ...` | See §5.2. |
| `x = f(a, b)` | `x ← f a b` | Velvet method call (monadic bind). |
| `break` | `break` | Only inside while loops. |
| `switch` / discriminant if-chain | `match` | See §5.4. |

All expressions `e` in the table above are translated using the spec expression rules (§4).

**Discriminant if-chains (data-carrying unions only):** When the codegen encounters an if-else chain where each condition tests `x.discriminantField === "variant"` on a discriminated union with data fields, it emits a Lean `match` instead of `if`. This is necessary because Lean's `if` cannot bind constructor fields — only `match` can. For enum-like types (string-literal unions, no data), `if` stays `if` with `DecidableEq`. See §5.4 and §8.3.

### 5.2 While Loops

```typescript
while (condition) {
  //@ invariant P
  //@ invariant Q
  //@ decreases D
  body
}
```

generates:

```lean
while condition'
  invariant P'
  invariant Q'
  decreasing D'
do
  body'
```

**Decreasing clause:** Emitted directly as a Lean expression. Lean's termination checker accepts any type with a well-founded relation — `Nat`, lexicographic tuples `(a, b)`, etc. The codegen does not add `.toNat` automatically; the user writes the decreasing expression in the form Lean expects.

**`done_with` clause:** If the loop body contains `break`, the user should add a `//@ done_with` annotation specifying what is true when the loop exits. (If omitted, Velvet defaults to the negation of the loop condition, which is only correct when there is no `break`.)

### 5.3 Return Inside Loops

`return` inside a `while` loop is **not supported**. Velvet does not support `return` inside loops, and the codegen does not transform it. If the codegen encounters `return` inside a loop, it emits an error.

The user must restructure their TypeScript to use `break` with an explicit result variable:

```typescript
// Unsupported:
while (...) {
  if (...) return mid;
}
return -1;

// Supported:
let result = -1;
while (...) {
  //@ invariant ...
  //@ done_with result !== -1 || !(lo <= hi)
  if (...) { result = mid; break; }
}
return result;
```

The TypeScript is still valid and runs identically. The verified version uses `break` instead of `return`, which maps directly to Velvet's `break` construct. The user writes invariants about their own `result` variable — no codegen magic.

### 5.4 Discriminant Dispatch → Match

Both `switch` on a discriminant and if-chains on a discriminant translate to Lean `match`. The codegen detects the pattern: conditions of the form `x.field === "variant"` (or `x === "variant"` for enum-like types) on the same variable.

**If-chain:**
```typescript
if (pkt.tag === "syn") return pkt.seq;
if (pkt.tag === "data") return state + pkt.len;
return state;
```

**Switch:**
```typescript
switch (pkt.tag) {
  case "syn": return pkt.seq;
  case "data": return state + pkt.len;
  default: return state;
}
```

Both produce the same Lean:

```lean
match pkt with
| .syn seq => return seq
| .data _ len => return state + len
| _ => return state
```

**Detection:** ts-morph provides the variable's type (discriminated union), the discriminant field name, and the variant field types. The codegen uses this — no guessing.

**Field binding:** Property accesses on the matched variable (`pkt.seq`, `pkt.len`) become bound variables from the match pattern. Unused fields get `_`.

**Enum-like types** (string literal unions, no data fields) stay as `if` with `DecidableEq`. The codegen does NOT convert them to `match`. `state === "idle"` → `state = .idle` (simple equality). Only discriminated unions with data fields trigger the if-chain → match transformation.

---

## 6. Generated Lean Files

For `src/foo.ts`, `lsc gen` produces `src/foo.types.lean` and `src/foo.def.lean`.

`foo.types.lean` contains Lean type definitions derived from TS `type` declarations (string literal unions, discriminated unions, etc.). If the TS file has no user-defined types, this file is not generated.

`foo.def.lean` contains the Velvet `method` definition:

```lean
/-
  Generated by lsc from foo.ts
  Do not edit — re-run `lsc gen` to regenerate.
-/
import «foo.spec»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

method foo (params...) return (res : RetType)
  require ...
  ensures ...
  do
    ...
```

The generated file contains **only the method definition**, no `prove_correct`. The proof lives in `foo.proof.lean`.

**Import chain:** `foo.def.lean` imports `foo.spec.lean`, which imports `foo.types.lean` (if it exists). If there is no `.spec.lean`, `foo.def.lean` imports `foo.types.lean` directly (or Velvet/Loom if there are no types either).

---

## 7. User-Written `.proof.lean` File

```lean
import «binarySearch.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct binarySearch by
  loom_solve
```

This is the simplest proof — delegate everything to `loom_solve`. When `loom_solve` fails:

1. `lsc check` reports unsolved goals.
2. The user (or LLM) edits `.proof.lean` to add fallback tactics:

```lean
prove_correct binarySearch by
  loom_solve!
  · -- handle remaining goal
    grind
```

3. Or the user adds helper lemmas to `.spec.lean` that `loom_solve` can use.

**Invariants** are part of the method definition (in the `//@ ` annotations), not the proof. If an invariant is missing, the user adds `//@ invariant` to the TS file and regenerates `.def.lean`.

### 7.1 Standalone Lemmas

Properties about functions can be proved as standalone Hoare triples in `.proof.lean`, separately from the function's `requires`/`ensures`. This is useful when:
- The function has no natural precondition but interesting properties hold under specific conditions
- Multiple properties should be proved about the same function
- The property involves multiple functions

```lean
-- The function has no ensures — just loop invariants
prove_correct runSession by
  loom_solve

-- Property proved separately as a Hoare triple
open TotalCorrectness DemonicChoice in
theorem runSession_timeout_resets (events : Array Event)
    (h1 : events.size > 0) (h2 : lastEvent events = .timeout) :
    triple (events.size > 0 ∧ lastEvent events = .timeout)
           (runSession events)
           (fun res => res = State.idle) := by
  unfold runSession
  loom_solve
```

The pattern: `unfold` the method to expose the body, then `loom_solve` to discharge the VCs. The loop invariants from the method definition are available after unfolding.

---

## 8. Type Mapping

### 8.1 Rules

| TypeScript type | Lean type | Notes |
|----------------|-----------|-------|
| `number` | `Int` | Default. `Nat` via `//@ type v nat`. |
| `boolean` | `Bool` | |
| `string` | `String` | |
| `T[]` / `Array<T>` | `Array T'` | `T'` is the Lean mapping of `T`. |
| Anything else | Pass through | `State` → `State`. Generated in `.types.lean`. |

The codegen reads parameter and variable types from ts-morph. Primitive types are mapped per the table. User-defined types (like `State`, `Event`) are passed through by name — the corresponding Lean type is generated in `.types.lean`.

`//@ type v nat` overrides the primitive mapping for `number` variables:
- `//@ type i nat` — `number` → `Nat` instead of `Int`

This is the only supported override. User-defined types (string literal unions, discriminated unions) are generated in `.types.lean` with the same name as the TS type. The TS name IS the Lean name — no renaming.

### 8.2 String Literals as Constructors

When a variable has a user-defined type, string literal comparisons map to Lean constructor equality:

| TypeScript | Lean |
|-----------|------|
| `state === "idle"` | `state = .idle` |
| `"connecting"` (as value) | `.connecting` |

Convention: the string literal and the Lean constructor have the same name. Lean infers the type from context (dot notation).

### 8.3 Discriminated Unions

Discriminated unions with data fields map to Lean inductives with constructor arguments.

```typescript
type Packet =
  | { tag: "syn"; seq: number }
  | { tag: "ack"; seq: number }
  | { tag: "data"; seq: number; len: number }
  | { tag: "fin" }
```

Generated in `.types.lean`:

```lean
inductive Packet where
  | syn (seq : Int) : Packet
  | ack (seq : Int) : Packet
  | data (seq : Int) (len : Int) : Packet
  | fin : Packet
deriving Repr, Inhabited
```

**If-chains on the discriminant → Lean `match`.**  When the codegen encounters an if-else chain where each condition tests `x.field === "variant"` on the same variable, it emits a `match`. ts-morph provides the discriminant field name, variant types, and field names — no guessing.

```typescript
if (pkt.tag === "syn") return pkt.seq;
if (pkt.tag === "ack") return state;
if (pkt.tag === "data") return state + pkt.len;
return state;
```

→

```lean
match pkt with
| .syn seq => return seq
| .ack _ => return state
| .data _ len => return state + len
| .fin => return state
```

**Field binding:** In each branch, `pkt.fieldName` becomes the bound variable `fieldName` from the match pattern. Field names match by construction since `.types.lean` is generated from the same TS type.

**`switch` also works:** A TS `switch (pkt.tag) { case "syn": ... }` translates to the same Lean `match`.

**Ensures with discriminated unions:** Specs that condition on the variant use `match` in the Lean ensures:

```typescript
//@ ensures pkt.tag === "syn" ==> \result === pkt.seq
//@ ensures pkt.tag === "data" ==> \result === state + pkt.len
```

→

```lean
ensures match pkt with
  | .syn seq => res = seq
  | .data _ len => res = state + len
  | _ => True
```

### 8.4 Full Examples

**Example 1: State machine (enum-like, no data)**

String literal unions with no data use `if` with constructor equality. `DecidableEq` makes this work.

```typescript
type State = "idle" | "connecting" | "connected" | "closing"
type Event = "connect" | "ack" | "close" | "timeout"

function transition(state: State, event: Event): State {
  //@ ensures event === "timeout" ==> \result === "idle"
  if (state === "idle" && event === "connect") return "connecting";
  if (state === "connecting" && event === "ack") return "connected";
  if (state === "connected" && event === "close") return "closing";
  if (state === "closing" && event === "ack") return "idle";
  if (event === "timeout") return "idle";
  return state;
}

function runSession(events: Event[]): State {
  //@ type i nat
  //@ requires events.length > 0
  //@ requires lastEvent(events) === "timeout"
  //@ ensures \result === "idle"
  let state: State = "idle";
  let i = 0;
  while (i < events.length) {
    //@ invariant i <= events.length
    //@ invariant i > 0 && events[i - 1] === "timeout" ==> state === "idle"
    //@ decreases events.length - i
    state = transition(state, events[i]);
    i = i + 1;
  }
  return state;
}
```

Generated `.types.lean`: inductives with `DecidableEq`. Generated `.def.lean`: `if state = .idle ∧ event = .connect then return .connecting` etc. `loom_solve` discharges all VCs automatically, including the inter-method call (runSession uses transition's ensures).

**Example 2: Packet processing (discriminated union with data)**

```typescript
type Packet =
  | { tag: "syn"; seq: number }
  | { tag: "ack"; seq: number }
  | { tag: "data"; seq: number; len: number }
  | { tag: "fin" }

function nextSeq(state: number, pkt: Packet): number {
  //@ ensures pkt.tag === "syn" ==> \result === pkt.seq
  //@ ensures pkt.tag === "data" ==> \result === state + pkt.len
  //@ ensures pkt.tag === "fin" ==> \result === state
  if (pkt.tag === "syn") return pkt.seq;
  if (pkt.tag === "ack") return state;
  if (pkt.tag === "data") return state + pkt.len;
  return state;
}
```

Generated `.def.lean` uses `match` for the body and ensures. `loom_solve` handles it automatically.

Both examples are validated — the generated Lean compiles and verifies.

### 8.5 Type Mapping Implementation

Type mapping logic lives in a single `types.ts` module imported by both codegen and specparser.

The module provides:
- `tsTypeToLean(tsType: string): string` — primitive type mapping, pass-through for user-defined types
- `isNatType(leanType: string): boolean` — `leanType === "Nat"`
- `isArrayType(leanType: string): boolean` — `leanType.startsWith("Array ")`

---

## 9. `lsc` CLI

```
lsc init                    — scaffold lakefile.lean + lean-toolchain
lsc gen <file.ts>           — generate .def.lean from TS
lsc check <file.ts>        — gen + lake build (checks .def.lean + .proof.lean)
lsc check --watch           — re-check on file changes
lsc extract <file.ts>       — print IR JSON (debugging)
```

**`lsc gen` workflow:**
1. Parse TS file with ts-morph → IR (including type declarations).
2. Generate `foo.types.lean` from TS type declarations (if any).
3. Generate `foo.def.lean` from function definitions + `//@ ` annotations.
4. Write both to `src/` next to the TS file.

**`lsc check` workflow:**
1. Run `lsc gen`.
2. Run `lake build` (checks `.def.lean` + `.proof.lean` + `.spec.lean`).
3. Report results.

**`lsc init` workflow:**
1. Create `lakefile.lean` requiring LemmaScript.
2. Create `lean-toolchain` matching LemmaScript's Lean version.
3. Download pre-built oleans for LemmaScript + dependencies.

---

## 10. LemmaScript Lean Library

The LemmaScript Lean library provides:

1. **Re-exports of Velvet (forked) and Loom.** Users import `LemmaScript` and get everything.
2. **Velvet fork:** One change from upstream — obligations are persisted across files so `prove_correct` works in a separate file from `method`.
3. **Any LemmaScript-specific macros.** Currently none. May be added if the generated Lean needs constructs Velvet doesn't provide.

The library depends on:
- Velvet (forked, which depends on Loom, which depends on mathlib)
- Z3 and cvc5 (downloaded by the lakefile)

Pre-built oleans are distributed so user projects skip compilation.

**Future: replacing Velvet with LemmaScript-native macros.** The Velvet fork is pragmatic for Phase 1. Long term, building our own Lean macros on Loom directly would give us: exact control over the generated proof state (no `WithName` surprises), TS-specific constructs (e.g., `break` with return value, for-of loops) without waiting on Velvet, error messages that reference TS source instead of Velvet internals, and independent evolution from Velvet's Dafny-oriented design. The fork gives us time to learn exactly which Velvet behaviors to keep.

---

## 11. Findings from Phase 0

Empirical constraints discovered during prototyping. They inform the design but should be re-validated.

### 11.1 Int vs Nat

- All TS `number` variables default to `Int` in Lean.
- Variables annotated `//@ type v nat` become `Nat`.
- Mixing Int and Nat in comparisons is fine — Lean coerces `Nat` to `Int`.
- Quantifier types must be consistent within a property: don't use `k : Int` in an invariant and `k : Nat` in the ensures for the same property.
- `arr.size` is `Nat`. No explicit `↑` coercion needed.
- Array indexing: `arr[i]!` for `Nat`, `arr[i.toNat]!` for `Int`.
- Recursive ghost functions on array indices should take `Nat`. Calling code should use `//@ type` for the index variable.
- Bridge lemmas (e.g., `(i + 1).toNat = i.toNat + 1`) may be needed in `.spec.lean` when mixing Int and Nat.

### 11.2 `loom_solve` Capabilities

- Discharges most VCs for array algorithms automatically.
- Handles all comparison directions (`≥`, `>`, `≤`, `<`).
- Needs ghost functions tagged `@[grind, loomAbstractionSimp]`.
- Recursive ghost functions may need explicit step lemmas with the same attributes.
- Cannot invent loop invariants. Missing or weak invariants produce unsolved goals.
- Cannot bridge `(i + 1).toNat` to `i.toNat + 1` without a lemma.

### 11.3 Velvet Specifics

- `method` syntax handles `require`, `ensures`, `invariant`, `done_with`, `decreasing`, `break`, mutable variables.
- `return` not supported inside loops — users restructure to `break` + result variable.
- `done_with` captures what is true when the loop exits (by condition or by break).
- `prove_correct` works across files (with our fork's persistence fix).
- `loom_solve!` shows unsolved goals for debugging.

### 11.4 Decreasing Clauses

- Lean accepts any well-founded relation: `Nat`, tuples (lexicographic), etc.
- `Nat` expressions work directly (e.g., `arr.size - i` where `i : Nat`).
- `Int` expressions need `.toNat` (e.g., `(hi - lo + 1).toNat`).
- Avoid mixing Nat and Int in subtraction: `(arr.size - i).toNat` where `i : Int` causes issues. Either make `i : Nat` or use `arr.size - i.toNat`.

---

## 12. What This Spec Does Not Cover (Future Work)

- **Compound pattern matching** — conditions like `state === "idle" && event.kind === "syn"` where both variables are data-carrying unions would need nested match or match on a tuple. Currently, compound conditions work only when both types have `DecidableEq` (enum-like).
- **Cross-file type imports** — types defined in a separate TS file and imported
- For-of loops, object types, higher-order functions, async/await
- Multiple functions per file with inter-function calls
- Array mutation (`arr[i] = v`)
- Error reporting (mapping Lean errors to TS source locations)
- VS Code extension
- LLM proof filling integration
- Pre-built olean distribution

---

## 13. Implementation Order

1. **Spec expression parser** — tokenizer, recursive descent, AST. Unit tested.
2. **Lean emitter** — AST → Lean string, using EmitContext for types. Unit tested.
3. **TS extractor** — ts-morph → IR. Tested on examples.
4. **Code generator** — IR → `.def.lean`. Tested by diffing against known-good output.
5. **`lsc` CLI** — wires extractor → codegen → Lake. Integration tested.
6. **Lean library** — re-exports Velvet fork + Loom. Verified by building examples.
7. **Project scaffolding** (`lsc init`).

Each step has clear inputs and outputs. Test at each boundary.
