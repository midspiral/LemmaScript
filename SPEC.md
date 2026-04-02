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
    binarySearch.types.lean      ← Lean types from TS (generated)
    binarySearch.spec.lean       ← ghost definitions, lemmas (user-written)
    binarySearch.def.lean        ← method definition (generated)
    binarySearch.proof.lean      ← prove_correct + tactics (user/LLM-written)
  lakefile.lean                  ← requires LemmaScript
  lean-toolchain
  package.json                   ← depends on @lemmascript/tools
```

### 2.1 The Four Lean Files

For each verified TS function `foo.ts`, there are up to four Lean files:

| File | Who writes it | Purpose |
|------|--------------|---------|
| `foo.types.lean` | `lsc gen` | Lean type definitions derived from TS types |
| `foo.spec.lean` | User | Ghost definitions, helper lemmas |
| `foo.def.lean` | `lsc gen` | Method definition (generated from TS) |
| `foo.proof.lean` | User / LLM | `prove_correct` with proof tactics |

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
| `done_with` | Before first statement of loop body | Post-loop condition (see §5.2) |
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
          | '{' (IDENT ':' expr ',')* IDENT ':' expr '}'
TYPE     := 'nat' | 'int'
```

**`\result`** refers to the function's return value (following Frama-C/ACSL convention). It is only valid in `ensures` annotations. The `\` prefix distinguishes it from any TS variable named `result`.

**`forall(k, P)`** quantifies `k` as `Int` by default. **`forall(k: nat, P)`** quantifies as `Nat`.

### 3.3 Type Annotations

`lsc` reads TS types from ts-morph and maps them to Lean (see §8). For `number` variables, the default mapping is `Int`. The `type` annotation overrides this to `Nat`:

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

The translation is purely syntactic. `lsc` does not infer types beyond what `//@ type` annotations provide.

### 4.1 Operator Mapping

| Spec | Lean |
|------|------|
| `===` / `==` | `=` |
| `!==` / `!=` | `≠` |
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
| `return f(a) + g(b)` (embedded calls) | `let _t0 ← f a`<br>`let _t1 ← g b`<br>`return _t0 + _t1` | Monadic lifting (selective ANF). See §4.4. |
| `Math.floor(e)` | `e` | Int division in Lean is already floor. |
| `s.indexOf(sub)` | `JSString.indexOf s sub` | Returns `Int` (-1 if not found). |
| `s.slice(start, end)` | `JSString.slice s start end` | Nat-indexed substring. |
| `s.length` | `s.length` | String length, `Nat`. |
| `arr.map((x) => e)` | `arr.map (fun x => e)` | Dot-notation dispatch. See §4.7. |
| `arr.filter((x) => e)` | `arr.filter (fun x => e)` | Dot-notation dispatch. |
| `arr.every((x) => e)` | `arr.all (fun x => e)` | TS `every` → Lean `all`. |
| `arr.some((x) => e)` | `arr.any (fun x => e)` | TS `some` → Lean `any`. |
| `[a, b, c]` | `#[a, b, c]` | Array literal (any length, including `[]` → `#[]`). |
| `{ ...obj, f: v }` | `{ obj with f := v }` | Functional record update. |
| `arr.with(i, v)` | `arr.set! i v` | Functional array update (ES2023). |
| `\result` | `res` | Only valid in `ensures`. |
| `"foo"` (string literal, enum context) | `.foo` | Constructor. Lean infers type from context. |
| `"foo"` (plain string context) | `"foo"` | String literal. Context-directed: user type → constructor, otherwise string. |
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

### 4.6 Monadic Lifting (Selective ANF)

When a Velvet method call appears embedded inside a larger expression (not at the top level of an assignment), the transform lifts it into a `let ← ` bind before the statement. This follows Lean's do-notation `←` desugaring rules (see Ullrich & de Moura, "'do' Unchained", 2022).

```typescript
return sumTo(arr, n - 1) + arr[n - 1];
```

generates:

```lean
let _t0 ← sumTo arr (n - 1)
return _t0 + arr[n - 1]!
```

**Rules:**
- Lift from arithmetic, comparisons, function arguments — left-to-right, depth-first
- `if` expressions: lift from the condition only, not from branches (branches are separate monadic blocks)
- Top-level method calls in assignments remain as direct binds (`x ← f a b`)
- Fresh names use the pattern `_t0`, `_t1`, etc.

Note: as in Lean's `←`, lifting from `&&`/`||` loses short-circuit semantics (both sides execute). This matches Lean's behavior.

### 4.7 Higher-Order Functions and Lambdas

Arrow functions extract as lambdas and emit as Lean's `fun` syntax:

```typescript
arr.map((x) => x * 2)    // → arr.map (fun x => x * 2)
arr.filter((x) => x > 0) // → arr.filter (fun x => x > 0)
arr.every((x) => x > 0)  // → arr.all (fun x => x > 0)
arr.some((x) => x < 0)   // → arr.any (fun x => x < 0)
```

Lambda bodies can be expressions (`(x) => x + 1`) or statement blocks (`(x) => { ... }`). Expression bodies emit as `(fun x => expr)`. Block bodies emit as `(fun x => do stmts)`.

Lambda parameter types are inferred by Lean (omitted from emission). Explicit TS type annotations are preserved if present.

**Monadic callbacks:** When the callback calls a Velvet method, the HOF call uses the monadic variant (e.g., `arr.mapM f`). Pure callbacks use the non-monadic variant (`arr.map f`). The transform checks the transformed lambda body for monadic binds (`←`) and selects the variant accordingly.

| Pure | Monadic | When |
|------|---------|------|
| `arr.map f` | `arr.mapM f` | callback calls a method |
| `arr.filter f` | `arr.filterM f` | callback calls a method |
| `arr.all f` | `arr.allM f` | callback calls a method |
| `arr.any f` | `arr.anyM f` | callback calls a method |

The monadic HOF call is itself monadic — it gets `←` at the call site via the existing monadic lifting mechanism. Purity classification accounts for this: functions that transitively call non-pure functions (including through lambda callbacks) are classified as non-pure via call-graph analysis (see §13).

**Proof note:** Velvet's WPGen does not currently have rules for `mapM`/`filterM`/etc. Proofs involving monadic HOFs require manual tactics.

### 4.8 Method Dispatch

Two strategies for translating `receiver.method(args)`:

1. **Remapped methods** (`METHOD_TABLE`): TS name → fully qualified Lean name, emitted as `leanFn receiver args`. Used when the Lean function lives in a separate module or has a different name. Example: `s.indexOf(sub)` → `JSString.indexOf s sub`.

2. **Dot-notation methods** (`DOT_METHODS`): TS name → Lean method name, emitted as `receiver.leanName args`. Lean resolves argument order via dot notation. Used for methods that exist directly on the Lean type.

| TS method | Lean method | Dispatch |
|-----------|-------------|----------|
| `s.indexOf(sub)` | `JSString.indexOf s sub` | Remapped |
| `s.slice(start, end)` | `JSString.slice s start end` | Remapped |
| `[a, b, c]` | `#[a, b, c]` | Array literal |
| `[...arr, e]` | `Array.push arr e` | Remapped |
| `arr.with(i, v)` | `arr.set! i v` | Dot-notation |
| `arr.map(f)` | `arr.map f` | Dot-notation |
| `arr.filter(f)` | `arr.filter f` | Dot-notation |
| `arr.every(f)` | `arr.all f` | Dot-notation |
| `arr.some(f)` | `arr.any f` | Dot-notation |
| `arr.includes(x)` | `arr.contains x` | Dot-notation |
| `arr.find(f)` | `arr.find? f` | Dot-notation |

The transform checks `METHOD_TABLE` first, then `DOT_METHODS`. If neither matches, it errors.

---

## 5. Statement Translation (TS → Lean)

### 5.1 Basic Statements

| TypeScript | Lean | Notes |
|-----------|------|-------|
| `let x = e` | `let mut x : T := e'` | Mutable. `T` from type map (§3.3). |
| `const x = e` | `let x := e'` | Immutable. No type annotation. |
| `x = e` | `x := e'` | Assignment. |
| `x += e`, `x -= e`, etc. | `x := x + e'` | Compound assignment (desugared). |
| `i++`, `++i`, `i--`, `--i` | `i := i + 1` / `i := i - 1` | Increment/decrement (desugared). |
| `return e` | `return e'` | Not supported inside loops — see §5.3. |
| `if (c) { ... }` | `if c' then ...` | |
| `if (c) { ... } else { ... }` | `if c' then ... else ...` | |
| `if (c) { ... } else if ...` | `if c' then ... else if ...` | Chained. |
| `while (c) { ... }` | `while c' invariant ... decreasing ... do ...` | See §5.2. |
| `x = f(a, b)` | `x ← f a b` | Velvet method call (monadic bind). |
| `break` | `break` | Only inside while loops. |
| `switch` / discriminant if-chain | `match` | See §5.4. |

All expressions `e` in the table above are translated using the spec expression rules (§4).

**Discriminant if-chains (data-carrying unions only):** When `lsc` encounters an if-else chain where each condition tests `x.discriminantField === "variant"` on a discriminated union with data fields, it emits a Lean `match` instead of `if`. This is necessary because Lean's `if` cannot bind constructor fields — only `match` can. For enum-like types (string-literal unions, no data), `if` stays `if` with `DecidableEq`. See §5.4 and §8.3.

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

**Decreasing clause:** Emitted directly as a Lean expression. Lean's termination checker accepts any type with a well-founded relation — `Nat`, lexicographic tuples `(a, b)`, etc. `lsc` does not add `.toNat` automatically; the user writes the decreasing expression in the form Lean expects.

**`done_with` clause:** If the loop body contains `break`, the user should add a `//@ done_with` annotation specifying what is true when the loop exits. (If omitted, Velvet defaults to the negation of the loop condition, which is only correct when there is no `break`.)

### 5.3 Return Inside Loops

`return` inside a `while` loop is **not supported**. Velvet does not support `return` inside loops, and `lsc` does not transform it. If `lsc` encounters `return` inside a loop, it emits an error.

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

The TypeScript is still valid and runs identically. The verified version uses `break` instead of `return`, which maps directly to Velvet's `break` construct. The user writes invariants about their own `result` variable — no magic.

### 5.4 Discriminant Dispatch → Match

Both `switch` on a discriminant and if-chains on a discriminant translate to Lean `match`. `lsc` detects the pattern: conditions of the form `x.field === "variant"` (or `x === "variant"` for enum-like types) on the same variable.

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

**Detection:** ts-morph provides the variable's type (discriminated union), the discriminant field name, and the variant field types. `lsc` uses this — no guessing.

**Field binding:** Property accesses on the matched variable (`pkt.seq`, `pkt.len`) become bound variables from the match pattern. Unused fields get `_`.

**Enum-like types** (string literal unions, no data fields) stay as `if` with `DecidableEq`. `lsc` does NOT convert them to `match`. `state === "idle"` → `state = .idle` (simple equality). Only discriminated unions with data fields trigger the if-chain → match transformation.

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

### 6.1 Pure Function Mirrors

For functions that are **pure** (no `while`, no mutable `let`), `lsc` also generates a plain Lean `def` in `foo.types.lean`, inside a `namespace Pure`:

```lean
namespace Pure

def foo (params...) : RetType :=
  -- same logic as the Velvet method, as a plain function

end Pure
```

This enables proofs by standard Lean induction over sequences of calls. The Velvet method is also generated, but as a thin wrapper: `return Pure.foo params`. This avoids termination issues (the pure `def` handles termination natively) while keeping the method callable from other Velvet methods via `←`.

Pure function detection: a function is pure if its body contains no `while` statements and no mutable `let` declarations, and it does not transitively call any non-pure function (determined via call-graph analysis in the resolve phase).

**Spec references:** In `//@ ensures`, `//@ requires`, and `//@ invariant` annotations, calls to pure functions are resolved as `Pure.fnName`. The resolve phase classifies these as `spec-pure` call kind, and the transform emits the qualified name. Calls to external Lean-defined spec helpers (e.g., `sumTo` in a hand-written `.spec.lean`) pass through unqualified.

**Proof note:** Since the method body is `return Pure.foo ...`, proofs need `unfold Pure.foo` before `loom_solve` to expose the logic.

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

`lsc` reads parameter and variable types from ts-morph. Primitive types are mapped per the table. User-defined types (like `State`, `Event`) are passed through by name — the corresponding Lean type is generated in `.types.lean`.

`//@ type v nat` overrides the primitive mapping for `number` variables:
- `//@ type i nat` — `number` → `Nat` instead of `Int`

Interface fields can also be overridden with a trailing annotation on the same line:

```typescript
export interface Model {
  memberCount: number; //@ type nat
  expenses: Expense[];
}
```

This generates `memberCount : Nat` instead of `memberCount : Int` in the Lean structure. No variable name is needed — the annotation applies to the field on the same line.

User-defined types (string literal unions, discriminated unions) are generated in `.types.lean` with the same name as the TS type. The TS name IS the Lean name — no renaming.

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

**If-chains on the discriminant → Lean `match`.**  When `lsc` encounters an if-else chain where each condition tests `x.field === "variant"` on the same variable, it emits a `match`. ts-morph provides the discriminant field name, variant types, and field names — no guessing.

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

### 8.5 Record/Object Types

TS interfaces and object types map to Lean structures.

```typescript
interface EffectState {
  res: boolean;
  done: boolean;
  rec: boolean;
}
```

Generated in `.types.lean`:

```lean
structure EffectState where
  res : Bool
  done : Bool
  rec : Bool
deriving Repr, Inhabited, DecidableEq
```

**Field access** passes through directly: `state.res` → `state.res` (Lean structures have field projection).

**Object literals** translate to anonymous constructors:

```typescript
return { res: true, done: true, rec: true };
```

→

```lean
return { res := true, done := true, rec := true }
```

**Spread update** translates to Lean's `with` syntax for functional record update:

```typescript
return { ...m, mood: newMood, baseHue: m.baseHue + delta };
```

→

```lean
return { m with mood := newMood, baseHue := m.baseHue + delta }
```

**Detection:** ts-morph identifies `interface` and `type` declarations that are pure object shapes (no union, no discriminant). These generate `structure` instead of `inductive`.

### 8.6 Type Mapping Implementation

Type mapping logic lives in `types.ts`, the single source of truth for both the resolve and transform phases.

The module provides:
- `parseTsType(tsType: string): Ty` — TS type string → structured `Ty` (used by resolve for type inference and by transform for type declarations)
- `tyToLean(ty: Ty): string` — `Ty` → Lean type string (the inverse of `parseTsType`)

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
- async/await
- Multiple functions per file with inter-function calls
- Array mutation (`arr[i] = v`)
- Error reporting (mapping Lean errors to TS source locations)
- VS Code extension
- LLM proof filling integration
- Pre-built olean distribution

---

## 13. Pipeline

The toolchain is a four-phase pipeline (see `TOOLS.md` for internal details):

```
extract (ts-morph → Raw IR) → resolve (→ Typed IR) → transform (→ Lean IR) → emit (→ text)
```

- **Extract**: ts-morph → structured AST. Body expressions are nodes, not strings. Annotations remain as strings.
- **Resolve**: attaches types, classifies calls, identifies discriminants, rejects unsupported patterns. Uses linked environments for lexical scoping. Computes purity via call-graph analysis: a function is pure if it is syntactically pure (no `while`/`for-of`/mutable `let`) AND does not transitively call any non-pure function.
- **Transform**: Typed IR → Lean IR. Pattern-matches on types. Desugars `for-of` to `while`. Detects discriminant if-chains → `match`. Lifts embedded method calls to `let ←` binds (selective ANF, §4.6).
- **Emit**: Lean IR → text. Trivial printer.

