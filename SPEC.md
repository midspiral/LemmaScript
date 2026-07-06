# LemmaScript — Implementation Specification

**Version:** 0.5.10
**Date:** July 2026

Backend-specific details:
- [SPEC_LEAN.md](SPEC_LEAN.md) — Lean backend (Velvet/Loom, four-file scheme, proof workflow)
- [SPEC_DAFNY.md](SPEC_DAFNY.md) — Dafny backend (two-file scheme, regen workflow)

---

## 1. Overview

LemmaScript is a verification toolchain for TypeScript. The user writes TypeScript with `//@ ` specification annotations. The toolchain generates formal verification artifacts; a backend prover (Lean or Dafny) checks them.

The toolchain has two components:
1. **`lsc` CLI** (Node.js) — parses TS, generates verification artifacts for the selected backend
2. **Backend-specific libraries** — Lean: LemmaScript Lean library (re-exports Velvet/Loom). Dafny: helper preambles auto-injected.

---

## 2. The `//@ ` Annotation Language

### 2.1 Annotation Kinds

Annotations are TypeScript comments of the form `//@ <keyword> <expression>`.

| Keyword | Placement | Meaning |
|---------|-----------|---------|
| `backend` | Top of file | Restrict file to a specific backend (see §2.6) |
| `safe-slice` | Top of file | Opt into JS-clamping semantics for two-arg `arr.slice(lo, hi)` (see §2.7) |
| `verify` | Before first statement of function/method body | Mark function for verification (see §2.5) |
| `requires` | Before first statement of function body | Precondition |
| `ensures` | Before first statement of function body | Postcondition (`\result` refers to return value) |
| `contract` | Before first statement of function body | Natural-language description of intent — prover-ignored; surfaced by `lsc extract` for vetting against the formal `requires`/`ensures` (see §2.13) |
| `invariant` | Before first statement of loop body | Loop invariant |
| `decreases` | Before first statement of loop or function body | Termination metric |
| `done_with` | Before first statement of loop body | Post-loop condition (see §5.2) |
| `type` | Before first statement of function body | Type override for a variable (see §2.4) |
| `ghost let x = e` | Before any statement | Ghost variable (proof-only, not runtime). See §2.3. |
| `ghost x = e` | Before any statement | Ghost variable reassignment. |
| `assert e` | Before any statement | Assertion (`assertGadget` in Lean, `assert` in Dafny). |
| `assume e` | Before any statement | Trusted assumption — emits `assume e;` in Dafny. Dafny backend only. See §2.3. |
| `pure` | Before function declaration | Force function to be pure — required to call from another function's `requires`/`ensures`. Dafny: `function by method` if body can't auto-convert (see §5.1). |
| `havoc` | Before a variable declaration | Nondeterministic value — skip init expression (see §2.9). |
| `havoc <key>` | Before a variable declaration | Nondeterministic subexpression — replace calls matching `<key>` (see §2.10). |
| `declare-type N { f: T, ... }` | Before any statement | Declare a record type for cross-file types (see §2.5). |
| `extern` | Before function declaration | Treat function as a body-less axiom — extract signature only, skip body (see §2.11). `//@ extern NS.method` registers it under a dotted name. |
| `autohavoc` | File-level, or before a `//@ verify` function | Abstract every unmodellable expression to a nondeterministic value, so verification rests only on declared contracts (see §2.12). Dafny only. |
| `skip` | Before any statement | Omit statement from verification model (for side-effect-only code). |

### 2.2 Spec Expression Grammar

The expression language is a subset of TypeScript with verification extensions.

```
expr     := iff
iff      := implies ('<==>' iff)?        // right-associative; binds loosest
implies  := or ('==>' implies)?          // right-associative
or       := and ('||' and)*
and      := compare ('&&' compare)*
compare  := add (cmpOp add)?
cmpOp    := '===' | '!==' | '>=' | '<=' | '>' | '<'
add      := mul (('+' | '-') mul)*
mul      := unary (('*' | '/' | '%') unary)*
unary    := '!' unary | '-' unary | postfix
postfix  := atom ('.' ident | '[' expr ']' | '(' args ')')*
cmpOp    := ... | 'in'                        // set/seq/map membership
atom     := NUMBER | HEX_NUMBER | IDENT | 'true' | 'false' | '\result'
          | 'forall' '(' IDENT (':' TYPE)? ',' expr ')'
          | 'exists' '(' IDENT (':' TYPE)? ',' expr ')'
          | 'perm' '(' expr ',' expr ')'        // permutation predicate (spec-only; Dafny backend)
          | '(' expr ')'
          | '[' (expr ',')* expr? ']'
          | '{' (IDENT ':' expr ',')* IDENT ':' expr '}'
TYPE     := IDENT                             // 'nat', 'int', 'string', user types
```

**`\result`** refers to the function's return value (following Frama-C/ACSL convention). It is only valid in `ensures` annotations. The `\` prefix distinguishes it from any TS variable named `result`.

**`forall(k, P)`** accepts an optional explicit type annotation, which may be **any** type — `forall(k: nat, …)`, `forall(s: string, …)`, `forall(x: MyType, …)`. When `k` is unannotated, its type is inferred: if `k` is used as a collection key or element (e.g., `map.has(k)`, `set.has(k)`, `arr.includes(k)`) → the collection's key/element type; otherwise `Int`/`int`. Same for `exists`.

**`perm(a, b)`** is a spec-only predicate holding iff arrays `a` and `b` are reorderings of each other (equal as multisets); both must be arrays of the same equality-supporting element type. It has no runtime counterpart, so it is rejected outside `//@` annotations. It lowers to Dafny's `multiset(a) == multiset(b)` (a transparent `Perm<T(==)>` predicate, so companion `.dfy` proofs can reason with `multiset` directly). **Dafny backend only** (`//@ backend dafny`). Canonical use: lifting a count's concatenation-homomorphism to permutation invariance. See [`examples/perm.ts`](examples/perm.ts).

### 2.3 Ghost Variables and Assertions

Ghost annotations introduce proof-only state that does not exist at runtime:

```typescript
//@ ghost let enqueued = new Set<string>()   // ghost variable declaration
//@ ghost enqueued = enqueued.add(id)        // ghost assignment
//@ assert !enqueued.has(id)                 // assertion
```

Ghost `let` declarations become mutable bindings in both backends (since they are typically reassigned). Ghost assignments become regular assignments. Assertions become `assertGadget` in Lean and `assert` in Dafny.

The init expression in `ghost let` supports `new Set<T>()` and `new Map<K,V>()` constructors, as well as any spec expression. An optional type annotation is supported: `//@ ghost let x: type = expr`.

**`//@ assume P`** is the trusted form of `//@ assert P` — emits `assume P;` in Dafny, not supported in the Lean backend. Canonical use is to constrain a `//@ havoc`'d value (see §2.10) inline in TS instead of post-hoc in the generated `.dfy` file.

### 2.4 Type Annotations

`lsc` reads TS types from ts-morph and maps them to the backend's type system. For `number` variables, the default mapping is `Int`/`int`. The `type` annotation overrides this to `Nat`/`nat`:

```
//@ type <varname> nat
```

Use `nat` for non-negative loop counters and array indices.

For generic functions that compare values with `===`, the Dafny backend needs an equality constraint on the type parameter. Annotate with:

```
//@ type T (==)
```

Example:
```typescript
export function linearSearch<T>(s: T[], x: T): number {
  //@ type T (==)
  let i = 0
  while (i < s.length) {
    if (s[i] === x) return i
    i = i + 1
  }
  return -1
}
```

This emits `method linearSearch<T(==)>(...)` in Dafny. Without it, Dafny rejects `==` on values of unconstrained type `T`.

Note: `arr.includes(x)` and `arr.indexOf(x)` are supported natively — no manual helpers needed. The compiler emits `(x in arr)` and `SeqIndexOf(arr, x)` respectively.

User-defined types (string literal unions, discriminated unions) are generated automatically with the same name as the TS type. No annotation needed or supported for these.

String-literal union members are emitted verbatim as backend constructor names — they must be valid identifiers in the target backend. Avoid operator characters like `"+"` or `"-"` (which Dafny rejects); use word names such as `"Add"`, `"Sub"` instead.

When a variable is Nat-typed:
- Lean: `arr[i]!` instead of `arr[i.toNat]!`
- Dafny: no difference (Dafny handles `nat` natively)
- Ghost function calls pass the variable directly

Type aliases can be overridden with a leading `//@ type <ty>` annotation. Use this when the declared TS type can't be modeled precisely — e.g. numeric-literal unions:

```typescript
//@ type nat
export type PresetMinutes = 5 | 15 | 30 | 45 | 60;
```

emits `type PresetMinutes = nat`. Any reference to `PresetMinutes` (parameters, fields, `PresetMinutes[]`) then resolves through the alias.

Interface fields can also be overridden with a trailing annotation on the same line:

```typescript
export interface Model {
  memberCount: number; //@ type nat
  expenses: Expense[];
}
```

### 2.5 Type Declarations: `//@ declare-type`

When imported types can't be resolved by ts-morph (e.g., in monorepos with bundler module resolution), declare them manually:

```typescript
//@ declare-type Box { x: number, y: number, x2: number, y2: number }
//@ declare-type Rect { x: number, y: number, width: number, height: number }
```

Each `declare-type` generates a Dafny `datatype` (or Lean `structure`) with the given fields. Field types use TS syntax (`number`, `string`, `boolean`, `T[]`, etc.) and are mapped through the standard type rules (§6.1).

Place `declare-type` annotations before the first function that uses the type. They can appear as leading comments on any statement. `declare-type` takes precedence over any type/interface of the same name in the source file, and is never filtered out by brownfield mode.

An **alias form** `//@ declare-type Name = TsType` declares `Name` as an alias for a TS type expression (e.g., `Ruleset = Rule[]`). Dotted references like `Namespace.Name` resolve via last-segment fallback, so `//@ declare-type Info { ... }` matches a reference to `Agent.Info`. Aliases whose target is structural (array/map/set/optional/another user type) are expanded at use sites; primitive-targeted aliases (`type TaskId = number`) stay nominal so the generated Dafny preserves the alias name.

### 2.6 Selective Verification: `//@ verify`

By default, `lsc` extracts and verifies every function in the file. In brownfield codebases where most functions are outside the supported fragment, add `//@ verify` to opt in individual functions:

```typescript
function isEmptyResult(result: string): boolean {
  //@ verify
  //@ ensures result.trim() === '' ==> \result === true
  if (!result) return true;
  const trimmed = result.trim();
  // ...
}
```

**Behavior:** If any function in the file has `//@ verify`, `lsc` switches to selective mode and only extracts functions marked with `//@ verify`. Functions without it are silently skipped. Type declarations, interface declarations, and module-level `const` declarations are always extracted (they may be needed by verified functions).

If no function in the file has `//@ verify`, all functions are extracted as before. This keeps existing LemmaScript projects (where every function is in-fragment) working without changes.

### 2.7 Backend Restriction: `//@ backend`

A file-level directive that restricts the file to a specific backend:

```typescript
//@ backend dafny
```

When `lsc` runs with a different backend (e.g., `--backend=lean`), the file is silently skipped. This is used for features only supported in one backend, such as class methods (Dafny only).

A second file-level directive, `//@ safe-slice`, opts the file into JS-clamping semantics for two-arg `arr.slice(lo, hi)`: the emitted Dafny goes through a `SafeSlice` helper that clamps both bounds to `[0, |s|]` rather than producing a direct `s[lo..hi]` (which Dafny requires `0 <= lo <= hi <= |s|`). Off by default — files that wrote `.slice` calls with provable bounds get direct emission. Files verifying production code that relies on JS's permissive slicing opt in with the directive at the top.

### 2.8 Classes

Class methods can be verified with `//@ verify`. The class fields become Dafny class fields, and `this.field` references work directly.

```typescript
export class Counter {
  private count: number;
  private max: number;

  increment(): number {
    //@ verify
    //@ requires this.count < this.max
    //@ ensures this.count <= this.max
    const old = this.count;
    this.count = this.count + 1;
    return old;
  }
}
```

generates (Dafny):

```dafny
class Counter {
  var count: int
  var max: int

  method increment() returns (res: int)
    requires (this.count < this.max)
    ensures (this.count <= this.max)
  {
    var old_ := this.count;
    this.count := (this.count + 1);
    return old_;
  }
}
```

**`modifies this` / `reads this`:** Not generated automatically. Add as proof-level additions in the `.dfy` file. Dafny will report an error if they're missing.

**Array-field mutation — length-preservation ensures:** When a method mutates an array-typed field via `this.arr[i] = v` (desugared to `this.arr = this.arr.with(i, v)`, emitted in Dafny as `this.arr := this.arr[i := v]`), `ensures` clauses that index into the field (e.g., `ensures this.arr[i] == v`) will fail Dafny's index-range check, because Dafny cannot automatically prove that the length was preserved across the modification. Add `ensures |this.arr| == old(|this.arr|)` to the `.dfy` file for each array field mutated this way. (An automated emission is not yet supported.)

**`old()` in ensures:** For mutating methods, `this.field` in `ensures` refers to the post-state. Use `old(this.field)` in the `.dfy` file to refer to the pre-state. (A `//@ old` spec expression is not yet supported.)

**Lean:** Class support is Dafny-only. Use `//@ backend dafny` on files with classes.

### 2.9 Cross-File Calls

A call to a symbol declared in another `.ts` file (resolved via ts-morph) is emitted as `function {:axiom} <flat>(...): T` — opaque, uninterpreted. Any `//@ requires` / `//@ ensures` on the source declaration are lifted onto the axiom so callers reason against the same contract the source verified; the lift is transitive through nested cross-file references. Only symbols *actually called* are externed; `.d.ts` declarations are skipped (covered by built-in dispatch, §3.8). No annotation is required.

### 2.10 Havoc: `//@ havoc`

Marks a variable declaration *or assignment* as nondeterministic — the RHS
expression is discarded and the target receives an arbitrary value of its
declared type:

```typescript
//@ havoc
const cleaned = text.replace(/[^a-z]/g, '');
// later in the same scope
//@ havoc
cleaned = cleaned.replace(/\s+/g, ' ');
```

generates (Dafny):

```dafny
var cleaned: string := *;
cleaned := *;
```

For assignments, the type is taken from the LHS variable (already declared);
`//@ havoc : Type` may still override. Only plain `x = e` is supported —
compound assigns (`x += e`), element assigns (`arr[i] = v`), and `x++` fall
through to normal extraction.

The verifier makes no assumptions about `cleaned`'s value. Code after the
havoc is verified for ALL possible values of the havoced variable.

#### Subexpression havoc: `//@ havoc <key>`

When a key is given, only calls whose function or method name matches the
key are replaced with a nondeterministic value. The rest of the expression
is preserved:

```typescript
//@ havoc encrypt
const msg = sign(encrypt(data, key), cert);
```

generates (Dafny):

```dafny
var _t0: EncryptedData := *;
var msg := sign(_t0, cert);
```

The `encrypt(...)` call is replaced with `*` (lifted to its own variable
since Dafny's `*` only appears in declaration/assignment positions), while
`sign(...)` is preserved and verified normally.

**Use case:** When a variable is initialized by an expression outside the
LS fragment (regex, JSON.parse, crypto, etc.), `//@ havoc` lets you skip
the unsupported expression while still verifying the logic that uses the
result. Properties that hold regardless of the havoced value are proved
sound.

**Backend support:** Havoc is supported in the Dafny backend only.

**Purity:** Functions containing havoced variables are classified as impure and emitted as Dafny `method`s (not `function`s), since Dafny's `*` is only valid in methods.

**Destructuring:** `//@ havoc` on a destructured declaration emits each named binding as a separate havoced variable. Types are inferred from the RHS when possible.

**Typed havoc:** `//@ havoc : Type` overrides the inferred type. For destructuring with multiple bindings, provide comma-separated types:

```typescript
//@ havoc : string, unknown
const { id: oldEdgeId, ...rest } = oldEdge;
// → var oldEdgeId: string := *;
// → var rest: int := *;
```

For single variables, `//@ havoc : EdgeBase | undefined` produces `Option<EdgeBase>`:

```typescript
//@ havoc : EdgeBase | undefined
const foundEdge = edges.find((e) => e.id === oldEdge.id) as EdgeType;
// → var foundEdge: Option<EdgeBase> := *;
```

**Axioms:** To constrain a havoced variable (e.g., `|cleaned| <= |text|`),
add a `//@ assume` immediately after the `//@ havoc` declaration. The
assume flows through to `.dfy.gen` and survives `lsc regen`.

### 2.11 Same-File Extern: `//@ extern`

Mark a function declaration as an opaque axiom — signature (with any `//@ requires` / `//@ ensures`) is extracted, body is skipped:

```typescript
//@ extern
export function match(str: string, pattern: string): boolean { ... }  // regex, out of model
```

→ Dafny: `function {:axiom} match_(str: string, pattern: string): bool`

Same machinery as cross-file auto-extern (§2.9): registered in the same externs map, lifted contract, name-escaped at emission so Dafny-keyword collisions (`match` → `match_`) resolve consistently. The difference from auto-extern is the trigger — cross-file fires automatically, in-file requires the explicit annotation.

**Use case:** the function is outside LS's model (regex, IO, parser) but callers should still verify *parametric over its behavior*. The axiom is deterministic and extensional, so proofs that depend on `f(x) == f(x)` go through. Unlike `//@ havoc`, which is nondeterministic at each call site and defeats determinism-dependent proofs.

In brownfield `//@ verify` mode (§2.6), `//@ extern` declarations are still extracted as externs; only their bodies are skipped.

Bare-name `//@ extern` calls are classified as pure (since they emit as `function {:axiom}`), so they are not lifted out of enclosing expressions by the method-call-lifting pass (§3.6). This means a bare-name extern call can appear inside a lambda body without producing a multi-statement lambda. Dotted externs (cross-file `NS.method` calls) go through a separate dispatch and are also pure.

**Dotted name.** Write `//@ extern fs.readFileSync` to give the extern a dotted name. A real `fs.readFileSync(...)` call in the code then resolves to this extern (§2.9) and is checked against its contract — so you can contract a library function directly, without writing a wrapper. Use a body-less `declare function` to carry the signature and the `//@ requires`/`//@ ensures`. (A function defined in the current file always wins over a same-named one in another file.)

### 2.12 Auto-havoc: `//@ autohavoc`

To verify a function, LemmaScript translates its whole body to the backend. That fails when the body mixes the property you care about (say, a path-traversal guard) with code that is out of model: framework I/O (`res.status()`, `req.query`), parsing (`JSON.parse`), env access (`process.env.X ?? y`), `uuidv4()`, anonymous object literals.

`//@ autohavoc` makes such a function verifiable by replacing each out-of-model expression with an arbitrary value of its type (a `//@ havoc`, §2.10). The verifier then assumes nothing about those values and checks only what remains — the control flow and the contracts of the functions called. So it proves the property while ignoring the surrounding plumbing. It is the complement of `//@ extern` (§2.11): `extern` gives an out-of-model function a contract to reason *against*; `autohavoc` discards out-of-model code *entirely*.

Enable it file-wide (a `//@ autohavoc` line at column 0) or on one function (next to its `//@ verify`). Dafny only (havoc is Dafny-only).

```typescript
app.get("/x", async (req, res) => {
  //@ verify
  //@ autohavoc
  const id: string = req.query.id;                       // out of model → arbitrary string
  const filePath = "./data/" + id + ".json";
  if (!validPath(filePath)) return res.status(400);      // guard: kept and checked
  return res.status(200).send(readFileSafe(filePath));   // readFileSafe contracted; its requires checked
});
```

Here `req.query.id` and the `res.status(...).send(...)` calls are havoc'd away; the one thing verified is that `validPath` guards the contracted `readFileSafe` call.

Three properties make this safe and useful:

- **It cannot hide a failure.** Havoc over-approximates — the verifier considers *every* value an abstracted expression could take — so a proof can only *fail* under autohavoc, never spuriously pass. (The pass only havocs; it never `assume`s.)
- **Contracts are still enforced.** A call to a function or extern with a `//@ requires` (a *sink*) is never discarded, even inside a havoc'd expression: it is pulled out to a `var _ := sink(...)` statement so its precondition is still checked, at any nesting depth.
- **Discarded calls are reported**, so a sink you forgot to contract can't vanish silently. The pass prints every out-of-model call it abstracted — `autohavoc: get_x abstracts 2 external call(s) — confirm none is an unguarded sink: JSON.parse, uuidv4` — where a raw `fs.readFileSync` on a user path would show up for review.

**Trust boundary:** the guarantee is "every *contracted* sink is reached only under its guard," not "every dangerous call is contracted." An out-of-model call with no contract is havoc'd (and reported); giving it a contract (§2.11) brings it under verification.

### 2.13 Informal Contracts: `//@ contract`

`//@ contract <text>` attaches a plain-English description of what a function is *meant* to do, beside its formal `//@ requires`/`//@ ensures`:

```ts
//@ contract Clamps x into the inclusive range [lo, hi]; the result never falls outside it.
//@ requires lo <= hi
//@ ensures \result >= lo && \result <= hi
export function clamp(x: number, lo: number, hi: number): number { ... }
```

The text is natural language, not a spec expression: the provers ignore it entirely (it never reaches the generated Dafny or Lean). `lsc extract` surfaces it per function in the Raw IR (`RawFunction.contract`); multiple `//@ contract` lines are collected in order, like `//@ requires`. Its purpose is to catch the gap between *intent* and *proof* — a spec can be verified yet guarantee less, or other, than the prose claims. The external [`lemmascript-claimcheck`](https://github.com/midspiral/lemmascript-claimcheck) tool checks `//@ contract` against the formal `//@ ensures` by an LLM round-trip.

---

## 3. Spec Expression Translation

The translation is purely syntactic. `lsc` does not infer types beyond what `//@ type` annotations provide.

### 3.1 Operator Mapping

| Spec | Lean | Dafny |
|------|------|-------|
| `===` / `==` | `=` | `==` |
| `!==` / `!=` | `≠` | `!=` |
| `>=` | `≥` | `>=` |
| `<=` | `≤` | `<=` |
| `>`, `<` | `>`, `<` | `>`, `<` |
| `&&` | `∧` | `&&` |
| `\|\|` | `∨` | `\|\|` |
| `!` | `¬` | `!` |
| `==>` | `→` | `==>` |
| `<==>` | `↔` | `<==>` |
| `+`, `-`, `*`, `/`, `%` | `+`, `-`, `*`, `/`, `%` | `+`, `-`, `*`, `/`, `%` |

No normalization of operators. Both backends handle all comparison directions.

**Truthiness coercion:** `!expr` is translated based on the operand's type:
- `string`: `!s` → `s == ""` (empty string is falsy)
- `optional`: `!opt` → match on None (undefined is falsy)
- `bool`: `!b` → `¬b` (standard negation)

`!!expr` works naturally: the inner `!` coerces to bool, the outer `!` negates.

The same coercion applies to non-bool conditions in `if`/`while`/`?:` positions: `n` (number) → `n > 0`, `xs` (array) → `|xs| > 0`, `s` (string) → `|s| > 0`. Optional conditions are handled separately (see Optional narrowing).

### 3.2 Special Forms

| Spec / TS | Lean | Dafny |
|-----------|------|-------|
| `arr.length` | `arr.size` | `\|arr\|` |
| `arr[e]` (Nat index) | `arr[e]!` | `arr[e]` |
| `arr[e]` (Int index) | `arr[e.toNat]!` | `arr[e]` |
| `f(a, b)` | `f a b` | `f(a, b)` |
| `x = f(a, b)` (method call) | `x ← f a b` | `x := f(a, b);` |
| `Math.floor(a / b)` | `a / b` (Lean int div floors) | `JSFloorDiv(a, b)` |
| `Math.floor(x)` (real arg) | — | `FloorReal(x)` → `x.Floor` |
| `Math.ceil(x)` (real arg) | — | `CeilReal(x)` → `x.Floor + 1` if non-integer |
| `Math.floor(n)` (int arg) | identity | identity |
| `Math.ceil(n)` (int arg) | identity | identity |
| `Math.abs(x)` | `MathAbs(x)` | `MathAbs(x)` (preamble: `if x >= 0 then x else -x`) |
| `Math.min(a, b)` | `MathMin(a, b)` | `MathMin(a, b)` (preamble: `if a <= b then a else b`) |
| `Math.max(a, b)` | `MathMax(a, b)` | `MathMax(a, b)` (preamble: `if a >= b then a else b`) |
| `c ? a : b` | `if c then a else b` | `if c then a else b` |
| `opt ? f(opt) : undefined` | match on Some/None | `match opt { case Some(v) => Some(f(v)) case None => None }` |
| `s.indexOf(sub)` | `JSString.indexOf s sub` | `StringIndexOf(s, sub)` |
| `s.indexOf(sub, from)` | — | `StringIndexOfFrom(s, sub, from)` (negative `from` clamps to 0) |
| `s.slice(start, end)` | `JSString.slice s start end` | `s[start..end]` |
| `s.substring(start)` / `s.substring(start, end)` | — | `s[start..]` / `s[start..end]` |
| `s.charCodeAt(i)` | — | `(s[i] as int)` |
| `s.trim()` | — | `StringTrim(s)` |
| `s.trimEnd()` / `s.trimStart()` | — | `StringTrimRight(s)` / `StringTrimLeft(s)` |
| `s.split(d)` (requires `\|d\| > 0`) | — | `StringSplit(s, d)` (axiomatic preamble: `1 <= \|res\| <= \|s\| + 1`) |
| `s.toLowerCase()` | — | `StringToLower(s)` |
| `s.toUpperCase()` | — | `StringToUpper(s)` |
| `s.includes(sub)` | — | `StringIndexOf(s, sub) >= 0` |
| `s.startsWith(p)` | — | `\|s\| >= \|p\| && s[..\|p\|] == p` |
| `s.endsWith(p)` | — | `\|s\| >= \|p\| && s[\|s\|-\|p\|..] == p` |
| `s.length` | `s.length` | `\|s\|` |
| `Math.max(...s)` / `Math.min(...s)` | — | `MaxOfSeq(s)` / `MinOfSeq(s)` (requires `\|s\| > 0`) |
| `perm(a, b)` (spec-only) | — | `Perm(a, b)` (preamble: `predicate Perm<T(==)>(a, b) { multiset(a) == multiset(b) }`) |
| `arr.map((x) => e)` | `arr.map (fun x => e)` | `Std.Collections.Seq.Map((x) => e, arr)` |
| `arr.filter((x) => e)` | `arr.filter (fun x => e)` | `Std.Collections.Seq.Filter((x) => e, arr)` |
| `arr.every((x) => e)` | `arr.all (fun x => e)` | `Std.Collections.Seq.All(arr, (x) => e)` |
| `arr.some((x) => e)` | `arr.any (fun x => e)` | `exists x :: x in arr && e` |
| `arr.includes(x)` | `arr.contains x` | `(x in arr)` |
| `arr.indexOf(x)` | — | `SeqIndexOf(arr, x)` (preamble) |
| `arr.find((x) => e)` | `arr.find? (fun x => e)` | — |
| `arr.findIndex((x) => e)` | — | `SeqFindIndex(arr, (x) => e)` (preamble: `-1 ⇔ no match`, `≥0 ⇔ first match with no earlier match`) |
| `arr.findLast((x) => e)` | — | `SeqFindLast(arr, (x) => e)` (preamble) |
| `arr.flat()` | — | `SeqFlatten(arr)` (preamble) |
| `arr.join(sep)` | — | `SeqJoin(arr, sep)` (preamble) |
| `arr.shift()` | — | `arr[0]` + `arr := arr[1..]` |
| `arr.pop()` | — | `(if \|arr\|>0 then Some(arr[\|arr\|-1]) else None)` + `arr := (if \|arr\|>0 then arr[..\|arr\|-1] else arr)` |
| `arr.unshift(e)` | — | `([e] + arr)` (mutating → reassignment) |
| `arr.sort(cmp)` | — | `SeqSortBy(arr, cmp)` (preamble axiom: permutation + length-preserving + sorted; mutating; `requires` cmp a total preorder) |
| `arr.slice(start)` | — | `arr[start..]` |
| `arr.slice(start, end)` | — | `arr[start..end]` |
| `expr!` (non-null) | unwrap Option | unwrap Option / direct map access |
| `expr \|\| default` (on optional) | match Some/None | `match { Some(v) => v, None => default }` |
| `expr \|\| undefined` (on optional) | identity | identity (no-op) |
| `expr \|\| default` (on string/array) | if non-empty | `if \|expr\| > 0 then expr else default` |
| `expr?.method(args)` | — | `if key in map { ... }` |
| `expr as T` | stripped | stripped |
| `null` | `none` | `None` (same as `undefined`) |
| `//@ skip` (before statement) | — | statement omitted from model |
| `new Map(arr.map(fn))` | — | loop building `map[]` |
| `[a, b, c]` | `#[a, b, c]` | `[a, b, c]` |
| `[...arr, e]` | `Array.push arr e` | `(arr + [e])` |
| `[a, ...b, c]` | `[a] + b + [c]` | `([a] + b + [c])` (general spread) |
| `arr.concat(other)` (T[] arg) | `arr ++ other` | `(arr + other)` |
| `arr.concat(elem)` (T arg) | `Array.push arr elem` | `(arr + [elem])` |
| `{ ...obj, f: v }` | `{ obj with f := v }` | `obj.(f := v)` |
| `{ ...map, [k]: v }` | — | `map[k := v]` (desugared to `.set()` in extract) |
| `{ [k]: v }` | — | `map[][k := v]` (desugared to `{}.set()` in extract) |
| `const { [k]: _, ...rest } = map` | — | `var rest := (map k' \| k' in map && k' != k :: map[k'])` (desugared to `.delete()` in extract) |
| `const [a, , c, ...rest] = arr` | — | `var a := arr[0]; var c := arr[2]; var rest := arr[3..]` (omits skipped, rest emits as slice) |
| `arr.with(i, v)` | `arr.set! i v` | `arr[i := v]` |
| `` `${a}/${b}` `` (template literal) | `toString a ++ "/" ++ toString b` | `IntToString(a) + "/" + IntToString(b)` |
| `{ k1: v1, ... }: Record<K,V>` | — | `map["k1" := v1, ...]` |
| `new Map<K,V>()` | `Std.HashMap.empty` | `map[]` |
| `Object.fromEntries(m)` | identity | identity |
| `m.get(k)` (in code) | `m.get? k` | `if k in m then Some(m[k]) else None` |
| `m.get(k)` (in spec) | `m.get! k` | `m[k]` |
| `m.set(k, v)` | `m := m.insert k v` | `m := m[k := v]` |
| `m.has(k)` | `m.contains k` | `(k in m)` |
| `m.delete(k)` | `m := m.erase k` | `m := (map k' \| k' in m && k' != k :: m[k'])` |
| `m.size` | `m.size` | `\|m\|` |
| `new Set<T>()` | `Std.HashSet.empty` | `{}` |
| `new Set(arr)` | `Std.HashSet.ofList arr.toList` | `(set x \| x in arr)` |
| `s.has(x)` | `s.contains x` | `(x in s)` |
| `x in S` | `x ∈ S` | `(x in S)` |
| `s.add(x)` | `s := s.insert x` | `s := (s + {x})` |
| `s.delete(x)` | `s := s.erase x` | `s := (s - {x})` |
| `s.size` | `s.size` | `\|s\|` |
| `for (const x of s)` | `.toArray` + for-in | `SetToSeq` + while |
| `for (const [k, v] of Object.entries(m))` | `.toArray` + for-in | `SetToSeq(m.Keys)` + while |
| `for (const v of Object.values(m))` | `.toArray` + for-in | `SetToSeq(m.Keys)` + while |
| `v !== undefined` | `if h : v.isSome then ... else ...` | `match v { case Some(...) => ... }` |
| `\result` | `res` | `res` |
| `"foo"` (enum context) | `.foo` | `Type.foo` |
| `"foo"` (string context) | `"foo"` | `"foo"` |
| `x.tag === "foo"` | `match` arm | `x.foo?` |
| `forall(k, P)` | `∀ k : T, P'` | `forall k :: P'` |
| `exists(k, P)` | `∃ k : T, P'` | `exists k :: P'` |

### 3.3 Nat-Typing Rules

An expression is Nat-typed if:
- It's a variable declared with `//@ type <v> nat`
- It's a quantified variable with `: nat` in the quantifier
- It's `arr.length` (i.e., `arr.size` / `|arr|`)
- It's an arithmetic expression where both operands are Nat-typed
- It's a non-negative numeric literal

The Nat-typing determines whether `.toNat` is needed for array indexing in Lean. Dafny handles `nat` natively.

### 3.4 Implication Flattening

`(A && B) ==> C` is emitted as curried implication: `A → B → C` (Lean) or `A ==> B ==> C` (Dafny).

### 3.5 Conjunction Splitting

Top-level `&&` in `requires`, `ensures`, and `invariant` annotations is split into separate clauses:

```
//@ ensures \result >= -1 && \result < arr.length
```

generates (Lean):

```lean
ensures res ≥ -1
ensures res < arr.size
```

generates (Dafny):

```dafny
  ensures res >= -1
  ensures res < |arr|
```

### 3.6 Method-Call Lifting

When a method call appears embedded inside a larger expression (not at the top level of an assignment), the transform lifts it into a separate statement before the enclosing statement. This is needed because method calls are statements in both target languages — they cannot appear inline in expressions.

```typescript
return sumTo(arr, n - 1) + arr[n - 1];
```

generates (Lean):

```lean
let _t0 ← sumTo arr (n - 1)
return _t0 + arr[n - 1]!
```

generates (Dafny):

```dafny
var _t0 := sumTo(arr, n - 1);
return _t0 + arr[n - 1];
```

**Rules:**
- Lift from arithmetic, comparisons, function arguments — left-to-right, depth-first
- `if` expressions: lift from the condition only, not from branches (branches are separate blocks)
- Top-level method calls in assignments remain as direct binds
- Fresh names use the pattern `_t0`, `_t1`, etc.

Note: lifting from `&&`/`||` loses short-circuit semantics (both sides execute). This matches Lean's behavior and is acceptable for verification.

In Lean, lifted calls use monadic `←` binds with specific WPGen semantics. See [SPEC_LEAN.md §2](SPEC_LEAN.md) for details.

### 3.7 Higher-Order Functions and Lambdas

Arrow functions extract as lambdas:

```typescript
arr.map((x) => x * 2)    // → Lean: arr.map (fun x => x * 2)
arr.filter((x) => x > 0) // → Lean: arr.filter (fun x => x > 0)
arr.every((x) => x > 0)  // → Lean: arr.all (fun x => x > 0)
arr.some((x) => x < 0)   // → Lean: arr.any (fun x => x < 0)
```

Lambda bodies can be expressions (`(x) => x + 1`) or statement blocks (`(x) => { ... }`). A block body is flattened to a single expression when its control flow allows — `if`/`let`/`return` shapes and a `switch` (lowered to a `match`-expression); bodies that can't reduce (loops, bare side effects) stay as statements, which the Dafny backend rejects (its lambdas are expression-only). A record literal returned from a callback is typed by the callback's return annotation, so `(x): Out => ({ ... })` constructs `Out(...)`, not an anonymous tuple.

**filterMap.** `xs.map(x => ... | undefined).filter((x): x is T => x !== undefined)` drops the `undefined`s *and* unwraps to `seq<T>` — lowered to the proven `SeqFilterSome` preamble (a plain `Map(.value, Filter(.Some?, ...))` wouldn't verify, since `.value` is partial).

**Monadic callbacks (Lean):** When the callback calls a method, the HOF call uses the monadic variant (e.g., `arr.mapM f`). Pure callbacks use the non-monadic variant (`arr.map f`). The transform checks the transformed lambda body for monadic binds and selects the variant accordingly.

| Pure | Monadic | When |
|------|---------|------|
| `arr.map f` | `arr.mapM f` | callback calls a method |
| `arr.filter f` | `arr.filterM f` | callback calls a method |
| `arr.all f` | `arr.allM f` | callback calls a method |
| `arr.any f` | `arr.anyM f` | callback calls a method |

**Pure calls in lambdas (Lean):** Inside lambda bodies, calls to pure same-file functions are classified as `spec-pure` (emitted as `Pure.fnName`, no `←`). This keeps the lambda pure so it can be passed to non-monadic HOFs.

### 3.8 Method Dispatch

The transform uses two strategies for translating `receiver.method(args)`:

1. **Helper-function methods**: TS name → semantic function name, emitted as `fn(receiver, args)`. Used when the target language function has a different calling convention. Example: `s.indexOf(sub)` → `stringIndexOf`.

2. **Dot-notation methods**: TS name → semantic method name, emitted as `receiver.method(args)` (preserving dot syntax). Each emitter maps the semantic name to its backend syntax.

| TS method | Semantic name | Lean | Dafny |
|-----------|--------------|------|-------|
| `s.indexOf(sub)` | `stringIndexOf` | `JSString.indexOf s sub` | `StringIndexOf(s, sub)` |
| `s.slice(start, end)` | `stringSlice` | `JSString.slice s start end` | `s[start..end]` |
| `[...arr, e]` | `arrayPush` | `Array.push arr e` | `(arr + [e])` |
| `arr.with(i, v)` | `arraySet` | `arr.set! i v` | `arr[i := v]` |
| `arr.map(f)` | `map` | `arr.map f` | `Std.Collections.Seq.Map(f, arr)` |
| `arr.filter(f)` | `filter` | `arr.filter f` | `Std.Collections.Seq.Filter(f, arr)` |
| `arr.every(f)` | `every` | `arr.all f` | `Std.Collections.Seq.All(arr, f)` |
| `arr.some(f)` | `some` | `arr.any f` | `exists x :: x in arr && ...` |
| `arr.includes(x)` | `includes` | `arr.contains x` | `(x in arr)` |
| `arr.indexOf(x)` | `indexOf` | — | `SeqIndexOf(arr, x)` |
| `arr.find(f)` | `find` | `arr.find? f` | — |
| `m.get(k)` | `mapGet` | `m.get? k` | `if k in m then Some(m[k]) else None` |
| `m.has(k)` | `mapHas` | `m.contains k` | `(k in m)` |
| `m.set(k, v)` | `mapSet` | `m.insert k v` | `m[k := v]` |
| `m.delete(k)` | `mapDelete` | `m.erase k` | `(map k' \| k' in m && k' != k :: m[k'])` |
| `s.has(x)` | `setHas` | `s.contains x` | `(x in s)` |
| `s.add(x)` | `setAdd` | `s.insert x` | `(s + {x})` |
| `s.delete(x)` | `setDelete` | `s.erase x` | `(s - {x})` |

The transform checks helper-function methods first, then dot-notation methods. If neither matches, it errors.

### 3.9 Map, Set, and Optional Narrowing

**Map vs Record runtime mismatch.** In both backends, `Record<K,V>` and `Map<K,V>` map to the same type (`map<K,V>` in Dafny, `HashMap` in Lean). But at JavaScript runtime they are different: `Record` is a plain object (`Object.keys` works, bracket access works) while `Map` is a Map instance (`Object.keys` returns `[]`, bracket access returns `undefined`). Code that builds a `Map` with `new Map()` + `.set()` and returns it as a `Record` will verify in Dafny but fail at runtime — the caller receives a Map where it expects a plain object.

**Fix:** When returning a `Map` as a `Record`, wrap with `Object.fromEntries(result)`. LemmaScript strips `Object.fromEntries()` during extraction (identity — Map and Record are the same type in the backend), but at runtime it converts the Map to a plain object. This is necessary whenever a function uses the `new Map()` + `.set()` pattern to build a Record result.

**Map and Set** (`Map<K,V>`, `Set<T>`) are immutable types in both backends. `const` declarations of collection types are automatically promoted to mutable bindings, since TS mutates in place but the backends require reassignment.

Mutating calls (`m.set(k, v)`, `s.add(x)`, `s.delete(x)`) are transformed into reassignments:
```typescript
inDegree.set(id, 0);    // → Lean: inDegree := inDegree.insert id 0
                          // → Dafny: inDegree := inDegree[id := 0];
enqueued.add(id);        // → Lean: enqueued := enqueued.insert id
                          // → Dafny: enqueued := (enqueued + {id});
```

**`Map.get` returns `Option`** in code context (since the key may not exist). In spec context (annotations), `map.get(k)` emits direct access without an Option wrapper, matching how specs reason about map contents.

**Optional narrowing.** All these patterns narrow the optional to its inner type in the appropriate scope:

- Equality: `v !== undefined`, `v === undefined` (early return)
- Truthiness: `if (v)`, `if (!v)`, `opt ? a : b`
- Composition: `v && rest` or `rest && v` (optional check on either side) — in an `if`/`?:` condition or as a bare statement (`v !== undefined && v.f()`, the `if`-less guard idiom); `a === undefined || b === undefined`
- Spec implication: `path !== undefined && rest ==> B` (premise narrows conclusion)
- Optional chaining: `obj?.field`, `obj?.foo()`, `obj?.[i]`, chained `obj?.a?.b?.c` and `obj?.a.b.c`
- Nullish coalescing: `x ?? default`; array index `arr[i] ?? default` (undefined ⟺ out of bounds under `noUncheckedIndexedAccess`) → `(0 <= i && i < arr.length) ? arr[i] : default`

The narrow pass (`narrow.ts`) detects these on the typed IR and rewrites them into a single `someMatch` IR node with a fresh binder. Transform lowers `someMatch` into Dafny `match` Some/None (or `if .Some? { ... .value ... }` after the peephole pass).

Following TS, the equality/truthiness/`&&`/`||`/`==>` patterns fire only for pure access paths (`x`, `obj.field`, `a.b.c.d`); method-call results must be bound first (`const v = m.get(k); if (v !== undefined) ...`). The `obj?.<chain>` and `x ?? d` forms are exceptions: extract emits dedicated single-evaluation IR nodes (`optChain`, `nullish`), so any expression on the left is allowed.

**Discriminated-union narrowing.** `if (e.kind === "lit") use(e.val)`, `if ('field' in x) use(x.field)`, and `if (x.kind !== "v") return; rest` all lower to `match` constructs that destructure variant-specific fields. Switch on a discriminator works similarly. Detection lives in `narrow.ts` alongside optional-narrowing rules (rewrites to a `tagMatch` IR node); the lowering to backend `match` lives in `transform.ts`.

**Synthesized array-union narrowing.** A plain union `U | T[]` (no shared discriminant) is synthesized at the boundary into a tagged datatype `ArrayBranch(arr: T[]) | NonArrayBranch(val: U)`. `Array.isArray(x)` narrows to the array branch (in `if` / `?:` / `==>`); when the non-array branch `U` is `string`, `typeof x === "string"` narrows to it in `?:` conditionals — the dual discriminator. Inside the matched branch, bare references to `x` use the variant's payload. The `typeof` form fires only when `U` is actually `string`; for any other `U` the runtime `"string"` test can't match that branch, so `lsc` does not narrow (and `typeof` stays unsupported).

See [TOOLS.md](TOOLS.md#narrow-rules) for the full rule list.

**Peephole simplification of `Map.get` ceremony.** The transform produces verbose-looking output for common `Map.get` consumer patterns — the call lowers to `(if k in m then Some(m[k]) else None)` followed by a match. A peephole pass between transform and emit collapses these into idiomatic backend code. See [TOOLS.md](TOOLS.md#peephole-rules) for the full rule list.

The pass takes the target backend as input. The Map.get rules apply to both backends. Boolean-simplification rules (collapsing `if c then b else false → c && b` etc.) are applied only for Dafny — they emit `∧`/`∨` in the IR which renders as Bool short-circuit operators in Dafny but as Prop disjunction in Lean, breaking structural-termination analysis for recursive functions. For Lean we keep the original if-then-else, which preserves the conditional that the termination checker needs.

The user-visible effect:
```typescript
// TS source
if (m.get(k) === 0) { ... }
```
```dafny
// Without peephole
if (match (if k in m then Some(m[k]) else None) {
      case Some(v) => v == 0
      case None => false
    }) { ... }

// With peephole (current behavior)
if (k in m && m[k] == 0) { ... }
```

The let-collapse rules apply when the partial result is bound to a local that's only used as the match scrutinee:
```typescript
// TS source
const lane = m.tasks[listId];
if (lane === undefined) return false;
return process(lane);
```
```dafny
// Output (peephole'd)
if (listId in m.tasks) {
  var lane := m.tasks[listId];
  return process(lane);
} else {
  return false;
}
```

The unwrapped value is bound once via a `var` (or `let` expression in pure contexts), preserving the source binding's name and capture semantics. Substituting `m.tasks[listId]` at every use would re-evaluate the access — incorrect if the body mutates `m`.

When the bound variable IS used after the match, the `let` is preserved and the `Option` value remains; only the inline match-on-`get` form is simplified.

**Quantifier type inference:** When a quantifier variable is used as a collection key or element (e.g., `forall(k, map.has(k) ==> ...)`, `forall(v, arr.includes(v) ==> ...)`), the variable type is inferred from the collection's key/element type instead of defaulting to `Int`.

**Set iteration:** `for (const x of s)` where `s` is a `Set<T>` converts the set to an array first (Lean: `.toArray`, Dafny: `SetToSeq` helper), then iterates with a standard indexed loop.

**Map/Record iteration via `Object.entries`:** `for (const [k, v] of Object.entries(map))` where `map` has type `Map<K,V>` or `Record<K,V>` desugars to iterating over `map.Keys` (via `SetToSeq`), with `k` bound to each key and `v` bound to `map[k]`. The `Object.entries()` wrapper is required because `for...of` on plain objects is not valid TypeScript or JavaScript — `Record<K,V>` is a plain object at runtime and does not have a `[Symbol.iterator]()` method. Similarly, `for (const v of Object.values(map))` desugars to the same key-iteration pattern, binding only the values. General destructuring in for-of (e.g., `for (const [a, b, c] of tuples)`) binds each name to `elem[0]`, `elem[1]`, etc.

---

## 4. Statement Translation

### 4.1 Basic Statements

| TypeScript | Lean | Dafny |
|-----------|------|-------|
| `let x = e` | `let mut x : T := e'` | `var x := e';` |
| `const x = e` | `let x := e'` | `var x := e';` |
| `x = e` | `x := e'` | `x := e';` |
| `arr[i] = v` (desugared to `arr = arr.with(i, v)`) | `arr := arr.set! i v` | `arr := arr[i := v];` |
| `x += e`, `x -= e`, etc. | `x := x + e'` | `x := x + e';` |
| `i++`, `++i`, `i--`, `--i` | `i := i + 1` / `i := i - 1` | `i := i + 1;` / `i := i - 1;` |
| `return e` | `return e'` | `return e';` |
| `if (c) { ... }` | `if c' then ...` | `if c' { ... }` |
| `if (c) { ... } else { ... }` | `if c' then ... else ...` | `if c' { ... } else { ... }` |
| `while (c) { ... }` | `while c' invariant ... do ...` | `while c' invariant ... { ... }` |
| `x = f(a, b)` (method call) | `x ← f a b` | `x := f(a, b);` |
| `break` | `break` | `break;` |
| `throw new Error(...)` | — | `assert false;` |
| `switch` / discriminant if-chain | `match` | `match` |

All expressions `e` above are translated using the spec expression rules (§3).

**`const` collections:** `const` declarations of Array, Map, or Set types become mutable bindings in both backends, since TS mutates these in place but the backends require reassignment.

**Uninitialized `let`:** `let x: T;` (no initializer) emits a type-appropriate default — `[]` for `T[]`, `map[]`/`{}` for `Map`/`Set`, `None` for `T | undefined` (and `null | T`), `0`/`false`/`""` for primitives. Other types fall through to Dafny's `default`, which won't compile — initialize at the declaration or annotate with `T | undefined`.

**For-of loops** are desugared to indexed loops: `for idx in [:bound]` (Lean) or `while idx < bound` (Dafny) with an auto-generated index variable `_varName_idx`. A bound invariant `_varName_idx ≤ bound` is automatically prepended to the user's invariants. When multiple for-of loops use the same variable name, the index is disambiguated with a suffix: `_id_idx`, `_id_idx2`, etc.

### 4.2 While Loops

```typescript
while (condition) {
  //@ invariant P
  //@ invariant Q
  //@ decreases D
  body
}
```

generates (Lean):

```lean
while condition'
  invariant P'
  invariant Q'
  decreasing D'
do
  body'
```

generates (Dafny):

```dafny
while condition'
  invariant P'
  invariant Q'
  decreases D'
{
  body'
}
```

**Decreasing clause:** Emitted directly as a backend expression. Both backends accept well-founded relations — `Nat`/`nat`, lexicographic tuples, etc.

**`done_with` clause:** If the loop body contains `break`, the user should add a `//@ done_with` annotation specifying what is true when the loop exits. (Lean: if omitted, Velvet defaults to the negation of the loop condition, which is only correct when there is no `break`. Dafny: not needed, the verifier handles break paths automatically.)

**C-style `for (init; cond; update)` loops** are desugared at extract time to the equivalent `init; while (cond) { body; update; }`. The loop variable from `init` is forced mutable so the update can mutate it. The update is a bare `Expression` in TS (not wrapped in an `ExpressionStatement`), but is routed through the same statement-position desugaring as `i++;` standalone — `i++`/`i--` become `i = i ± 1`, compound assignments become their plain-assignment equivalents. `//@ invariant` and `//@ decreases` annotations placed in the for-loop body carry through to the desugared `while`.

### 4.3 Return Inside Loops

**Dafny:** `return` inside loops is supported. Dafny handles early return paths natively.

**Lean:** `return` inside a `while` loop is **not supported** — Velvet does not support it. The user must restructure to use `break` with an explicit result variable:

```typescript
let result = -1;
while (...) {
  //@ invariant ...
  //@ done_with result !== -1 || !(lo <= hi)
  if (...) { result = mid; break; }
}
return result;
```

### 4.4 Discriminant Dispatch → Match

Both `switch` on a discriminant and if-chains on a discriminant translate to `match` in both backends. `lsc` detects the pattern: conditions of the form `x.field === "variant"` (or `x === "variant"` for enum-like types) on the same variable.

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

Both produce (Lean):

```lean
match pkt with
| .syn seq => return seq
| .data _ len => return state + len
| _ => return state
```

Both produce (Dafny):

```dafny
match pkt {
  case syn(seq) =>
    return seq;
  case data(_, len) =>
    return state + len;
  case _ =>
    return state;
}
```

**Detection:** ts-morph provides the variable's type (discriminated union), the discriminant field name, and the variant field types. `lsc` uses this — no guessing.

**Field binding:** Property accesses on the matched variable (`pkt.seq`, `pkt.len`) become bound variables from the match pattern. Unused fields get `_`.

**Switch fall-through:** a non-empty `case` must end in `break`/`return`/`throw` — C-style fall-through into the next case's body is rejected. Empty `case A: case B: body` stacking (leading labels sharing the next body) is supported.

**Enum-like types** (string literal unions, no data fields) stay as `if` with constructor equality. Only discriminated unions with data fields trigger the if-chain → match transformation.

---

## 5. Pure Function Detection

A function is **pure** if its body contains no `while` statements, no `for...of` statements, and no mutable `let` declarations, and it does not transitively call any non-pure function (determined via call-graph analysis in the resolve phase).

Pure functions are handled differently by each backend:

- **Lean:** generates a plain `def` in `foo.types.lean` inside `namespace Pure`, plus a Velvet method wrapper: `return Pure.foo params`. This enables proofs by standard Lean induction. In spec annotations, calls to pure functions emit as `Pure.fnName`. See [SPEC_LEAN.md](SPEC_LEAN.md).
- **Dafny:** generates a `function` declaration (no wrapper, no namespace). `requires` and `ensures` are emitted directly. If the function has `ensures`, a companion `lemma` is generated as a proof target. See [SPEC_DAFNY.md](SPEC_DAFNY.md).

### 5.1 `//@ pure` — Forced Purity and `function by method`

The `//@ pure` annotation forces a function to be treated as pure in the call graph, even if it contains loops or calls impure functions. This prevents impurity from propagating to callers.

```typescript
//@ pure
function tagNameExists(m: Model, name: string, excludeTag?: TagId): boolean {
  for (const [tid, tag] of Object.entries(m.tags)) {
    if (excludeTag === undefined || tid !== excludeTag) {
      if (eqIgnoreCase(tag.name, name)) return true
    }
  }
  return false
}
```

If `transformPureBody` can auto-convert the body to a pure expression, the function emits as a normal Dafny `function`. If it cannot (e.g., the body has loops), it emits as `function by method`:

```dafny
function tagNameExists(m: Model, name: string, excludeTag: Option<TagId>): bool
{
}
by method {
  var i_tid_keys := SetToSeq(m.tags.Keys);
  // ... auto-generated imperative body
}
```

The empty `{ }` block is the spec body placeholder — **Dafny will reject the file as a parse error until it is filled in**. Complete it in the `.dfy` file *before* running verify:

```dafny
function tagNameExists(m: Model, name: string, excludeTag: Option<TagId>): bool
{
  exists tid :: tid in m.tags &&
    (match excludeTag { case None => true case Some(v) => v != tid }) &&
    eqIgnoreCase(m.tags[tid].name, name)
}
by method {
  // ... auto-generated, preserved by regen
}
```

The spec body is purely additive — `regen` three-way-merges and preserves user additions while updating the `by method` block when the TypeScript changes.

**Effect on callers:** Since `//@ pure` functions are `function`s in Dafny, callers that only invoke pure functions become pure automatically. For example, a large `switch`-based `apply` function becomes a `function` if all the map-iterating helpers it calls are marked `//@ pure`.

**Lean backend:** `//@ pure` with `function by method` is Dafny-specific. Using `//@ pure` on a function whose body cannot be auto-converted will throw an error for the Lean backend.

---

## 6. Type Mapping

### 6.1 Rules

| TypeScript type | Lean type | Dafny type |
|----------------|-----------|-----------|
| `number` | `Int` | `int` |
| `bigint` | `Int` | `int` |
| `number` (with `//@ type nat`) | `Nat` | `nat` |
| `boolean` | `Bool` | `bool` |
| `string` | `String` | `string` |
| `T[]` / `Array<T>` | `Array T'` | `seq<T'>` |
| `Map<K, V>` | `Std.HashMap K' V'` | `map<K', V'>` |
| `Set<T>` | `Std.HashSet T'` | `set<T'>` |
| `T \| undefined` | `Option T'` | `Option<T'>` |
| `true \| false \| undefined` | `Option Bool` | `Option<bool>` |
| `Record<K, V>` | `Std.HashMap K' V'` | `map<K', V'>` |
| `(a: T1, b: T2) => R` (function type) | — | `(T1, T2) -> R` (typically used in a `type Foo = (...) => R` alias; lambda params passed to a callee with a `Foo`-typed parameter get inferred types) |
| `unknown` | `Int` | `int` |
| `[T, T, ...]` (tuple) | `Array T'` | `seq<T'>` |
| `<T extends Base>` (record/nominal bound) | `T` erased to `Base` | `T` erased to `Base` |
| `<T>` / `<T extends U>` (unbounded, or union/intersection bound) | `T` kept as type param (bound dropped) | `T` kept as type param (bound dropped) |
| `A \| B` (union param) | field intersection type | field intersection type |
| Anything else | Pass through | Pass through |

`lsc` reads parameter and variable types from ts-morph. Primitive types are mapped per the table. User-defined types (like `State`, `Event`) are passed through by name — the corresponding backend type is generated from the TS type declaration.

### 6.1.1 BigInt

TypeScript's `bigint` type maps to `Int`/`int` (same as `number`). BigInt literals like `32n`, `0xffffn` are treated as integer literals with the `n` suffix stripped. Hex literals (`0x...`) and the `n` suffix are supported in both function bodies and `//@ ` annotations:

| TypeScript | Dafny | Lean |
|-----------|-------|------|
| `32n` | `32` (int) | `32` (Int) |
| `0xffffn` | `65535` (int) | `65535` (Int) |

**Bitwise operators (Dafny only):** Since Dafny's `int` has no native bitwise ops, they are translated to arithmetic when the right operand is a literal:

| TypeScript | Dafny |
|-----------|-------|
| `x >> 32n` | `x / 4294967296` |
| `x << 8n` | `x * 256` |
| `x & 0xffffffffn` | `x % 4294967296` (only when mask+1 is a power of 2) |

Lean backend does not yet support bitwise operators.

### 6.1.2 Constants

Module-level `const` declarations are extracted and emitted as constants in the backend:

```typescript
const MAPPED_PREFIX = 281470681743360
```

→ Dafny: `const MAPPED_PREFIX: int := 281470681743360`
→ Lean: `def MAPPED_PREFIX : Int := 281470681743360`

Constants are always extracted (even in `//@ verify` selective mode) so verified functions can reference them. The type is inferred from the initializer. Literal types (e.g., TypeScript inferring `281470681743360` instead of `number`) are widened to their base type.

### 6.1.3 Real Numbers

JavaScript has one numeric type (`number`, IEEE 754 doubles). LemmaScript maps `number` to `int` by default, but **non-integer numeric literals** (e.g., `0.8`, `3.14`) are typed as `real`:

| TypeScript | Dafny | Lean |
|-----------|-------|------|
| `42` | `42` (int) | `42` (Int) |
| `0.8` | `0.8` (real) | `0.8` (Float) |

**Mixed arithmetic:** When `int` and `real` operands appear in the same arithmetic expression, the `int` operand is coerced to `real` with `as real`:

```typescript
tokens.length * 0.8    // nat * real
```

→ Dafny: `(|tokens| as real * 0.8)`

**`Math.ceil` and `Math.floor`:** These convert `real` → `int`:

| TypeScript | Dafny | When |
|-----------|-------|------|
| `Math.ceil(x)` | `CeilReal(x)` | `x` is `real` |
| `Math.ceil(n)` | `n` (identity) | `n` is `int` |
| `Math.floor(x)` | `FloorReal(x)` | `x` is `real` |
| `Math.floor(a / b)` | `JSFloorDiv(a, b)` | `a`, `b` are `int` (legacy) |
| `Math.floor(n)` | `n` (identity) | `n` is `int` |

`CeilReal` and `FloorReal` are preamble helpers using Dafny's built-in `.Floor` on `real`:

```dafny
function FloorReal(x: real): int { x.Floor }
function CeilReal(x: real): int {
  if x == (x.Floor as real) then x.Floor else x.Floor + 1
}
```

**Cross-file types:** When a verified function references a type imported from another file (e.g., `Module` from `../types`), `lsc` automatically resolves the type via ts-morph and generates the corresponding backend type declaration. Resolution is recursive — types referenced by resolved types are also extracted (e.g., resolving `Claim` also extracts `ClaimStatus`, `EmbeddedDecision`). Both record types and type aliases (string unions, discriminated unions) are resolved. `lsc` discovers the nearest `tsconfig.json` for module resolution. Built-in types (`Map`, `Set`, `Array`, etc.) are excluded.

### 6.2 String Literals as Constructors

When a variable has a user-defined type, string literal comparisons map to constructor equality:

| TypeScript | Lean | Dafny |
|-----------|------|-------|
| `state === "idle"` | `state = .idle` | `state.idle?` |
| `"connecting"` (as value) | `.connecting` | `State.connecting` |

The same coercion applies wherever a string literal appears in a user-type context: ternary branches, record fields, return values, and variable assignments.

### 6.3 Discriminated Unions

Discriminated unions with data fields map to:
- Lean: `inductive` with constructor arguments
- Dafny: `datatype` with constructor arguments

```typescript
type Packet =
  | { tag: "syn"; seq: number }
  | { tag: "ack"; seq: number }
  | { tag: "data"; seq: number; len: number }
  | { tag: "fin" }
```

Generated (Lean):

```lean
inductive Packet where
  | syn (seq : Int) : Packet
  | ack (seq : Int) : Packet
  | data (seq : Int) (len : Int) : Packet
  | fin : Packet
deriving Repr, Inhabited
```

Generated (Dafny):

```dafny
datatype Packet = syn(seq: int) | ack(seq: int) | data(seq: int, len: int) | fin
```

**Single-variant unions** are supported. TypeScript collapses `type X = | { kind: 'Foo'; ... }` to a plain object type, so `lsc` detects single-variant unions by checking for `|` syntax in the source declaration text combined with a string-literal discriminant field.

```typescript
type MultiAction =
  | { kind: 'SingleAction'; projectId: string; action: Action }
```

→ Dafny: `datatype MultiAction = SingleAction(projectId: string, action: Action)`

**Ensures with discriminated unions** — specs that condition on the variant use `match`:

```typescript
//@ ensures pkt.tag === "syn" ==> \result === pkt.seq
//@ ensures pkt.tag === "data" ==> \result === state + pkt.len
```

→ (Lean):

```lean
ensures match pkt with
  | .syn seq => res = seq
  | .data _ len => res = state + len
  | _ => True
```

→ (Dafny):

```dafny
  ensures pkt.syn? ==> res == pkt.seq
  ensures pkt.data? ==> res == state + pkt.len
```

### 6.4 Record/Object Types

TS interfaces and object types map to:
- Lean: `structure` with field projection
- Dafny: `datatype` with single constructor

```typescript
interface EffectState {
  res: boolean;
  done: boolean;
  rec: boolean;
}
```

Generated (Lean):

```lean
structure EffectState where
  res : Bool
  done : Bool
  rec : Bool
deriving Repr, Inhabited, DecidableEq
```

Generated (Dafny):

```dafny
datatype EffectState = EffectState(res: bool, done: bool, rec: bool)
```

**Field access** passes through directly: `state.res` → `state.res` (both backends).

**Object literals:**

```typescript
return { res: true, done: true, rec: true };
```

→ Lean: `return { res := true, done := true, rec := true }`
→ Dafny: `return EffectState(true, true, true);`

**Spread update** (`{ ...obj, f: v }`) maps to functional record update in both backends. **Object-spread merge** (`{ ...base, ...over }`, multiple sources) expands field-wise against the result record type: an override field wins when present, else the base shows through; for optional fields presence is decided at runtime (`Some?`), and an optional override operand guards the whole merge. Both operands need a known record type. See [`examples/spreadMerge.ts`](examples/spreadMerge.ts).

**Record index by enum key** (`rec[k]`, `k` ranging over field names) lowers so the dynamic access verifies like a static one: a named string-union key becomes `match k { case f => rec.f }`; an inline union key (`"a" | "b"`) becomes an equality chain `if k === "a" then rec.a else …`. The chain/match covers exactly the key's members, so a key that is a subset of the fields stays sound. See [`examples/recordIndexByEnum.ts`](examples/recordIndexByEnum.ts).

**Inline object types:** Anonymous object types in interface fields (e.g., `decision?: { decision: string; rationale: string }`) are extracted as named datatypes with synthetic names (e.g., `SpecEntryDecision`). The parent field references the generated name.

**Anonymous return types:** Functions returning inline object types (e.g., `(): { modules: Module[]; claims: Claim[] }`) get a synthetic return type (e.g., `ParseSpecYamlResult`). Named type aliases (e.g., `type Foo = { ... }`) are resolved by their alias name instead.

**Record constructor padding (Dafny):** When an object literal has fewer fields than the target datatype (e.g., TS code omits optional fields), missing optional fields are filled with `None`. The emitter matches provided fields by name against the datatype declaration.

**Optional field coercion:** When a non-optional value is assigned to an optional field in a record constructor (e.g., `createdAt: now` where `now: int` and the field type is `Option<int>`), the resolve phase wraps the value in `Some`. The coercion only fires when the value has a concrete non-optional type — `unknown` and `void` values are left as-is.

### 6.5 Type Mapping Implementation

Type mapping logic lives in `types.ts`: `parseTsType(tsType: string): Ty`. Each emitter has its own `Ty → string` function (`tyToLean` in `lean-emit.ts`, `tyToDafny` in `dafny-emit.ts`).

### 6.6 Full Examples

**Example 1: State machine (enum-like, no data)**

String literal unions with no data use `if` with constructor equality.

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

Both backends verify this. Lean uses `loom_solve` to discharge all VCs, including the inter-method call. Dafny's Z3 verifier handles it directly.

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

Both backends generate `match` for the body and ensures. Both verify automatically.

---

## 7. `lsc` CLI

```
lsc gen [--backend=lean|dafny] <file.ts>      — generate verification artifacts
lsc check [--backend=lean|dafny] <file.ts>    — gen + verify
lsc regen --backend=dafny <file.ts>           — regenerate with three-way merge (Dafny only)
lsc extract <file.ts>                          — print Raw IR JSON (debugging)
lsc info <file.ts>                             — write a JSON summary of verified functions (backend-neutral)
```

Default backend is Dafny. `extract` and `info` are backend-neutral and always run, regardless of any `//@ backend` directive.

**Flags** (passed through to the prover on `check`):
- `--time-limit=<seconds>` — per-VC verification time limit (Dafny: `--verification-time-limit`).
- `--extra-flags=<string>` — extra flags forwarded verbatim to the backend prover.

### 7.1 `gen`

- **Lean:** writes `foo.types.lean` + `foo.def.lean`
- **Dafny:** writes `foo.dfy.gen`, seeds `foo.dfy` if missing

### 7.2 `check`

- **Lean:** gen + `lake build` (checks `.def.lean` + `.proof.lean` + `.spec.lean`)
- **Dafny:** gen + additions-only check + `dafny verify`

### 7.3 `regen` (Dafny only)

Three-way merge when generated code changes. See [SPEC_DAFNY.md](SPEC_DAFNY.md).

### 7.4 `info`

Extract-only (no resolve/transform/emit). Writes `foo.ts.json` next to the source, mapping each top-level function and class method (`ClassName.method`) to its signature and original `//@ requires` / `//@ ensures` / `//@ decreases` clause text. Backend-neutral.

---

## 8. Pipeline

Six-phase pipeline:

```
extract → resolve → narrow → transform → peephole → emit
```

Each phase (and the three intermediate representations — Raw IR, Typed IR, IR) is documented in [TOOLS.md](TOOLS.md#pipeline).

---

## 9. Not Yet Supported

The following TS features are not yet handled by the toolchain:

- Compound pattern matching (nested match on multiple discriminated unions)
- `await` / true async — a `Promise<T>`-returning function with an `await` in its body is unmodellable. An `async` function with **no** `await` is supported: its `Promise<T>` return type is unwrapped to `T` (the wrapper is just calling convention), so the body verifies normally.
- Error reporting (mapping prover errors to TS source locations)
- VS Code extension
