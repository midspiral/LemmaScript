# LemmaScript — Implementation Specification

**Version:** 0.3
**Date:** April 2026

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
| `verify` | Before first statement of function body | Mark function for verification (see §2.5) |
| `requires` | Before first statement of function body | Precondition |
| `ensures` | Before first statement of function body | Postcondition (`\result` refers to return value) |
| `invariant` | Before first statement of loop body | Loop invariant |
| `decreases` | Before first statement of loop body | Termination metric |
| `done_with` | Before first statement of loop body | Post-loop condition (see §5.2) |
| `type` | Before first statement of function body | Type override for a variable (see §2.4) |
| `ghost let x = e` | Before any statement | Ghost variable (proof-only, not runtime). See §2.3. |
| `ghost x = e` | Before any statement | Ghost variable reassignment. |
| `assert e` | Before any statement | Assertion (`assertGadget` in Lean, `assert` in Dafny). |

### 2.2 Spec Expression Grammar

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
          | '[' (expr ',')* expr? ']'
          | '{' (IDENT ':' expr ',')* IDENT ':' expr '}'
TYPE     := 'nat' | 'int'
```

**`\result`** refers to the function's return value (following Frama-C/ACSL convention). It is only valid in `ensures` annotations. The `\` prefix distinguishes it from any TS variable named `result`.

**`forall(k, P)`** infers the type of `k`: explicit `: nat` → `Nat`/`nat`; if `k` is used as a collection key or element (e.g., `map.has(k)`, `set.has(k)`, `arr.includes(k)`) → the collection's key/element type; otherwise `Int`/`int`. Same for `exists`.

### 2.3 Ghost Variables and Assertions

Ghost annotations introduce proof-only state that does not exist at runtime:

```typescript
//@ ghost let enqueued = new Set<string>()   // ghost variable declaration
//@ ghost enqueued = enqueued.add(id)        // ghost assignment
//@ assert !enqueued.has(id)                 // assertion
```

Ghost `let` declarations become mutable bindings in both backends (since they are typically reassigned). Ghost assignments become regular assignments. Assertions become `assertGadget` in Lean and `assert` in Dafny.

The init expression in `ghost let` supports `new Set<T>()` and `new Map<K,V>()` constructors, as well as any spec expression. An optional type annotation is supported: `//@ ghost let x: type = expr`.

### 2.4 Type Annotations

`lsc` reads TS types from ts-morph and maps them to the backend's type system. For `number` variables, the default mapping is `Int`/`int`. The `type` annotation overrides this to `Nat`/`nat`:

```
//@ type <varname> nat
```

Use `nat` for non-negative loop counters and array indices.

User-defined types (string literal unions, discriminated unions) are generated automatically with the same name as the TS type. No annotation needed or supported for these.

When a variable is Nat-typed:
- Lean: `arr[i]!` instead of `arr[i.toNat]!`
- Dafny: no difference (Dafny handles `nat` natively)
- Ghost function calls pass the variable directly

Interface fields can also be overridden with a trailing annotation on the same line:

```typescript
export interface Model {
  memberCount: number; //@ type nat
  expenses: Expense[];
}
```

### 2.5 Selective Verification: `//@ verify`

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

**Behavior:** If any function in the file has `//@ verify`, `lsc` switches to selective mode and only extracts functions marked with `//@ verify`. Functions without it are silently skipped. Type and interface declarations are always extracted (they may be needed by verified functions).

If no function in the file has `//@ verify`, all functions are extracted as before. This keeps existing LemmaScript projects (where every function is in-fragment) working without changes.

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
| `+`, `-`, `*`, `/`, `%` | `+`, `-`, `*`, `/`, `%` | `+`, `-`, `*`, `/`, `%` |

No normalization of operators. Both backends handle all comparison directions.

**String truthiness:** `!stringVar` where the operand has type `string` is translated as `stringVar == ""` (Dafny) / `stringVar = ""` (Lean), matching JavaScript's truthy semantics for strings.

### 3.2 Special Forms

| Spec / TS | Lean | Dafny |
|-----------|------|-------|
| `arr.length` | `arr.size` | `\|arr\|` |
| `arr[e]` (Nat index) | `arr[e]!` | `arr[e]` |
| `arr[e]` (Int index) | `arr[e.toNat]!` | `arr[e]` |
| `f(a, b)` | `f a b` | `f(a, b)` |
| `x = f(a, b)` (method call) | `x ← f a b` | `x := f(a, b);` |
| `Math.floor(a / b)` | `a / b` (Lean int div floors) | `JSFloorDiv(a, b)` |
| `c ? a : b` | `if c then a else b` | `if c then a else b` |
| `s.indexOf(sub)` | `JSString.indexOf s sub` | `StringIndexOf(s, sub)` |
| `s.slice(start, end)` | `JSString.slice s start end` | `s[start..end]` |
| `s.trim()` | — | `StringTrim(s)` |
| `s.toLowerCase()` | — | `StringToLower(s)` |
| `s.toUpperCase()` | — | `StringToUpper(s)` |
| `s.includes(sub)` | — | `StringIndexOf(s, sub) >= 0` |
| `s.length` | `s.length` | `\|s\|` |
| `arr.map((x) => e)` | `arr.map (fun x => e)` | `Seq.Map((x) => e, arr)` |
| `arr.filter((x) => e)` | `arr.filter (fun x => e)` | `Seq.Filter((x) => e, arr)` |
| `arr.every((x) => e)` | `arr.all (fun x => e)` | `Seq.All(arr, (x) => e)` |
| `arr.some((x) => e)` | `arr.any (fun x => e)` | `exists x :: x in arr && e` |
| `arr.includes(x)` | `arr.contains x` | `(x in arr)` |
| `arr.find((x) => e)` | `arr.find? (fun x => e)` | — |
| `arr.shift()` | — | `arr[0]` + `arr := arr[1..]` |
| `arr.slice(start)` | — | `arr[start..]` |
| `expr!` (non-null) | unwrap Option | unwrap Option / direct map access |
| `expr \|\| default` (on optional) | match Some/None | `match { Some(v) => v, None => default }` |
| `expr?.method(args)` | — | `if key in map { ... }` |
| `expr as T` | stripped | stripped |
| `new Map(arr.map(fn))` | — | loop building `map[]` |
| `[a, b, c]` | `#[a, b, c]` | `[a, b, c]` |
| `[...arr, e]` | `Array.push arr e` | `(arr + [e])` |
| `{ ...obj, f: v }` | `{ obj with f := v }` | `obj.(f := v)` |
| `arr.with(i, v)` | `arr.set! i v` | `arr[i := v]` |
| `new Map<K,V>()` | `Std.HashMap.empty` | `map[]` |
| `m.get(k)` (in code) | `m.get? k` | `if k in m then Some(m[k]) else None` |
| `m.get(k)` (in spec) | `m.get! k` | `m[k]` |
| `m.set(k, v)` | `m := m.insert k v` | `m := m[k := v]` |
| `m.has(k)` | `m.contains k` | `(k in m)` |
| `m.size` | `m.size` | `\|m\|` |
| `new Set<T>()` | `Std.HashSet.empty` | `{}` |
| `s.has(x)` | `s.contains x` | `(x in s)` |
| `s.add(x)` | `s := s.insert x` | `s := (s + {x})` |
| `s.delete(x)` | `s := s.erase x` | `s := (s - {x})` |
| `s.size` | `s.size` | `\|s\|` |
| `for (const x of s)` | `.toArray` + for-in | `SetToSeq` + while |
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

Lambda bodies can be expressions (`(x) => x + 1`) or statement blocks (`(x) => { ... }`).

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
| `arr.map(f)` | `map` | `arr.map f` | `Seq.Map(f, arr)` |
| `arr.filter(f)` | `filter` | `arr.filter f` | `Seq.Filter(f, arr)` |
| `arr.every(f)` | `every` | `arr.all f` | `Seq.All(arr, f)` |
| `arr.some(f)` | `some` | `arr.any f` | `exists x :: x in arr && ...` |
| `arr.includes(x)` | `includes` | `arr.contains x` | `(x in arr)` |
| `arr.find(f)` | `find` | `arr.find? f` | — |
| `m.get(k)` | `mapGet` | `m.get? k` | `if k in m then Some(m[k]) else None` |
| `m.has(k)` | `mapHas` | `m.contains k` | `(k in m)` |
| `m.set(k, v)` | `mapSet` | `m.insert k v` | `m[k := v]` |
| `s.has(x)` | `setHas` | `s.contains x` | `(x in s)` |
| `s.add(x)` | `setAdd` | `s.insert x` | `(s + {x})` |
| `s.delete(x)` | `setDelete` | `s.erase x` | `(s - {x})` |

The transform checks helper-function methods first, then dot-notation methods. If neither matches, it errors.

### 3.9 Map, Set, and Optional Narrowing

**Map and Set** (`Map<K,V>`, `Set<T>`) are immutable types in both backends. `const` declarations of collection types are automatically promoted to mutable bindings, since TS mutates in place but the backends require reassignment.

Mutating calls (`m.set(k, v)`, `s.add(x)`, `s.delete(x)`) are transformed into reassignments:
```typescript
inDegree.set(id, 0);    // → Lean: inDegree := inDegree.insert id 0
                          // → Dafny: inDegree := inDegree[id := 0];
enqueued.add(id);        // → Lean: enqueued := enqueued.insert id
                          // → Dafny: enqueued := (enqueued + {id});
```

**`Map.get` returns `Option`** in code context (since the key may not exist). In spec context (annotations), `map.get(k)` emits direct access without an Option wrapper, matching how specs reason about map contents.

**Optional narrowing:** `v !== undefined` where `v : T | undefined` emits a pattern match on Some/None, binding the unwrapped value in the then-branch. Optional comparisons like `opt === 0` emit a match on `Some`/`None`.

**Quantifier type inference:** When a quantifier variable is used as a collection key or element (e.g., `forall(k, map.has(k) ==> ...)`, `forall(v, arr.includes(v) ==> ...)`), the variable type is inferred from the collection's key/element type instead of defaulting to `Int`.

**Set iteration:** `for (const x of s)` where `s` is a `Set<T>` converts the set to an array first (Lean: `.toArray`, Dafny: `SetToSeq` helper), then iterates with a standard indexed loop.

**Map destructuring iteration:** `for (const [k, v] of map)` where the iterable has type `Map<K,V>` desugars to iterating over `map.Keys` (via `SetToSeq`), with `k` bound to each key and `v` bound to `map[k]`. General destructuring in for-of (e.g., `for (const [a, b, c] of tuples)`) binds each name to `elem[0]`, `elem[1]`, etc.

---

## 4. Statement Translation

### 4.1 Basic Statements

| TypeScript | Lean | Dafny |
|-----------|------|-------|
| `let x = e` | `let mut x : T := e'` | `var x := e';` |
| `const x = e` | `let x := e'` | `var x := e';` |
| `x = e` | `x := e'` | `x := e';` |
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

### 4.3 Return Inside Loops

`return` inside a `while` loop is **not supported**. Lean's Velvet does not support `return` inside loops, and for consistency both backends reject it. If `lsc` encounters `return` inside a loop, it emits an error.

The user must restructure to use `break` with an explicit result variable:

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

The TypeScript is still valid and runs identically.

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

**Enum-like types** (string literal unions, no data fields) stay as `if` with constructor equality. Only discriminated unions with data fields trigger the if-chain → match transformation.

---

## 5. Pure Function Detection

A function is **pure** if its body contains no `while` statements and no mutable `let` declarations, and it does not transitively call any non-pure function (determined via call-graph analysis in the resolve phase).

Pure functions are handled differently by each backend:

- **Lean:** generates a plain `def` in `foo.types.lean` inside `namespace Pure`, plus a Velvet method wrapper: `return Pure.foo params`. This enables proofs by standard Lean induction. In spec annotations, calls to pure functions emit as `Pure.fnName`. See [SPEC_LEAN.md](SPEC_LEAN.md).
- **Dafny:** generates a `function` declaration (no wrapper, no namespace). `requires` and `ensures` are emitted directly. If the function has `ensures`, a companion `lemma` is generated as a proof target. See [SPEC_DAFNY.md](SPEC_DAFNY.md).

---

## 6. Type Mapping

### 6.1 Rules

| TypeScript type | Lean type | Dafny type |
|----------------|-----------|-----------|
| `number` | `Int` | `int` |
| `number` (with `//@ type nat`) | `Nat` | `nat` |
| `boolean` | `Bool` | `bool` |
| `string` | `String` | `string` |
| `T[]` / `Array<T>` | `Array T'` | `seq<T'>` |
| `Map<K, V>` | `Std.HashMap K' V'` | `map<K', V'>` |
| `Set<T>` | `Std.HashSet T'` | `set<T'>` |
| `T \| undefined` | `Option T'` | `Option<T'>` |
| `Record<K, V>` | `Std.HashMap K' V'` | `map<K', V'>` |
| `unknown` | `Int` | `int` |
| Anything else | Pass through | Pass through |

`lsc` reads parameter and variable types from ts-morph. Primitive types are mapped per the table. User-defined types (like `State`, `Event`) are passed through by name — the corresponding backend type is generated from the TS type declaration.

**Cross-file types:** When a verified function references a type imported from another file (e.g., `WorkflowNode` from `types/index.ts`), `lsc` automatically resolves the type via ts-morph and generates the corresponding backend type declaration. This works for record/interface types used in function parameters. Built-in types (`Map`, `Set`, `Array`, etc.) are excluded from cross-file resolution.

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

**Spread update** (`{ ...obj, f: v }`) maps to functional record update in both backends.

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
```

Default backend is Lean (for now).

### 7.1 `gen`

- **Lean:** writes `foo.types.lean` + `foo.def.lean`
- **Dafny:** writes `foo.dfy.gen`, seeds `foo.dfy` if missing

### 7.2 `check`

- **Lean:** gen + `lake build` (checks `.def.lean` + `.proof.lean` + `.spec.lean`)
- **Dafny:** gen + additions-only check + `dafny verify`

### 7.3 `regen` (Dafny only)

Three-way merge when generated code changes. See [SPEC_DAFNY.md](SPEC_DAFNY.md).

---

## 8. Pipeline

Four-phase pipeline:

```
extract (ts-morph → Raw IR) → resolve (→ Typed IR) → transform (→ IR) → emit (→ text)
```

- **Extract** (`extract.ts`): ts-morph → structured AST. Body expressions are nodes, not strings. Annotations remain as strings.
- **Resolve** (`resolve.ts`): attaches types, classifies calls (pure/method/spec-pure/unknown), identifies discriminants, rejects unsupported patterns. Uses linked environments for lexical scoping. Computes purity via call-graph analysis: a function is pure if it is syntactically pure (no `while`/`for-of`/mutable `let`) AND does not transitively call any non-pure function.
- **Transform** (`transform.ts`): Typed IR → backend-neutral IR. Desugars `for-of` to indexed loops. Detects discriminant if-chains → `match`. Lifts embedded method calls to statement-level bindings (selective ANF, §3.6). Configured with `TransformOptions` for backend-specific behavior (monadic lifting, method name selection).
- **Emit** (`lean-emit.ts` / `dafny-emit.ts`): IR → backend text.

---

## 9. Not Yet Supported

The following TS features are not yet handled by the toolchain:

- Array index assignment (`arr[i] = v`)
- Compound pattern matching (nested match on multiple discriminated unions)
- Cross-file type imports
- async/await
- Error reporting (mapping prover errors to TS source locations)
- VS Code extension
