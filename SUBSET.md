# LemmaScript — The Supported TypeScript Subset

A friendly tour of *which* TypeScript you can write and have verified. For the precise translation rules, see [SPEC.md](SPEC.md); for a hands-on walkthrough, [GETTING_STARTED.md](GETTING_STARTED.md).

## The idea in one minute

You write ordinary TypeScript and add `//@ ` comments that state what your code should do. The `lsc` tool reads the TypeScript, translates the parts it understands into a prover's language (Dafny or Lean 4), and the prover checks that your code actually meets the spec.

```typescript
// Clamp a number into [lo, hi].
export function clamp(x: number, lo: number, hi: number): number {
  //@ verify
  //@ requires lo <= hi
  //@ ensures lo <= \result && \result <= hi
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}
```

The function body is plain TypeScript that runs unchanged. The `//@ ` lines are the contract — invisible at runtime, checked by the prover. Nothing here is a custom dialect: it's a *subset* of TypeScript, plus comment annotations.

Two things shape what you can verify:
1. **What TypeScript constructs `lsc` understands** — the subject of this document.
2. **What you can say in `//@ ` annotations** — the spec language, covered in [SPEC.md §2](SPEC.md#2-the---annotation-language).

> **Backends differ.** Both Dafny and Lean are supported, but Dafny currently understands a wider set of library methods (most string/array helpers below are Dafny-only). Where it matters, SPEC.md has a per-backend column. When in doubt, target Dafny.

## Types you can use

| You write | Modeled as | Notes |
|-----------|-----------|-------|
| `number` | integer | Maps to `int` by default. Add `//@ type nat` for a non-negative integer. |
| `number` (non-integer literal) | real | `0.8`, `3.14` become reals; mixed int/real arithmetic coerces automatically. |
| `bigint` | integer | Same as `number`; `32n`, `0xffffn` literals supported. |
| `boolean` | bool | |
| `string` | string | |
| `T[]` / `Array<T>` / `readonly T[]` | sequence | |
| `[A, B, ...]` (heterogeneous tuple) | tuple | Native tuple (`(A, B)` / `A × B`). Access needs a literal index (`t[0]`, `t[1]`); `const [a, b] = t` works. |
| `[T, T, ...]` (homogeneous tuple) | sequence | Same-typed elements model as a `seq` (more capable than a fixed tuple). |
| `Map<K, V>` / `Record<K, V>` | map | |
| `Set<T>` | set | |
| `T \| undefined`, `T \| null` | optional | `undefined` and `null` model identically. |
| user `type` / `interface` | generated datatype | Records and unions — see [Modeling data](#modeling-data). |
| `<T extends Base>` | generic | Type parameter erased to its bound; `.map`/`.filter` etc. work over it. |
| `(a: T) => R` | function value | Used for higher-order params and lambdas. |

User-defined types referenced from a verified function are pulled in automatically, recursively, even across files. You don't redeclare them.

## Values, operators, literals

All the usual operators carry over with their normal meaning: `=== !== < <= > >= + - * / % && || !` and the ternary `c ? a : b`. `number / number` is real division (matching JS: `3 / 2 === 1.5`); for an integer quotient use `Math.floor(a / b)`. `bigint / bigint` is integer division.

Supported literal forms include number/bigint/hex literals, string and template literals (`` `${n} items` `` concatenates), array literals with spread (`[...xs, e]`), object literals with spread (`{ ...obj, f: v }`), and `Record`/`Map` object literals.

A handful of `Math.*` helpers are understood: `abs`, `min`, `max`, `floor`, `ceil` (and `Math.max(...arr)` over an array).

## Control flow

| Construct | Supported? |
|-----------|-----------|
| `if` / `else if` / `else` | ✅ |
| `while` | ✅ — annotate with `//@ invariant` and `//@ decreases` |
| `for (let i = ...; ...; i++)` | ✅ — desugared to a `while` |
| `for (const x of xs)` | ✅ — over arrays, sets, `Object.entries/values` |
| `switch` on a discriminant | ✅ — becomes a `match` |
| `if`-chain on a `.tag` field | ✅ — also becomes a `match` |
| `break` | ✅ — add `//@ done_with` to say what holds on exit |
| `return` inside a loop | ✅ on Dafny; on Lean, restructure to `break` + a result variable |
| `throw new Error(...)` | ✅ — modeled as an unreachable point; characterize valid input with `//@ requires` instead of relying on it |

Loops are where most of the proof effort lives: a `while` or `for` usually needs a loop invariant. That's expected — it's the heart of what's being verified.

## Functions, generics, lambdas

Plain functions are the core unit. Parameters and the return type are read from your annotations. A function whose body is a single expression (or is recursive) becomes prover-level *and* spec-usable — you can mention it inside other `//@ ` specs — so write predicate helpers as expression-bodied functions.

Generics work: `<T extends Base>` parameters, plus the higher-order array methods `.map`, `.filter`, `.some`, `.every`, `.find`, `.findIndex` with inline arrow functions. Lambdas passed to these get their parameter types inferred.

`async` functions are supported **only when they contain no `await`** — the `Promise<T>` wrapper is just unwrapped to `T`. A real `await` / genuine async is not modelable.

## Collections and their methods

Arrays, strings, maps, and sets all carry a useful slice of their standard library. A representative set (Dafny has the fullest coverage — see [SPEC.md §3.2](SPEC.md#32-special-forms) for the exact list and any per-backend gaps):

- **Array** — `.length`, indexing `a[i]`, `.map`, `.filter`, `.some`, `.every`, `.includes`, `.indexOf`, `.find`, `.findIndex`, `.slice`, `.concat`, `.flat`, `.join`, `.shift`, `.pop`, immutable update `a.with(i, v)` (and `a[i] = v`), spread `[...a, x]`.
- **String** — `.length`, indexing, `.slice`, `.substring`, `.indexOf`, `.includes`, `.startsWith`, `.endsWith`, `.split`, `.trim`/`.trimStart`/`.trimEnd`, `.toLowerCase`/`.toUpperCase`, `.charCodeAt`.
- **Map / Record** — `.get` (returns optional in code, direct in specs), `.set`, `.has`, `.delete`, `.size`, `in`, object-literal construction, `Object.entries`/`values`/`fromEntries`.
- **Set** — `.add`, `.delete`, `.has`, `.size`, `in`, iteration.

Indexing into an array under `noUncheckedIndexedAccess` yields an optional element, matching TypeScript's own typing.

## Modeling data

Two shapes cover most domain modeling, and both translate directly:

**Records** — an object type becomes a single-constructor datatype with the same fields:

```typescript
type Point = { x: number; y: number };
```

```dafny
datatype Point = Point(x: int, y: int)
```

**Discriminated unions** — a union of objects sharing a literal tag becomes a sum type, and you branch on it with `switch` or an `if`-chain on the tag:

```typescript
type Result =
  | { tag: "ok"; value: number }
  | { tag: "error"; message: string };
```

```dafny
datatype Result = ok(value: int) | error(message: string)
```

A `switch`/`if`-chain on `result.tag` becomes a `match`, and a spec that conditions on a variant uses the constructor test — `result.tag === "ok"` reads as `result.ok?` in Dafny.

A bare string-literal union (`type State = "idle" | "running"`) becomes an enum: comparisons like `s === "idle"` and using `"running"` as a value both work.

```dafny
datatype State = idle | running
```

## The annotation layer (the other half)

The `//@ ` comments are where you say what to prove. The common ones:

- `//@ requires P` — a precondition the caller must meet.
- `//@ ensures P` — a postcondition the function guarantees (use `\result` for the return value).
- `//@ invariant P` / `//@ decreases D` — on loops.
- `//@ verify` — opt this function in (once any function in a file is marked, only marked functions are verified).

The spec expressions support quantifiers (`forall(k, P)`, `exists(k, P)`), implication (`==>`), and the same operators and method calls as code. The full language — including ghost state, `//@ havoc`, `//@ extern`, and selective verification — is [SPEC.md §2](SPEC.md#2-the---annotation-language).

## Where to go next

- [GETTING_STARTED.md](GETTING_STARTED.md) — clone a working example and run the edit loop.
- [SPEC.md](SPEC.md) — the precise annotation language and translation rules.
- [examples/](examples) — small, complete, verified LemmaScript files.
- [README.md](README.md) — the case studies, from string helpers to full verified apps.
