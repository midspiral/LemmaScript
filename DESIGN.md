# LemmaScript — Design Document

**Version:** 0.1 (Draft)
**Authors:** Nerd
**Date:** March 2026
**Status:** Early exploration

---

## 1. What This Is

LemmaScript is a verified imperative language that looks like a subset of TypeScript, verifies through Lean 4 via the Loom framework, and erases to plain TypeScript/JavaScript. Ghost state, loop invariants, pre/postconditions, decreases clauses, and proof blocks are all first-class constructs in the source language — and all disappear completely at compile time. What remains is the computational content: ordinary TypeScript that runs anywhere.

The core move: Verus is to Rust as LemmaScript is to TypeScript. The verified code *is* the production code, after erasure.

---

## 2. Why This Exists

### The JavaScript verification gap

JavaScript and TypeScript have no path to formal verification of functional properties. The options today are:

- **Runtime checking** (assertions, contracts, property-based testing): catches bugs but proves nothing.
- **Refinement types** (RSC, 2016): a research prototype for TypeScript that was never maintained. Restricted to decidable SMT fragments — no induction, no lemmas, no interesting proofs.
- **Model-based verification** (extract to Dafny, verify the model): works, but introduces a semantic gap between the verified model and the production code. The gap is where bugs hide.
- **Dafny's JS backend**: exists, but the runtime baggage (BigInteger emulation, immutable collections, class dispatch) creates a different semantic gap — between what the verifier assumed and what the compiled JS actually does.

### Why not a "lite Dafny backend"?

Building a compiler backend that faithfully preserves the semantics the Dafny verifier assumed is extraordinarily difficult. The failure mode is silent unsoundness: you *think* you proved something, but the compiled JS disagrees. This is worse than having no verification at all.

### Why not translate JS → Dafny?

Better failure modes (conservatism is safe — reject what you can't translate), but you still face the problem of faithfully modeling JavaScript's semantics in a language that wasn't designed for it. And when Dafny's SMT automation gets stuck, you're stuck — Dafny has no interactive proof escape hatch.

### The Verus existence proof

Verus demonstrates that a verification language can erase to a production systems language (Rust) with no semantic gap. The key insight: the verification annotations are *ghost* — they exist only for the prover and are erased during compilation. The computational content is real Rust, verified in place.

LemmaScript applies the same insight to the TypeScript ecosystem, built on top of Lean 4 infrastructure rather than Rust's.

---

## 3. Architecture

```
LemmaScript source (.ls / .ls.ts)
  │
  ├──→ [Frontend] Parse → LemmaScript AST
  │
  ├──→ [Lean Embedding] AST → Loom monadic program
  │     │
  │     ├──→ Loom WP generation → verification conditions
  │     │     │
  │     │     ├──→ Z3 / cvc5 (automated discharge)
  │     │     │
  │     │     └──→ Lean interactive mode (when SMT fails)
  │     │           │
  │     │           └──→ LLM-assisted proof search (lean-lsp-mcp)
  │     │
  │     └──→ Proof artifact (.lean) — machine-checked, archivable
  │
  └──→ [Erasure] AST → TypeScript (.ts) → JavaScript (.js)
        │
        └──→ Strip ghost state, invariants, proof blocks
              Emit computational skeleton
              (deletion, not translation)
```

### Key property: erasure is deletion

The erasure pass does not *transform* code. It *deletes* verification-only constructs and emits the remaining computational content as TypeScript. This is what makes it trustworthy — you cannot introduce bugs by removing things. The operational semantics of the erased program are a subset of the operational semantics of the source program.

---

## 4. The Language

LemmaScript is a subset of TypeScript extended with verification constructs. The computational fragment is valid TypeScript. The verification fragment is ghost.

### 4.1 Computational Fragment (erases to TS)

The computational fragment covers the subset of TypeScript with clean, verifiable semantics:

```typescript
// Variables and bindings
let x: number = 0
const y: string = "hello"
let mut z: number = 0          // explicit mutability marker

// Primitive types
number                          // IEEE 754 doubles (with integer reasoning mode)
int                             // mathematical integers (ghost-backed, erases to number)
boolean
string

// Compound types
Array<T>                        // fixed or dynamic arrays
{ field: T, ... }               // object literals (no prototypes)
[T, U, ...]                     // tuples
T | U                           // unions (discriminated)
T & U                           // intersections

// Control flow
if / else
while (with mandatory invariant)
for (of iterable)
return
match (exhaustive pattern matching)

// Functions
function f(x: T): U { ... }    // named functions
(x: T): U => { ... }           // arrow functions (no closure over mutable state)

// Modules
import / export
```

**Explicitly excluded from the computational fragment:**

- `this` and method dispatch
- Prototypes, classes with inheritance
- Closures over mutable state
- `any`, `unknown` (except at boundaries)
- Generators, async/await (future work)
- Implicit coercions
- `eval`, `with`, dynamic property access via string
- The event loop

These exclusions are not limitations of the implementation — they are design decisions that define the verifiable subset. Code that needs these features lives outside LemmaScript and interacts through the contract boundary.

### 4.2 Verification Fragment (erased at compile time)

```typescript
// Pre/postconditions
function withdraw(account: Account, amount: number): Account
  requires amount > 0
  requires account.balance >= amount
  ensures result.balance === account.balance - amount
  ensures result.balance >= 0
{
  return { ...account, balance: account.balance - amount }
}

// Loop invariants
let mut i: number = 0
let mut sum: number = 0
while (i < arr.length)
  invariant 0 <= i && i <= arr.length
  invariant sum === arraySum(arr, 0, i)       // ghost function
  decreases arr.length - i
{
  sum = sum + arr[i]
  i = i + 1
}

// Ghost variables (exist only during verification)
ghost let originalBalance = account.balance

// Ghost functions (specifications, not implementations)
ghost function isSorted(arr: Array<number>): boolean {
  forall(i, j, 0 <= i && i < j && j < arr.length ==> arr[i] <= arr[j])
}

// Lemma functions (proof steps, fully erased)
lemma function sortPreservesLength<T>(arr: Array<T>, sorted: Array<T>)
  requires isSorted(sorted) && isPermutation(arr, sorted)
  ensures sorted.length === arr.length
{
  // proof body — may be filled by LLM, checked by Lean
}

// Proof blocks (inline proof steps, fully erased)
proof {
  assert someIntermediateFact
  // unfold definition, apply lemma, etc.
}

// Quantifiers (in specifications only)
forall(x: T, P(x))
exists(x: T, P(x))
```

### 4.3 Syntax Design Principles

1. **Familiar to TypeScript developers.** The computational fragment *is* TypeScript. No new syntax for things that already have syntax.

2. **Verification constructs are visually distinct.** `requires`, `ensures`, `invariant`, `decreases`, `ghost`, `lemma`, `proof` — these are keywords that don't exist in TypeScript. A developer can see at a glance what's computational and what's specification.

3. **Erasure is syntactically obvious.** Everything that erases is introduced by a verification keyword. If it doesn't have a verification keyword, it survives erasure. No surprises.

4. **No verification in expressions.** Verification constructs appear at the statement/declaration level, never inside expressions. This keeps the computational fragment a clean subset of TS and makes erasure trivial.

---

## 5. Semantic Foundation

### 5.1 Embedding into Loom

LemmaScript programs are translated into Loom's monadic shallow embedding. Loom represents imperative programs as monadic computations in Lean 4 and provides:

- **Monad transformer algebra** for composing effects (state, exceptions, nondeterminism)
- **Weakest precondition generation** via the algebra structure
- **SMT integration** (Z3, cvc5) for automated discharge of VCs
- **Lean escape hatch** for interactive proofs when SMT fails

The translation targets Loom's imperative language, which already supports `let mut`, while loops, structured control flow, and arrays — aligning closely with LemmaScript's computational fragment.

### 5.2 Semantic Correspondence

The critical property: for every LemmaScript program P, the Loom embedding `⟦P⟧_loom` and the TypeScript erasure `⟦P⟧_ts` must agree on all observable behaviors.

This is achievable by construction because:

- The computational fragment has no features whose TypeScript semantics diverge from the Loom embedding's semantics (this is why we exclude prototypes, `this`, closures over mutable state, etc.)
- The verification fragment is erased from both — it exists only in the Loom embedding for proof purposes and is deleted in the TS output.
- Erasure is monotone deletion: `⟦P⟧_ts ⊆ ⟦P⟧_loom` in terms of the computational content.

### 5.3 The Number Problem

JavaScript has one numeric type: IEEE 754 doubles. Dafny, Lean, and most verification systems reason about mathematical integers.

LemmaScript takes a layered approach:

- **`int`**: Mathematical integers. Ghost type. Used in specifications and proofs. Erases to `number` in TS output. The programmer asserts (and must verify) that values stay within safe integer range, or the system inserts overflow checks.
- **`number`**: IEEE 754 doubles. Used in computational code. Verification reasons about the double semantics when needed (rare — most programs don't need floating-point proofs).
- **Bounded integers**: `int32`, `uint8`, etc. — phantom-typed wrappers that carry range invariants. Erase to `number` with verified bounds.

For most programs, the developer writes `number`, the verifier reasons about `int` (mathematical integers), and an automatic side-condition ensures the values stay within `Number.MAX_SAFE_INTEGER`. This is the same trade-off Verus makes with Rust's fixed-width integers.

---

## 6. The Boundary: @lemmafit/contracts

LemmaScript does not require rewriting an entire codebase. It coexists with regular TypeScript through the `@lemmafit/contracts` boundary layer.

```
┌─────────────────────────────────────┐
│         Regular TypeScript          │
│  (unverified, full language)        │
│                                     │
│    ┌───────────────────────────┐    │
│    │   @lemmafit/contracts     │    │
│    │   (runtime enforcement)   │    │
│    │                           │    │
│    │   ┌───────────────────┐   │    │
│    │   │   LemmaScript     │   │    │
│    │   │   (verified,      │   │    │
│    │   │    erases to TS)  │   │    │
│    │   └───────────────────┘   │    │
│    │                           │    │
│    └───────────────────────────┘    │
│                                     │
└─────────────────────────────────────┘
```

- **Inside the LemmaScript boundary**: properties are proved. Zero runtime cost.
- **At the boundary**: contracts enforce that unverified TS interacts correctly with verified LemmaScript modules. Runtime checked in development, optionally stripped in production (with the understanding that the contract violations indicate bugs in the *unverified* code, not the verified code).
- **Outside the boundary**: regular TypeScript. No verification claims. Business as usual.

Developers adopt LemmaScript incrementally: start with contracts on existing code, then rewrite critical modules in LemmaScript when the properties matter enough to prove.

---

## 7. Toolchain

### 7.1 Compiler

```
lsc (LemmaScript Compiler)
  │
  ├── lsc check   — verify (emit Lean, run Loom, report results)
  ├── lsc build   — verify + erase to TypeScript
  ├── lsc erase   — erase only (skip verification, for fast iteration)
  └── lsc prove   — interactive proof mode (open in Lean/VS Code)
```

The compiler is written in TypeScript (dogfooding the ecosystem). The Lean embedding and proof checking require a Lean 4 installation, but `lsc erase` works standalone — letting developers iterate on computational code without waiting for the verifier.

### 7.2 Editor Integration

- **VS Code extension**: syntax highlighting, inline verification status, ghost code dimming, error reporting from Lean
- **LSP**: standard Language Server Protocol for editor-agnostic support
- **Inline proof state**: when SMT fails, show the Lean proof context inline (à la Velvet's InfoView integration)

### 7.3 LLM Integration

When verification conditions can't be discharged by SMT:

1. The unsolved goals are extracted as Lean proof obligations
2. An LLM (via lean-lsp-mcp) attempts to synthesize proof terms
3. Lean checks the synthesized proofs
4. If successful, proofs are cached alongside the source

The LLM is not trusted. Lean is. The LLM proposes; the kernel disposes.

### 7.4 Claude Code / MCP Integration

A LemmaScript MCP server provides tools for AI coding agents:

- `verify_function` — check a LemmaScript function against its spec
- `suggest_spec` — propose pre/postconditions for a function body
- `fill_proof` — attempt to fill in a lemma or proof block
- `explain_failure` — explain why a verification condition failed
- `erase_module` — produce the TypeScript output for a module

---

## 8. Example: Verified Binary Search

```typescript
// binarySearch.ls.ts

ghost function sorted(arr: Array<number>): boolean {
  forall(i, j, 0 <= i && i < j && j < arr.length ==> arr[i] <= arr[j])
}

function binarySearch(arr: Array<number>, target: number): number
  requires sorted(arr)
  requires arr.length > 0
  ensures result >= -1 && result < arr.length
  ensures result >= 0 ==> arr[result] === target
  ensures result === -1 ==> forall(i, 0 <= i && i < arr.length ==> arr[i] !== target)
{
  let mut lo: number = 0
  let mut hi: number = arr.length - 1

  while (lo <= hi)
    invariant 0 <= lo && lo <= arr.length
    invariant -1 <= hi && hi < arr.length
    invariant forall(i, 0 <= i && i < lo ==> arr[i] !== target)
    invariant forall(i, hi < i && i < arr.length ==> arr[i] !== target)
    decreases hi - lo + 1
  {
    const mid = Math.floor((lo + hi) / 2)

    proof {
      assert 0 <= mid && mid < arr.length
      // follows from invariants and loop condition
    }

    if (arr[mid] === target) {
      return mid
    } else if (arr[mid] < target) {
      lo = mid + 1
    } else {
      hi = mid - 1
    }
  }

  return -1
}
```

**After erasure** (`lsc erase binarySearch.ls.ts`):

```typescript
// binarySearch.ts — generated by lsc, do not edit

function binarySearch(arr: Array<number>, target: number): number {
  let lo: number = 0
  let hi: number = arr.length - 1

  while (lo <= hi) {
    const mid = Math.floor((lo + hi) / 2)

    if (arr[mid] === target) {
      return mid
    } else if (arr[mid] < target) {
      lo = mid + 1
    } else {
      hi = mid - 1
    }
  }

  return -1
}
```

Completely ordinary TypeScript. No runtime overhead. The proof existed at build time and is gone.

---

## 9. Scope of the Computational Fragment

### What you can verify (day 1)

- Pure functions over numbers, booleans, strings
- Array algorithms (search, sort, partition, accumulate)
- Object/record manipulation (immutable updates, field access)
- State machines with explicit state types
- Simple control flow: if/else, while, for-of, early return

### What you can verify (later)

- Async/await (via Loom's monad transformer support — the effect is explicit)
- Map/Set operations (with suitable axiomatization)
- Higher-order functions (map, filter, reduce — with contracts on the callback)
- Module-level invariants (enforced across function boundaries)

### What you don't verify (ever)

- DOM manipulation
- Network I/O
- Prototype chains
- Dynamic dispatch
- `eval` and friends

These live outside the LemmaScript boundary. Contracts handle the interface.

---

## 10. Building on Loom

### What Loom provides for free

- Monadic shallow embedding of imperative programs into Lean 4
- Weakest precondition generation via monad transformer algebras
- SMT solver integration (Z3, cvc5) for automated VC discharge
- Support for partial and total correctness, separately or combined
- Nondeterminism (useful for modeling external inputs)
- Lean's full proof automation (grind, aesop, omega, etc.)
- Property-based testing integration (Plausible)
- Machine-checked soundness of the VC generator

### What LemmaScript adds on top

- A TypeScript-flavored surface syntax (parse → Loom embedding)
- Erasure to TypeScript (AST → TS code generation)
- The semantic correspondence argument (LemmaScript ↔ TS)
- Editor tooling and DX
- LLM-assisted proof filling
- @lemmafit/contracts integration at the boundary
- MCP server for AI agent interaction

### Relationship to Velvet

Velvet is one verifier built on Loom. LemmaScript is another. They share the Loom substrate but target different surface languages and different developer communities. Velvet targets Lean developers who want imperative verification. LemmaScript targets TypeScript developers who want verified code that erases to their production language.

---

## 11. Research Contributions

LemmaScript, if realized, would constitute several research contributions:

1. **Verified erasure for a dynamic language.** Verus demonstrated erasure for Rust (a statically typed, ownership-aware language where the semantics are well-understood). LemmaScript does it for a subset of TypeScript, which requires carefully delineating the verifiable fragment and arguing semantic correspondence despite JavaScript's notoriously complex semantics.

2. **Loom as a retargetable verification backend.** Building a second verifier on Loom (after Velvet) validates the framework's claim to generality and exercises its monad transformer algebra in a new setting.

3. **LLM-assisted proof completion in an embedded verifier.** Using LLMs to fill proof obligations in a Loom-based verifier, with Lean as the trust anchor, is a concrete instance of the LLM-verifier interface that is directly relevant to the LICS keynote thesis.

4. **Gradual verification via contracts.** The @lemmafit/contracts boundary layer enables gradual adoption — moving from runtime checking to static verification without rewriting. The formal relationship between the two modes is itself a contribution.

---

## 12. Open Questions

### 12.1 Surface syntax: new file extension or TypeScript superset?

**Option A:** `.ls` files with TypeScript-like syntax plus verification keywords. Requires a custom parser. Clean separation but no existing editor support for free.

**Option B:** `.ls.ts` files that are valid TypeScript (modulo the verification keywords, which could be encoded as decorators or specially-named functions). Leverages existing TS tooling. Uglier encoding of verification constructs.

**Option C:** TypeScript with a compiler plugin that recognizes verification constructs in comments or JSDoc-style annotations. No new syntax at all. Maximum compatibility. Least expressive.

Leaning toward Option A with a dedicated VS Code extension. The verification constructs are too important to hide in comments.

### 12.2 How much of TypeScript's type system do we mirror?

LemmaScript's type system must be *at least* as expressive as the TypeScript types used in the computational fragment, so that erasure produces well-typed TypeScript. But TypeScript's type system is complex (structural subtyping, conditional types, mapped types, template literal types). How much do we need?

Probably: basic structural types, generics, unions, intersections, literal types. Not: conditional types, mapped types, template literal types, declaration merging. The boundary contracts handle the impedance mismatch.

### 12.3 Integer overflow

Most LemmaScript programs will reason about mathematical integers but erase to JavaScript `number`. The mismatch is real: `Number.MAX_SAFE_INTEGER` is 2^53 - 1. Options:

- **Default: automatic safe-integer side conditions.** Every arithmetic operation generates a VC that the result stays within safe integer range. Annoying for large computations but sound.
- **Opt-in: BigInt erasure.** For programs that need true arbitrary precision, erase `int` to `BigInt` instead of `number`. Sound but with performance implications.
- **Explicit bounded types.** `int32`, `uint16`, etc. with modular arithmetic semantics matching typed arrays.

### 12.4 Arrays: mutable or immutable?

Loom/Velvet uses immutable sequences in specifications. JavaScript arrays are mutable. Options:

- **Computational arrays are mutable** (matching JS semantics), with automatic snapshotting for pre-state references in postconditions.
- **Ghost arrays are immutable** (matching Lean `List`/`Array` semantics). The translation between computational mutable arrays and ghost immutable sequences is handled by the embedding.
- **Functional update syntax** for the common case where you're building a new array from an old one.

### 12.5 Proof portability

Proofs are currently Lean 4 tactic scripts. These are fragile across Lean/Loom/mathlib versions. Options:

- Accept fragility (proofs are re-checked on each build anyway)
- Generate proof terms instead of tactic scripts (more stable but harder for LLMs to produce)
- Version-lock Lean/Loom/mathlib in the project (practical but constraining)

### 12.6 Community and ecosystem

LemmaScript sits at the intersection of three communities that rarely overlap: TypeScript developers, formal verification researchers, and LLM/AI tooling builders. The messaging and onboarding must work for all three without alienating any.

---

## 13. Implementation Plan

### Phase 0: Feasibility (Weeks 1–4)

**Goal:** Prove the Loom embedding works for a representative example.

- Take the binary search example from Section 8
- Hand-write the Loom embedding in Lean 4
- Verify it using Loom's infrastructure
- Hand-write the TypeScript erasure
- Document the semantic correspondence argument
- Identify where Loom's current API needs extension

### Phase 1: Core Compiler (Months 2–4)

**Goal:** `lsc check` and `lsc erase` work for a minimal fragment.

- Parser for LemmaScript (subset: functions, if/else, while, let/const, arrays, numbers, booleans)
- AST → Loom embedding (code generation into Lean)
- AST → TypeScript erasure
- Basic error reporting (parse errors, type errors, verification failures)
- 5–10 verified example programs (search, sort, accumulate, state machines)

### Phase 2: Tooling (Months 4–6)

**Goal:** Usable developer experience.

- VS Code extension (syntax highlighting, inline verification status, ghost dimming)
- LLM proof filling via lean-lsp-mcp
- MCP server for Claude Code integration
- @lemmafit/contracts interop (import LemmaScript modules from TS, contracts at boundary)
- `lsc prove` interactive mode

### Phase 3: Language Expansion (Months 6–12)

**Goal:** Cover the useful subset identified by early adopters.

- Generics
- Higher-order functions with contracts
- Object types and structural subtyping
- Match expressions
- Module system
- More comprehensive standard library specifications (Array methods, Math, etc.)

---

## 14. Relationship to Existing Work

| System | Relationship |
|--------|-------------|
| **Verus** | Direct inspiration. Verus is to Rust as LemmaScript is to TypeScript. Key difference: Verus can rely on Rust's ownership model and borrow checker; LemmaScript must define its own discipline for mutable state. |
| **Dafny** | LemmaScript replaces Dafny in LemmaFit's stack for the TypeScript use case. Dafny remains relevant for standalone verification and non-TS targets. |
| **Velvet** | Sibling project built on the same Loom substrate. Velvet validates Loom's design. LemmaScript benefits from Loom improvements driven by Velvet's development. |
| **Loom** | The foundational framework. LemmaScript is a Loom client, like Velvet. |
| **RSC (Refined TypeScript)** | Prior art for TypeScript verification. RSC attempted refinement type inference across the full language. LemmaScript takes a different approach: explicit annotations on a restricted fragment, with full Lean proving power instead of only SMT. |
| **@lemmafit/contracts** | The interop layer. Contracts bridge verified LemmaScript and unverified TypeScript. |
| **ClaimCheck** | Spec auditing for LemmaScript's pre/postconditions. Round-trip formalization validates that specs match developer intent. |
| **VerMCTS** | MCTS-guided proof search could complement LLM-based proof filling for difficult verification conditions. |
| **lean-lsp-mcp** | The bridge between LLMs and Lean's proof engine. LemmaScript's LLM proof filling is a direct client. |

---

## 15. Why Now

Three things have converged:

1. **Loom exists.** Building a verification language from scratch requires years of foundational work — WP calculi, SMT integration, proof infrastructure. Loom gives us all of this as a library. We build the surface language and the erasure, not the verification engine.

2. **LLMs can fill proofs.** The interactive proof obligations that remain after SMT automation were, until recently, the exclusive domain of expert Lean users. LLMs (particularly via lean-lsp-mcp and similar integrations) can now handle many of these automatically, with Lean checking their work. This lowers the barrier from "must know Lean" to "must understand your specification."

3. **TypeScript is the world's most popular language** and has zero verified programming story. The market is not "TypeScript developers who want verification" (tiny, today). The market is "AI agents generating TypeScript that should be trustworthy" (enormous, growing). LemmaScript gives agents a target language where correctness is provable, not just testable.
