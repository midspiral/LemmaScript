# LemmaScript — Design Document

**Version:** 0.2 (Draft)
**Authors:** Nerd
**Date:** March 2026
**Status:** Early exploration

---

## 1. What This Is

LemmaScript is a verification toolchain for TypeScript. You write ordinary TypeScript with lightweight specification annotations (`//@ requires`, `//@ ensures`, `//@ invariant`). You write proofs and ghost definitions in Lean 4 (using LemmaScript's macro library). The toolchain parses your TypeScript, generates a Loom monadic embedding, and Lean checks everything.

There is no new language. There are two languages: TypeScript and Lean. The toolchain bridges them.

The core insight: Verus is to Rust as LemmaScript is to TypeScript — but where Verus embeds specifications in Rust syntax, LemmaScript keeps TypeScript clean and puts the proof machinery where it belongs: in Lean.

---

## 2. Why This Exists

### The JavaScript verification gap

JavaScript and TypeScript have no path to formal verification of functional properties. The options today are:

- **Runtime checking** (assertions, contracts, property-based testing): catches bugs but proves nothing.
- **Refinement types** (RSC, 2016): a research prototype for TypeScript that was never maintained. Restricted to decidable SMT fragments — no induction, no lemmas, no interesting proofs.
- **Model-based verification** (extract to Dafny, verify the model): works, but introduces a semantic gap between the verified model and the production code. The gap is where bugs hide.
- **Dafny's JS backend**: exists, but the runtime baggage (BigInteger emulation, immutable collections, class dispatch) creates a different semantic gap — between what the verifier assumed and what the compiled JS actually does.

### Why not a new language that erases to TypeScript?

The previous version of this design proposed a "LemmaScript" surface language — a TypeScript subset extended with verification keywords that erases to plain TS. This has three problems:

1. **Parsing TypeScript is hard.** Even a "subset" of TS syntax is vast and evolving. Building and maintaining a custom parser is a major engineering burden that has nothing to do with verification.
2. **Erasure introduces a trust question.** Does the erased TS faithfully preserve the semantics of the source? You have to argue this. With our current approach, the TS *is* the source — there is no erasure.
3. **Three languages.** Developers would need to understand TypeScript, LemmaScript (the superset), and enough Lean to debug proof failures. Two languages (TS + Lean) is strictly better than three.

### The Verus existence proof, adapted

Verus demonstrates that verification annotations can coexist with production code and be erased at compile time. LemmaScript takes a different cut: instead of embedding specifications *in* the production language and erasing them, we keep specifications *beside* the production code in a language (Lean) that was purpose-built for proofs. The production code is never modified.

---

## 3. Architecture

```
  TypeScript source (.ts)
  with //@ annotations
       │
       ├──→ [ts-morph] Parse AST + extract //@ annotations
       │         │
       │         └──→ [Code Generator] Emit Loom monadic embedding (.lean)
       │                    │
       │                    ├── imports *.spec.lean (ghost defs, lemmas, proofs)
       │                    │
       │                    └──→ Lean 4 / Loom checks everything
       │                          │
       │                          ├──→ Z3 / cvc5 (automated VC discharge)
       │                          │
       │                          └──→ Lean interactive mode (when SMT fails)
       │                                │
       │                                └──→ LLM-assisted proof search (lean-lsp-mcp)
       │
       └──→ TypeScript IS the production output. No erasure needed.
```

### Key property: no erasure, no gap

The TypeScript source *is* the production code. The `//@ ` annotations are comments — invisible to the TS compiler, bundlers, and runtime. The `.spec.lean` files never touch the production build. There is no compilation step that could introduce a semantic mismatch between "what was verified" and "what runs in production."

The only trust question is: does the generated Loom embedding faithfully model the TypeScript code's semantics? This is a one-directional question (TS → Lean) that can be validated by inspection of the code generator.

---

## 4. Developer-Facing Surface

### 4.1 TypeScript with `//@ ` annotations

Developers write TypeScript. They add specifications as structured comments:

```typescript
// withdraw.ts

export function withdraw(account: Account, amount: number): Account {
  //@ requires amount > 0
  //@ requires account.balance >= amount
  //@ ensures result.balance === account.balance - amount
  //@ ensures result.balance >= 0
  return { ...account, balance: account.balance - amount }
}
```

```typescript
// binarySearch.ts

export function binarySearch(arr: number[], target: number): number {
  //@ requires sorted(arr)
  //@ requires arr.length > 0
  //@ ensures result >= -1 && result < arr.length
  //@ ensures result >= 0 ==> arr[result] === target
  //@ ensures result === -1 ==> forall(i, 0 <= i && i < arr.length ==> arr[i] !== target)

  let lo = 0
  let hi = arr.length - 1

  while (lo <= hi) {
    //@ invariant 0 <= lo && lo <= arr.length
    //@ invariant -1 <= hi && hi < arr.length
    //@ invariant forall(i, 0 <= i && i < lo ==> arr[i] !== target)
    //@ invariant forall(i, hi < i && i < arr.length ==> arr[i] !== target)
    //@ decreases hi - lo + 1

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

The `//@ ` annotations are the only LemmaScript-specific syntax. They use a small expression language for specifications:

- `requires <expr>` — precondition
- `ensures <expr>` — postcondition (`result` refers to return value)
- `invariant <expr>` — loop invariant
- `decreases <expr>` — termination metric
- `assert <expr>` — inline assertion (for proof guidance)

The expression language supports basic arithmetic, comparisons, logical connectives, array access, `forall`/`exists` quantifiers, and calls to ghost functions defined in `.spec.lean` files.

### 4.2 Lean specification files

Ghost definitions, lemmas, and proofs live in `.spec.lean` files:

```lean
-- binarySearch.spec.lean
import LemmaScript

ghost_fun sorted (arr : Array Int) : Prop :=
  ∀ i j, 0 ≤ i → i < j → j < arr.size → arr[i]! ≤ arr[j]!

ghost_fun arraySum (arr : Array Int) (lo hi : Int) : Int :=
  if lo ≥ hi then 0 else arr[lo]! + arraySum arr (lo + 1) hi

lemma sumNonneg (arr : Array Int) (n : Int)
    (h : ∀ i, 0 ≤ i → i < n → arr[i]! ≥ 0)
    : arraySum arr 0 n ≥ 0 := by
  loom_solve
```

These are plain Lean 4 files using LemmaScript's macro library (`ghost_fun`, etc.). The full power of Lean is available: tactics, mathlib, induction, everything. The Lean LSP provides proof state, autocomplete, and error reporting.

### 4.3 What developers see

```
withdraw.ts              ← TypeScript + //@ annotations (you write this)
withdraw.spec.lean       ← ghost defs, lemmas, proofs (you write this, LLM helps)
.lsc/withdraw.lean       ← generated Loom embedding (don't edit, don't commit)
```

Two files to think about. Two languages. No compilation step that transforms your TypeScript.

---

## 5. The Computational Fragment

### What TypeScript constructs are supported for verification

The code generator (ts-morph → Loom) must understand the TypeScript it reads. The supported fragment:

```typescript
// Variables and bindings
let x: number = 0
const y: string = "hello"

// Primitive types
number                          // IEEE 754 doubles (with integer reasoning mode)
boolean
string

// Compound types
Array<T>                        // arrays
{ field: T, ... }               // object literals (no prototypes)
[T, U, ...]                     // tuples
T | U                           // unions (discriminated)

// Control flow
if / else
while (with //@ invariant)
for (of iterable)
return

// Functions
function f(x: T): U { ... }    // named functions
(x: T): U => { ... }           // arrow functions (no closure over mutable state)

// Modules
import / export
```

**Not supported (code outside these constructs cannot be verified):**

- `this` and method dispatch
- Prototypes, classes with inheritance
- Closures over mutable state
- `any`, `unknown`
- Generators, async/await (future work)
- Implicit coercions
- `eval`, `with`, dynamic property access via string

Unsupported code isn't *forbidden* — it just can't be verified. It lives outside the LemmaScript boundary and interacts through contracts.

---

## 6. Semantic Foundation

### 6.1 Embedding into Loom

The code generator reads TypeScript (via ts-morph) and emits a Loom monadic program in Lean. Loom provides:

- **Monad transformer algebras** for composing effects (state, exceptions, nondeterminism)
- **Weakest precondition generation** via the algebra structure
- **SMT integration** (Z3, cvc5) for automated VC discharge
- **Lean escape hatch** for interactive proofs when SMT fails

The generated `.lean` file contains:
1. The Loom monadic program (the computational semantics of the TS function)
2. Imports of the `.spec.lean` file (ghost definitions, lemmas)
3. The wiring: pre/postconditions from `//@ ` annotations linked to Loom's `triple` infrastructure
4. A `prove_correct` obligation that Lean checks

### 6.2 Semantic Correspondence

The critical question: does the generated Loom embedding faithfully model the TypeScript code?

This is easier to argue than in the previous design (where we had to argue that erasure preserved semantics) because:

- The TS code is the ground truth. The Loom embedding is a *model* of it, not a *translation* of it.
- The model covers only the supported computational fragment (§5), which was chosen specifically because its semantics are well-defined and align with Loom's.
- The code generator is the single point of trust. It can be inspected, tested, and (eventually) verified.

### 6.3 The Number Problem

JavaScript has one numeric type: IEEE 754 doubles. Lean and Loom reason about mathematical integers.

**Approach:**

- The Loom embedding models `number` as mathematical integers (`Int`) by default.
- Automatic side-conditions ensure values stay within `Number.MAX_SAFE_INTEGER` (2^53 - 1).
- The `.spec.lean` file can override the reasoning mode per function or per variable if needed.
- For the rare case of floating-point verification, the embedding can model `number` as `Float` with IEEE 754 semantics (future work).

For most programs (array algorithms, business logic, state machines), integer reasoning is what you want. The safe-integer side-conditions close the gap. This is the same trade-off Verus makes with Rust's fixed-width integers.

---

## 7. The Boundary: @lemmafit/contracts

LemmaScript does not require verifying an entire codebase. It coexists with regular TypeScript through the `@lemmafit/contracts` boundary layer.

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
│    │   │  Verified TS      │   │    │
│    │   │  (//@ annotations │   │    │
│    │   │   + .spec.lean)   │   │    │
│    │   └───────────────────┘   │    │
│    │                           │    │
│    └───────────────────────────┘    │
│                                     │
└─────────────────────────────────────┘
```

- **Inside the verified boundary**: properties are proved. Zero runtime cost.
- **At the boundary**: contracts enforce that unverified TS interacts correctly with verified modules. Runtime checked in development, optionally stripped in production.
- **Outside the boundary**: regular TypeScript. No verification claims.

Developers adopt LemmaScript incrementally: start with contracts on existing code, then add `//@ ` annotations and `.spec.lean` files to critical modules when the properties matter enough to prove.

---

## 8. Toolchain

### 8.1 CLI

```
lsc (LemmaScript Compiler)
  │
  ├── lsc check <file.ts>    — parse TS, generate Loom embedding, verify via Lean
  ├── lsc check --watch       — re-check on file changes
  ├── lsc init                — scaffold .spec.lean file for a TS module
  └── lsc status              — show verification status across project
```

The compiler is a Node.js tool (dogfooding the ecosystem) that orchestrates:
1. **ts-morph** to parse TypeScript and extract `//@ ` annotations
2. **Code generation** to emit `.lsc/*.lean` files (Loom embedding + VC wiring)
3. **Lean/Lake** to check the generated files plus user-written `.spec.lean` files

`lsc check` is the only command most developers run. There is no `build` or `erase` — the TypeScript is already the output.

### 8.2 Editor Integration

- **VS Code extension**: inline verification status (green/red gutters), `//@ ` annotation autocomplete, ghost function name resolution
- **Lean LSP** (standard): proof state, error reporting, autocomplete in `.spec.lean` files — works out of the box, no custom tooling needed
- **Inline proof state**: when SMT fails, the developer opens the `.spec.lean` file and uses Lean's standard InfoView

### 8.3 LLM Integration

When verification conditions can't be discharged by SMT:

1. Unsolved goals are extracted as Lean proof obligations
2. An LLM (via lean-lsp-mcp) attempts to synthesize proof terms
3. Lean checks the synthesized proofs
4. If successful, proofs are written into the `.spec.lean` file

The LLM is not trusted. Lean is. The LLM proposes; the kernel disposes.

### 8.4 Claude Code / MCP Integration

A LemmaScript MCP server provides tools for AI coding agents:

- `verify_function` — run `lsc check` on a specific function
- `suggest_spec` — propose `//@ ` annotations for a function body
- `fill_proof` — attempt to fill a lemma in a `.spec.lean` file
- `explain_failure` — explain why a verification condition failed

---

## 9. Example: Verified Binary Search

### TypeScript source

```typescript
// binarySearch.ts

export function binarySearch(arr: number[], target: number): number {
  //@ requires sorted(arr)
  //@ requires arr.length > 0
  //@ ensures result >= -1 && result < arr.length
  //@ ensures result >= 0 ==> arr[result] === target
  //@ ensures result === -1 ==> forall(i, 0 <= i && i < arr.length ==> arr[i] !== target)

  let lo = 0
  let hi = arr.length - 1

  while (lo <= hi) {
    //@ invariant 0 <= lo && lo <= arr.length
    //@ invariant -1 <= hi && hi < arr.length
    //@ invariant forall(i, 0 <= i && i < lo ==> arr[i] !== target)
    //@ invariant forall(i, hi < i && i < arr.length ==> arr[i] !== target)
    //@ decreases hi - lo + 1

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

### Specification file

```lean
-- binarySearch.spec.lean
import LemmaScript

ghost_fun sorted (arr : Array Int) : Prop :=
  ∀ i j, 0 ≤ i → i < j → j < arr.size → arr[i]! ≤ arr[j]!
```

No lemmas needed for this example — the invariants are strong enough that `loom_solve` (backed by Z3/cvc5) discharges all VCs automatically.

### Generated embedding (build artifact)

```lean
-- .lsc/binarySearch.lean (generated by lsc, do not edit)
import Loom
import «binarySearch.spec»

def binarySearch (arr : Array Int) (target : Int) : LoomM Int := do
  let mut lo := 0
  let mut hi := arr.size - 1
  repeat
    invariant (0 ≤ lo ∧ lo ≤ arr.size)
    invariant (-1 ≤ hi ∧ hi < arr.size)
    invariant (∀ i, 0 ≤ i → i < lo → arr[i]! ≠ target)
    invariant (∀ i, hi < i → i < arr.size → arr[i]! ≠ target)
    decreasing (hi - lo + 1)
    ...
  ...

prove_correct binarySearch by
  loom_solve
```

### What the developer experiences

1. Write `binarySearch.ts` with `//@ ` annotations
2. Run `lsc init binarySearch.ts` → scaffolds `binarySearch.spec.lean` with `sorted` stub
3. Fill in the ghost function definition
4. Run `lsc check binarySearch.ts` → green checkmark
5. Ship `binarySearch.ts` to production. It's just TypeScript.

---

## 10. Scope

### What you can verify (day 1)

- Pure functions over numbers, booleans, strings
- Array algorithms (search, sort, partition, accumulate)
- Object/record manipulation (immutable updates, field access)
- State machines with explicit state types
- Simple control flow: if/else, while, for-of, early return

### What you can verify (later)

- Async/await (via Loom's monad transformer support)
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

## 11. Building on Loom

### What Loom provides

- Monadic shallow embedding of imperative programs into Lean 4
- Weakest precondition generation via monad transformer algebras
- SMT solver integration (Z3, cvc5) for automated VC discharge
- Support for partial and total correctness
- Nondeterminism (useful for modeling external inputs)
- Lean's full proof automation (grind, aesop, omega, etc.)
- Property-based testing integration (Plausible)
- Machine-checked soundness of the VC generator

### What LemmaScript adds

- A TypeScript reader (ts-morph) that extracts control flow and `//@ ` annotations
- Code generation: TS → Loom monadic embedding
- Lean macro library for ghost definitions (`ghost_fun`, etc.)
- The semantic correspondence argument (generated Loom embedding ↔ TS semantics)
- `lsc` CLI for the check/watch/init workflow
- Editor tooling (VS Code extension for `//@ ` annotations)
- LLM-assisted proof filling via lean-lsp-mcp
- @lemmafit/contracts integration at the boundary
- MCP server for AI agent interaction

### Relationship to Velvet

Velvet is a Dafny-style verifier built on Loom. LemmaScript is a TypeScript verifier built on Loom. They share the Loom substrate but target different surface languages and developer communities. Velvet validates Loom's macro-based approach to surface syntax. LemmaScript adapts the pattern: lightweight macros in Lean for `.spec.lean` files, `//@ ` comments in TS for inline annotations.

---

## 12. The Code Generator

The code generator is the critical component and the single point of trust. It reads TypeScript and emits Lean.

### Input

- TypeScript AST (via ts-morph)
- `//@ ` annotations extracted from comments and associated with AST nodes
- Type information from the TypeScript type checker

### Output

- A Lean file containing:
  - Import of Loom and the user's `.spec.lean`
  - A Loom monadic program mirroring the TS function's control flow
  - Pre/postconditions wired from `//@ requires` / `//@ ensures`
  - Loop invariants and decreases clauses wired from `//@ invariant` / `//@ decreases`
  - A `prove_correct` obligation

### Translation rules (sketch)

| TypeScript | Loom embedding |
|-----------|----------------|
| `let x = e` | `let x ← eval e` |
| `let x = e; x = e2; ...` | `let mut x ← eval e; x := eval e2; ...` |
| `if (c) { ... } else { ... }` | `if c then ... else ...` |
| `while (c) { ... }` | `repeat ... invariant ... decreasing ...` |
| `arr[i]` | `arr[i]!` (with bounds VC) |
| `arr[i] = v` | `arr := arr.set i v` |
| `return e` | `return e` (with postcondition VC) |
| `f(x, y)` | `f x y` (with precondition VC) |
| `//@ requires P` | `require P` in Loom spec |
| `//@ ensures P` | `ensure P` in Loom spec |
| `//@ invariant P` | `invariant P` on loop |
| `//@ decreases e` | `decreasing e` on loop |

### What makes this trustworthy

The code generator is a relatively simple syntactic translation. It does not optimize, reorder, or transform. Each TS construct maps to one Loom construct. The generated Lean files are human-readable and inspectable. Over time, the code generator itself could be verified (in Lean, using LemmaScript on its own codebase).

---

## 13. Open Questions

### 13.1 The `//@ ` expression language

The `//@ ` annotations contain expressions (e.g., `forall(i, 0 <= i && i < arr.length ==> arr[i] !== target)`). These must be parsed and translated to Lean. Options:

- **TypeScript-flavored expressions.** Familiar to TS developers. Requires a small expression parser in the code generator.
- **Lean expressions in comments.** No parsing needed — pass through directly. But unfamiliar to TS developers.
- **A minimal shared syntax.** Basic arithmetic, comparisons, `forall`/`exists`, `==>`, and calls to ghost functions. Small enough to be unambiguous, familiar enough to be readable.

Leaning toward the minimal shared syntax. It's a small parser (not a full language), and it avoids exposing TS developers to Lean notation.

### 13.2 Connecting `//@ ` annotations to `.spec.lean`

When an `//@ ` annotation references a ghost function (e.g., `sorted(arr)`), the code generator must resolve it to the Lean definition in the `.spec.lean` file. How?

- **By name.** The ghost function name in the `//@ ` annotation must match the Lean definition name. Simple, probably sufficient.
- **Via a manifest.** A generated mapping file that connects TS names to Lean names. More flexible but more machinery.

Starting with by-name resolution.

### 13.3 Integer overflow side-conditions

When the Loom embedding models `number` as `Int`, every arithmetic operation generates a side-condition that the result fits in `[-2^53+1, 2^53-1]`. This could produce many trivial VCs. Options:

- **Generate all, let SMT handle them.** Simple. SMT is fast on bounded arithmetic.
- **Elide when provably safe.** If the code generator can see that values are bounded (e.g., array indices), skip the side-condition. Reduces noise but adds complexity to the code generator.
- **User opt-out.** An `//@ assume safe_integers` annotation that suppresses overflow checks for a function.

### 13.4 Mutable state model

TypeScript `let` variables are mutable. The Loom embedding must model mutation. Options:

- **StateT.** Each mutable variable becomes part of a state tuple. Matches Velvet's approach.
- **Lean's `let mut`.** Lean 4 supports `let mut` in `do` blocks. Simpler if Loom supports it directly.

Loom already supports `let mut` in its imperative language, so this aligns naturally.

### 13.5 Proof portability

Proofs in `.spec.lean` files are Lean 4 tactic scripts. These are fragile across Lean/Loom/mathlib versions. Options:

- Accept fragility (proofs are re-checked on each build anyway)
- Generate proof terms instead of tactic scripts (more stable but harder for LLMs)
- Version-lock Lean/Loom/mathlib in the project (practical but constraining)

---

## 14. Implementation Plan

### Phase 0: Feasibility (Weeks 1–4)

**Goal:** Prove the TS → Loom embedding works for a representative example.

- Take the binary search example from Section 9
- Hand-write the Loom embedding in Lean 4 (what the code generator would produce)
- Write the `.spec.lean` file with ghost definitions
- Verify using Loom's infrastructure
- Document where Loom's current API needs extension
- Build a minimal ts-morph prototype that parses binary search and extracts `//@ ` annotations

### Phase 1: Code Generator (Months 2–4)

**Goal:** `lsc check` works for a minimal fragment.

- Implement the TS → Loom code generator (ts-morph → Lean emission)
- `//@ ` annotation parser (minimal expression language)
- Lean macro library (`ghost_fun`, etc.)
- Basic error reporting (parse errors, annotation errors, verification failures surfaced from Lean)
- 5–10 verified example programs (search, sort, accumulate, state machines)

### Phase 2: Tooling (Months 4–6)

**Goal:** Usable developer experience.

- VS Code extension (`//@ ` annotation support, inline verification status)
- `lsc init` scaffolding
- `lsc check --watch` mode
- LLM proof filling via lean-lsp-mcp
- MCP server for Claude Code integration
- @lemmafit/contracts interop

### Phase 3: Language Expansion (Months 6–12)

**Goal:** Cover the useful subset identified by early adopters.

- Higher-order functions with contracts
- Object types and structural subtyping
- For-of loops
- Module-level invariants
- More comprehensive standard library specifications (Array methods, Math, etc.)

---

## 15. Relationship to Existing Work

| System | Relationship |
|--------|-------------|
| **Verus** | Direct inspiration. Verus embeds specs in Rust and erases them. LemmaScript keeps specs beside TypeScript in Lean. Different cut, same goal: verified production code with no runtime overhead. |
| **Frama-C / ACSL** | Closest architectural precedent. ACSL puts specs in C comments; Frama-C verifies them. LemmaScript puts lightweight specs in TS comments and heavy proofs in Lean files. |
| **JML** | External specification for Java. Similar separation of code and specs, but JML targets runtime checking more than formal proof. |
| **Dafny** | LemmaScript replaces Dafny in LemmaFit's stack for the TypeScript use case. |
| **Velvet** | Sibling project built on the same Loom substrate. Validates the approach. LemmaScript benefits from Loom improvements driven by Velvet. |
| **Loom** | The foundational framework. LemmaScript is a Loom client, like Velvet. |
| **RSC (Refined TypeScript)** | Prior art for TypeScript verification. RSC attempted refinement type inference across the full language. LemmaScript takes a different approach: explicit annotations on a restricted fragment, with full Lean proving power. |
| **@lemmafit/contracts** | The interop layer. Contracts bridge verified and unverified TypeScript. |
| **lean-lsp-mcp** | The bridge between LLMs and Lean's proof engine. LemmaScript's LLM proof filling is a direct client. |

---

## 16. Why Now

Three things have converged:

1. **Loom exists.** Building verification infrastructure from scratch requires years. Loom gives us WP calculi, SMT integration, proof automation, and machine-checked soundness as a library.

2. **LLMs can fill proofs.** The interactive proof obligations that remain after SMT automation were, until recently, the exclusive domain of expert Lean users. LLMs can now handle many of these, with Lean checking their work. This lowers the barrier from "must know Lean" to "must understand your specification."

3. **TypeScript is the world's most popular language** and has zero verified programming story. The market is not "TypeScript developers who want verification" (tiny, today). The market is "AI agents generating TypeScript that should be trustworthy" (enormous, growing). LemmaScript gives agents a target where correctness is provable, not just testable.
