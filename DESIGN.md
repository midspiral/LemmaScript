# LemmaScript — Design Rationale

**Version:** 0.3
**Date:** March 2026

> For implementation details, see [SPEC.md](SPEC.md).

---

## 1. What This Is

LemmaScript is a verification toolchain for TypeScript. You write ordinary TypeScript with `//@ ` specification annotations. Ghost definitions and proofs live in Lean 4 files. The toolchain generates a Lean method definition from your TypeScript; Lean checks the proof.

There is no new language. There are two languages: TypeScript and Lean. The toolchain bridges them.

The core insight: Verus is to Rust as LemmaScript is to TypeScript — but where Verus embeds specifications in Rust syntax, LemmaScript keeps TypeScript clean and puts the proof machinery in Lean, where it belongs.

---

## 2. Why This Exists

### The JavaScript verification gap

JavaScript and TypeScript have no path to formal verification of functional properties. The options today are:

- **Runtime checking** (assertions, contracts, property-based testing): catches bugs but proves nothing.
- **Refinement types** (RSC, 2016): a research prototype for TypeScript that was never maintained. Restricted to decidable SMT fragments — no induction, no lemmas, no interesting proofs.
- **Model-based verification** (extract to Dafny, verify the model): works, but introduces a semantic gap between the verified model and the production code. The gap is where bugs hide.
- **Dafny's JS backend**: exists, but the runtime baggage (BigInteger emulation, immutable collections, class dispatch) creates a different semantic gap — between what the verifier assumed and what the compiled JS actually does.

### Why not a new language that erases to TypeScript?

An earlier version of this design proposed a "LemmaScript" surface language — a TypeScript subset with verification keywords that erases to plain TS. This was abandoned for three reasons:

1. **Parsing TypeScript is hard.** Even a "subset" of TS syntax is vast and evolving. Building and maintaining a custom parser is a major engineering burden unrelated to verification.
2. **Erasure introduces a trust question.** Does the erased TS faithfully preserve the semantics of the source? With the current approach, the TS *is* the source — there is no erasure.
3. **Three languages.** Developers would need TypeScript, the superset, and enough Lean to debug proof failures. Two languages (TS + Lean) is strictly better.

### The Verus existence proof, adapted

Verus demonstrates that verification annotations can coexist with production code. LemmaScript takes a different cut: instead of embedding specifications *in* the production language and erasing them, we keep specifications *beside* the production code in a language (Lean) that was purpose-built for proofs. The production code is never modified.

---

## 3. Architecture

```
  TypeScript source (.ts)
  with //@ annotations
       │
       ├──→ [ts-morph] Parse AST + extract //@ annotations
       │         │
       │         └──→ [Code Generator] Emit Velvet method definition (.def.lean)
       │                    │
       │                    ├── imports .spec.lean (ghost defs, lemmas)
       │                    │
       │                    └──→ .proof.lean imports .def.lean
       │                          │
       │                          ├──→ loom_solve (automated VC discharge via Z3/cvc5)
       │                          │
       │                          └──→ Lean interactive mode / LLM proof filling
       │
       └──→ TypeScript IS the production output. No erasure.
```

### Key properties

**No erasure, no gap.** The TypeScript source *is* the production code. The `//@ ` annotations are comments — invisible to tsc, bundlers, and the runtime. The `.spec.lean` and `.proof.lean` files never touch the production build.

**Three-file separation.** For each verified function:
- `.def.lean` — generated from TS, always regeneratable
- `.spec.lean` — ghost definitions and lemmas, user-written, version-controlled
- `.proof.lean` — proof tactics, user/LLM-written, version-controlled

Regenerating `.def.lean` from changed TS annotations never destroys proof work.

**The trust question.** Does the generated Lean embedding faithfully model the TypeScript code? This is a one-directional question (TS → Lean) validated by inspection of the code generator. The code generator is a straightforward syntactic translation — it does not optimize, reorder, or transform.

---

## 4. The Computational Fragment

LemmaScript verifies a subset of TypeScript chosen for clean, well-defined semantics that align with Lean/Loom.

### Supported (now)

- Variables: `let`, `const`
- Types: `number` (→ `Int` or `Nat`), `boolean`, `string`, `number[]`
- Control flow: `if`/`else`, `while` (with `break`), `return`
- Functions: named, with typed parameters
- Array access: `arr[i]`, `arr.length`

### Supported (future)

- `for`-of loops
- Object/record types
- Higher-order functions (`map`, `filter`, `reduce`) with contracts
- `async`/`await` (via Loom's monad transformers)
- `Map`/`Set` operations

### Excluded (by design)

- `this` and method dispatch
- Prototypes, classes with inheritance
- Closures over mutable state
- `any`, `unknown`
- Implicit coercions
- `eval`, `with`, dynamic property access

Excluded code lives outside the LemmaScript boundary and interacts through `@lemmafit/contracts`.

---

## 5. The Number Problem

JavaScript has one numeric type: IEEE 754 doubles. Lean and Loom reason about mathematical integers.

LemmaScript models `number` as `Int` by default. The user can annotate variables as `Nat` (`//@ type i nat`) for non-negative values like loop counters and array indices. This determines:
- Lean type declarations (`Int` vs `Nat`)
- Array indexing syntax (`arr[i.toNat]!` vs `arr[i]!`)
- Interaction with ghost functions (which naturally take `Nat` for structural recursion)

For most programs (array algorithms, business logic, state machines), integer reasoning is what you want. The safe-integer question (overflow at 2^53) is deferred — for now, we reason about mathematical integers and trust that production values stay in range.

---

## 6. The Boundary: @lemmafit/contracts

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
│    │   │   + .spec.lean    │   │    │
│    │   │   + .proof.lean)  │   │    │
│    │   └───────────────────┘   │    │
│    │                           │    │
│    └───────────────────────────┘    │
│                                     │
└─────────────────────────────────────┘
```

- **Inside**: properties are proved. Zero runtime cost.
- **At the boundary**: contracts enforce that unverified TS interacts correctly with verified modules.
- **Outside**: regular TypeScript. No verification claims.

Developers adopt incrementally: start with contracts, then add `//@ ` annotations and `.spec.lean` files when the properties matter enough to prove.

---

## 7. Building on Loom and Velvet

### What Loom provides

- Monadic shallow embedding of imperative programs into Lean 4
- Weakest precondition generation via monad transformer algebras
- SMT solver integration (Z3, cvc5) for automated VC discharge
- Support for partial and total correctness
- Lean's full proof automation (grind, aesop, omega, etc.)
- Machine-checked soundness of the VC generator

### What Velvet provides

LemmaScript currently generates Velvet `method` declarations rather than raw Loom programs. Velvet provides:
- `method` / `require` / `ensures` / `invariant` / `done_with` / `decreasing` / `break` syntax
- `prove_correct` command that generates Hoare triple obligations
- `loom_solve` tactic for automated VC discharge

We use a fork of Velvet with one change: obligations persist across files, so `prove_correct` can live in `.proof.lean` while `method` lives in `.def.lean`.

Long term, we may replace Velvet with LemmaScript-native Lean macros for: exact control over proof state, TS-specific constructs, error messages referencing TS source, and independent evolution.

### Relationship to Velvet

Velvet targets Lean developers writing Dafny-style verified programs. LemmaScript targets TypeScript developers who never see Lean. They share the Loom substrate but serve different communities.

---

## 8. LLM Integration

When `loom_solve` can't discharge all verification conditions:

1. Unsolved goals are reported by `lsc check`.
2. An LLM (via lean-lsp-mcp) can propose proof tactics or helper lemmas.
3. Lean checks the LLM's proposals — the LLM is not trusted, only the kernel.
4. Accepted proofs go into `.proof.lean` or `.spec.lean`.

The LLM can help with proof tactics (in `.proof.lean`) and ghost function definitions / lemmas (in `.spec.lean`). It cannot help with missing invariants — those must be added as `//@ invariant` in the TS source and the `.def.lean` regenerated.

---

## 9. Relationship to Existing Work

| System | Relationship |
|--------|-------------|
| **Verus** | Direct inspiration. Verus embeds specs in Rust and erases them. LemmaScript keeps specs beside TypeScript in Lean. Different cut, same goal. |
| **Frama-C / ACSL** | Closest architectural precedent. ACSL puts specs in C comments; Frama-C verifies them. LemmaScript's `//@ ` annotations follow this model. |
| **JML** | External specification for Java. Similar separation of code and specs. |
| **Dafny** | LemmaScript replaces Dafny in LemmaFit's stack for the TypeScript use case. |
| **Velvet** | Sibling project on Loom. LemmaScript currently generates Velvet syntax. |
| **Loom** | The foundational framework. LemmaScript is a Loom client. |
| **RSC** | Prior art for TS verification. LemmaScript uses explicit annotations on a restricted fragment with full Lean proving power, rather than refinement type inference. |
| **@lemmafit/contracts** | The interop layer between verified and unverified TypeScript. |
| **lean-lsp-mcp** | The bridge between LLMs and Lean's proof engine. |

---

## 10. Why Now

Three things have converged:

1. **Loom exists.** Building verification infrastructure from scratch requires years. Loom gives us WP calculi, SMT integration, proof automation, and machine-checked soundness as a library.

2. **LLMs can fill proofs.** The interactive proof obligations that remain after SMT automation were, until recently, the exclusive domain of expert Lean users. LLMs can now handle many of these, with Lean checking their work.

3. **TypeScript is the world's most popular language** and has zero verified programming story. The market is not "TypeScript developers who want verification" (tiny, today). The market is "AI agents generating TypeScript that should be trustworthy" (enormous, growing). LemmaScript gives agents a target where correctness is provable, not just testable.
