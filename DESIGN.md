# LemmaScript — Design Rationale

**Version:** 0.4
**Date:** April 2026

> For implementation details, see [SPEC.md](SPEC.md), [SPEC_LEAN.md](SPEC_LEAN.md), [SPEC_DAFNY.md](SPEC_DAFNY.md).
> For internal toolchain architecture, see [TOOLS.md](TOOLS.md).

---

## 1. What This Is

LemmaScript is a verification toolchain for TypeScript. You write ordinary TypeScript with `//@ ` specification annotations. The toolchain generates formal verification artifacts; a backend prover checks them.

There is no new language. There is TypeScript, and there is a prover (Lean or Dafny). The toolchain bridges them.

The core insight: Verus is to Rust as LemmaScript is to TypeScript — but where Verus embeds specifications in Rust syntax, LemmaScript keeps TypeScript clean and puts the proof machinery in a purpose-built prover.

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
3. **Three languages.** Developers would need TypeScript, the superset, and enough Lean to debug proof failures. Two languages (TS + prover) is strictly better.

### The Verus existence proof, adapted

Verus demonstrates that verification annotations can coexist with production code. LemmaScript takes a different cut: instead of embedding specifications *in* the production language and erasing them, we keep specifications *beside* the production code in a language purpose-built for proofs. The production code is never modified.

---

## 3. Two Backends

LemmaScript supports two verification backends:

**Dafny** is the primary backend. It is currently easier for LLMs to verify programs in Dafny than in Lean/Loom/Velvet. This is true, despite a mismatch in tooling where Dafny has a generated stub that needs to be completed to a full verified program. See [SPEC_DAFNY.md](SPEC_DAFNY.md).

**Lean** (via Velvet/Loom) is the secondary backend. It is more powerful for inductive proofs and offers a richer proof language, but automation is harder for LLMs. See [SPEC_LEAN.md](SPEC_LEAN.md).

Both backends share the same TypeScript source, `//@ ` annotations, and pipeline (extract → resolve → transform). They differ only in the emitter and the proof workflow.

---

## 4. Architecture

```
  TypeScript source (.ts)
  with //@ annotations
       │
       ├──→ extract  (ts-morph → Raw IR)
       │         │
       │         └──→ resolve   (types + type-narrowing)
       │                   │
       │                   └──→ narrow  (structural narrowing → someMatch / tagMatch)
       │                             │
       │                             └──→ transform (Typed IR → IR)
       │                                       │
       │                                       └──→ peephole (Some/None cleanup)
       │                                                 │
       │                          ┌──────────────────────┴──────────────────────┐
       │                          │                                             │
       │                     lean-emit.ts                                  dafny-emit.ts
       │                          │                                             │
       │                  .types.lean + .def.lean                          .dfy.gen
       │                     (generated)                                   (generated)
       │                          │                                             │
       │                  .spec.lean + .proof.lean                              .dfy
       │                     (user / LLM)                              (gen + user additions)
       │                          │                                             │
       │                    lake build                                    dafny verify
       │
       └──→ TypeScript IS the production output. No erasure.
```

See [ARCHITECTURE_NARROWING.md](ARCHITECTURE_NARROWING.md) for the
design choices in the resolve/narrow/transform split, and
[TOOLS.md](TOOLS.md) for the implementation surface.

### Key properties

**No erasure, no gap.** The TypeScript source *is* the production code. The `//@ ` annotations are comments — invisible to tsc, bundlers, and the runtime. Proof files never touch the production build.

**Shared pipeline, separate emitters.** Extract, resolve, narrow, and transform are backend-agnostic. Peephole takes a `backend` parameter (some rewrites are Dafny-only — see [TOOLS.md](TOOLS.md#peephole-rules)). The IR uses semantic names (e.g., `arraySet`, `mapGet`) and preserves `Ty` objects — each emitter maps to its own syntax and type system.

**The trust question.** Does the generated embedding faithfully model the TypeScript code? This is a one-directional question (TS → prover) validated by inspection of the code generator. The code generator is a straightforward syntactic translation — it does not optimize, reorder, or transform.

### Lean backend file separation

For each verified function:
- `.types.lean` — generated type definitions, always regeneratable
- `.spec.lean` — ghost definitions and lemmas, user-written, version-controlled
- `.def.lean` — method definition, generated, always regeneratable
- `.proof.lean` — proof tactics, user/LLM-written, version-controlled

Regenerating `.types.lean` and `.def.lean` from changed TS never destroys proof work.

### Dafny backend file separation

For each verified function:
- `.dfy.gen` — generated stub, always regeneratable, merge base
- `.dfy` — source of truth, starts as copy of gen, accumulates proof annotations

Regenerating `.dfy.gen` triggers a three-way merge to preserve user additions in `.dfy`.

**Pure defs are total.** `//@ requires` annotations are emitted on Velvet methods (as `require` clauses) but dropped from Lean `Pure` namespace defs. Pure defs must be total Lean functions — they accept any input, including invalid ones. This is because Pure defs are called from runtime-check functions (e.g., `validExpense` calls `sumTo` to *test* whether shares sum to the amount, before knowing that they do). Dafny handles this differently: its verifier tracks path conditions through if-branches, so a function guarded by a runtime check can satisfy a callee's `requires`.

---

## 5. The Computational Fragment

LemmaScript verifies a subset of TypeScript chosen for clean, well-defined semantics that align with both backends.

### Supported

- Variables: `let`, `const`
- Types: `number` (→ `Int`/`int` or `Nat`/`nat`), `boolean`, `string`
- Arrays: `T[]`, `Array<T>` — access, index assignment (`arr[i] = v`, desugared to `arr.with(i, v)`), length, `with`, `map`, `filter`, `every`, `some`, `includes`, `find`, `push`
- Maps: `Map<K,V>` — `get`, `set`, `has`, `size`
- Sets: `Set<T>` — `has`, `add`, `size`, iteration via `for-of`
- Control flow: `if`/`else`, `while` (with `break`), `for-of`, `return`, `switch`
- Functions: named, with typed parameters, inter-function calls
- Higher-order functions: `map`, `filter`, `every`, `some` with lambda callbacks
- Object/record types: interfaces, discriminated unions, string literal unions
- String operations: `indexOf`, `slice`, `length`
- Ghost state: ghost variables, assertions
- Ternary expressions: `c ? a : b`

### Not yet supported

- Compound pattern matching (nested match on multiple discriminated unions)
- Cross-file type imports
- `async`/`await`

### Excluded (by design)

- `this` and method dispatch
- Prototypes, classes with inheritance
- Closures over mutable state
- `any`, `unknown`
- Implicit coercions
- `eval`, `with`, dynamic property access

---

## 6. The Number Problem

JavaScript has one numeric type: IEEE 754 doubles. Both backends reason about mathematical integers.

LemmaScript models `number` as `Int`/`int` by default. The user can annotate variables as `Nat`/`nat` (`//@ type i nat`) for non-negative values like loop counters and array indices. This determines:
- Backend type declarations (`Int` vs `Nat`, `int` vs `nat`)
- Array indexing syntax (Lean: `arr[i.toNat]!` vs `arr[i]!`)
- Interaction with ghost functions (which naturally take `Nat` for structural recursion)

For most programs (array algorithms, business logic, state machines), integer reasoning is what you want. The safe-integer question (overflow at 2^53) is deferred — for now, we reason about mathematical integers and trust that production values stay in range.

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
│    │   │   + specs/proofs) │   │    │
│    │   └───────────────────┘   │    │
│    │                           │    │
│    └───────────────────────────┘    │
│                                     │
└─────────────────────────────────────┘
```

- **Inside**: properties are proved. Zero runtime cost.
- **At the boundary**: contracts enforce that unverified TS interacts correctly with verified modules.
- **Outside**: regular TypeScript. No verification claims.

Developers adopt incrementally: start with contracts, then add `//@ ` annotations and proof files when the properties matter enough to prove.

---

## 8. Building on Loom and Velvet (Lean backend)

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

## 9. LLM Integration

When automated verification can't discharge all conditions:

1. Unsolved goals are reported by `lsc check`.
2. An LLM (via lean-lsp-mcp or direct Dafny interaction) can propose proof tactics, helper lemmas, or assert statements.
3. The prover checks the LLM's proposals — the LLM is not trusted, only the prover.
4. Accepted proofs go into the appropriate proof files.

The LLM can help with proof tactics and ghost definitions. It cannot help with missing invariants — those must be added as `//@ invariant` in the TS source and the artifacts regenerated.

---

## 10. Relationship to Existing Work

| System | Relationship |
|--------|-------------|
| **Verus** | Direct inspiration. Verus embeds specs in Rust and erases them. LemmaScript keeps specs beside TypeScript in a prover. Different cut, same goal. |
| **Frama-C / ACSL** | Closest architectural precedent. ACSL puts specs in C comments; Frama-C verifies them. LemmaScript's `//@ ` annotations follow this model. |
| **JML** | External specification for Java. Similar separation of code and specs. |
| **Dafny** | One of LemmaScript's verification backends. Also the model for Velvet's design. |
| **Velvet** | Sibling project on Loom. LemmaScript currently generates Velvet syntax for the Lean backend. |
| **Loom** | The foundational framework for the Lean backend. LemmaScript is a Loom client. |
| **RSC** | Prior art for TS verification. LemmaScript uses explicit annotations on a restricted fragment with full proving power, rather than refinement type inference. |
| **@lemmafit/contracts** | The interop layer between verified and unverified TypeScript. |
| **lean-lsp-mcp** | The bridge between LLMs and Lean's proof engine. |

---

## 11. Why Now

Three things have converged:

1. **Loom exists.** Building verification infrastructure from scratch requires years. Loom gives us WP calculi, SMT integration, proof automation, and machine-checked soundness as a library.

2. **LLMs can fill proofs.** The interactive proof obligations that remain after SMT automation were, until recently, the exclusive domain of expert Lean users. LLMs can now handle many of these, with the prover checking their work.

3. **TypeScript is the world's most popular language** and has zero verified programming story. The market is not "TypeScript developers who want verification" (tiny, today). The market is "AI agents generating TypeScript that should be trustworthy" (enormous, growing). LemmaScript gives agents a target where correctness is provable, not just testable.
