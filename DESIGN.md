# LemmaScript — Design Rationale

**Version:** 0.6.x
**Date:** August 2026

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

**Dafny** is the primary backend. It is currently easier for LLMs to verify programs in Dafny than in Lean/Velvet 2. This is true, despite a mismatch in tooling where Dafny has a generated stub that needs to be completed to a full verified program. See [SPEC_DAFNY.md](SPEC_DAFNY.md).

**Lean** (via Velvet 2) is the secondary backend. It is more powerful for inductive proofs and offers a richer proof language, but automation is harder for LLMs. See [SPEC_LEAN.md](SPEC_LEAN.md).

Both backends share the same TypeScript source, `//@ ` annotations, and pipeline (extract → resolve → transform). They differ mainly in the emitter and the proof workflow, with some backend-specific steps in transform and peephole.

---

## 4. Architecture

```
  TypeScript source (.ts)
  with //@ annotations
       │
       ├──→ extract  (ts-morph → Raw IR)
       │         │
       │         └──→ resolve   (types + callback bindings + type-narrowing)
       │                   │
       │                   └──→ narrow  (structural narrowing → someMatch / tagMatch)
       │                             │
       │                             └──→ transform (Typed IR → IR, including callback adaptation)
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

Inline callbacks bind JavaScript's actual arguments during resolve, with all parameter names in scope before defaults initialize them. Literal default closures wait for their captured bindings; initializer computations retain source order. A shared adapter inside transform lowers index/source access to iteration over positions. This keeps lexical binding and unused-argument simplification shared across backends; see [Callback binding and lowering](TOOLS.md#callback-binding-and-lowering).

### Key properties

**No erasure, no gap.** The TypeScript source *is* the production code. The `//@ ` annotations are comments — invisible to tsc, bundlers, and the runtime. Proof files never touch the production build.

**Shared pipeline, separate emitters.** Extract, resolve, and narrow are backend-agnostic. Transform and peephole take a `backend` parameter (some steps are backend-specific — see [TOOLS.md](TOOLS.md#peephole-rules)). The IR retains raw method-name strings (e.g., `push`, `slice`) with their `Ty` objects — each emitter maps those to its own syntax and type system.

**The trust question.** Does the generated embedding faithfully model the TypeScript code? This is a one-directional question (TS → prover). The generator's lowerings, including callback argument binding and adaptation, are part of the trusted translation and must preserve source behavior. Verification checks the generated program; correspondence with TypeScript is assessed through code review and regression tests comparing runtime behavior, generated output, and proof outcomes.

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

**Pure defs are total.** `//@ requires` annotations are emitted on Velvet methods (as `requires` clauses) but dropped from Lean `Pure` namespace defs. Pure defs must be total Lean functions — they accept any input, including invalid ones. This is because Pure defs are called from runtime-check functions (e.g., `validExpense` calls `sumTo` to *test* whether shares sum to the amount, before knowing that they do). Dafny handles this differently: its verifier tracks path conditions through if-branches, so a function guarded by a runtime check can satisfy a callee's `requires`.

---

## 5. The Computational Fragment

LemmaScript verifies a subset of TypeScript chosen for clean, well-defined semantics that align with both backends: the pure, functional core — variables, the primitive types, arrays, maps, sets, ordinary control flow, named and higher-order functions with lambda callbacks, discriminated-union records, ghost state, and ternaries. [SPEC §3](SPEC.md) is the definitive list of supported operations and how each translates.

### Not yet supported

- `await` / true async (an `async` function with no `await` is supported)

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

For most programs (array algorithms, business logic, state machines), integer reasoning is what you want. The safe-integer question (overflow at 2^53) is deferred — for now, we reason about mathematical integers and trust that production values stay in range. [DESIGN_NUMBERS.md](DESIGN_NUMBERS.md) specifies the research and backend gates for an opt-in faithful JavaScript `Number` model.

---

## 7. The Boundary: the runtime guard

LemmaScript does not require verifying an entire codebase. It coexists with regular TypeScript through a runtime guard at the boundary.

```
┌─────────────────────────────────────┐
│         Regular TypeScript          │
│  (unverified, full language)        │
│                                     │
│    ┌───────────────────────────┐    │
│    │   runtime guard           │    │
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

## 8. Building on Velvet 2 (Lean backend)

### The Lean foundation

Velvet 2 builds on Lean's `Std.Internal.Do` framework for weakest preconditions
and Hoare triples, and uses symbolic simplification and grind for VC generation
and discharging. LemmaScript pins its Lean version in `lean-toolchain` and
imports supporting Mathlib tactics and lemmas. The current backend does not
require Loom or external SMT solver binaries.

### What Velvet provides

LemmaScript generates Velvet 2 `method` declarations. Velvet provides:
- `method ... returns (...)` / `requires` / `ensures` / `invariant` / `done_with` / `decreasing` / `break` syntax
- `prove_correct` command that generates Hoare triple obligations
- `velvet_vcgen [methodName] with finish` for VC generation and shared solving

Use the `lemma2` branch of the `namin/velvet` fork as the sibling `../velvet`
checkout; see [setup](README.md#setup). Its persistent method specifications
allow `prove_correct` to live in `.proof.lean` while `method` lives in `.def.lean`.

Long term, we may replace Velvet with LemmaScript-native Lean macros for: exact control over proof state, TS-specific constructs, error messages referencing TS source, and independent evolution.

### Relationship to Velvet

Velvet targets Lean developers writing Dafny-style verified programs. LemmaScript targets TypeScript developers and generates the Velvet layer from annotated TS. Hand-written Lean specifications and proofs remain available when automation needs help.

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
| **Velvet 2** | LemmaScript generates its method syntax and uses its VC generator on top of Lean's `Std.Internal.Do` framework. |
| **Loom** | Framework used by the previous Velvet backend; the current Velvet 2 backend has no Loom dependency. |
| **RSC** | Prior art for TS verification. LemmaScript uses explicit annotations on a restricted fragment with full proving power, rather than refinement type inference. |
| **runtime guard** | The enforcement layer between verified and unverified TypeScript. |
| **lean-lsp-mcp** | The bridge between LLMs and Lean's proof engine. |
