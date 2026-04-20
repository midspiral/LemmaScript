# LemmaScript (Tech Preview)

A verification toolchain for TypeScript. Write ordinary TypeScript with `//@ ` specification annotations. The toolchain generates verifiable code from your TypeScript — either in Dafny or Lean 4 (with Velvet/Loom).

See [SPEC.md](SPEC.md) and [DESIGN.md](DESIGN.md).

This is a **Tech Preview**: the core idea is there, but support, semantics, and ergonomics are still evolving.

## Examples and Case Studies

Each example and case study is verified in Lean 4 and/or Dafny from the same annotated TypeScript source.

See the internal [examples](examples).

See the external case studies:
- **[collab-todo-lemmascript](https://github.com/midspiral/collab-todo-lemmascript/)** — collaborative task management web app (React + Supabase) with a verified domain model. Single `domain.ts` imported directly by the UI, hooks, and edge functions — no adapter layer. 123 Dafny lemmas (120 in a separate `domain.proofs.dfy`): 16-conjunct invariant preserved across 25 single-project + 3 cross-project actions, NoOp completeness/soundness, initialization. Dafny only.
- **[colorwheel-lemmascript](https://github.com/midspiral/colorwheel-lemmascript/)** — verified color palette generator with mood + harmony constraints. 31 Lean proofs + 18 behavioral properties, 115 Dafny lemmas (invariant preservation, commutativity, NoOp completeness).
- **[clear-split-lemmascript](https://github.com/midspiral/clear-split-lemmascript/)** — greenfield verified expense splitting web app. Conservation theorem, invariant preservation, delta laws — all proven in both Lean (no sorry) and Dafny (56 lemmas).
- **[github-star-checker-lemmascript](https://github.com/midspiral/github-star-checker-lemmascript/)** — small verified CLI that tracks GitHub star counts across repos and reports per-run deltas. Verifies: per-row diff correctness and `totalDiff == sumDiffs(rows)` (via an inductive `SumDiffs_append` lemma); three sign-classified extractors (gainers / losers / unchanged) with soundness, completeness, **ordered completeness** (gainers appear in the notification in the same order they were listed on the command line), and count/sum equalities against prefix-indexed `upTo` helpers; conservation theorem `decompose(r)` — the three splits partition every row exactly once, and `sumDiffs(increases) + sumDiffs(decreases) == totalDiff`. 33 Dafny VCs, 0 errors; proof additions include a head/tail bridge (`sumDiffs` ↔ `sumDiffsUpTo`) and two partition-on-n inductions. Dafny only.
- **[equality-game-lemmascript](https://github.com/midspiral/equality-game-lemmascript/)** — greenfield verified arithmetic equality card game (React + Tailwind). Sound + complete decision procedure for "can these two card lists be combined into equal expressions": `canEqualize(L, R) ⟺ ∃ eL, eR. eval(eL) == eval(eR) ∧ multiset(leaves(eL)) == multiset(L) ∧ same for R`. Algorithm is subset-DP over a bitmask `m ∈ [1, 2^n − 1)`; the proof composes a `PopCount` upper/lower bound chain (with stdlib `LemmaDivDenominator` / `LemmaFundamentalDivModConverse`), a `splitLeft`/`splitRight` ↔ imperative-loop connection, a `WitnessCombine` lemma threading existential `Expr` witnesses through the cross-product loops, and a `ChooseMask` combinatorial constructor that, given any sub-multiset of `cards`, produces the realizing mask. Capped by `CompletenessFromMaskCoverage`. 753 verification conditions, 0 errors, 0 `assume`s, 0 axioms under `--isolate-assertions --verification-time-limit 180`. Dafny only.
- **[node-casbin-lemmascript](https://github.com/midspiral/node-casbin-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [node-casbin](https://github.com/casbin/node-casbin). 5 functions verified, 217 existing tests pass. End-to-end correctness and order independence for all 4 effect modes in both Lean and Dafny (39 lemmas).
- **[hono-lemmascript](https://github.com/midspiral/hono-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [hono](https://github.com/honojs/hono)'s security middleware. Two CVEs verified: IP restriction bypass ([CVE-2026-39409](https://github.com/honojs/hono/security/advisories/GHSA-3mpf-rcc7-5347)) and cookie name bypass ([CVE-2026-39410](https://github.com/honojs/hono/security/advisories/GHSA-r5rp-j6wh-rvv4)) — 51 Dafny lemmas. [Cookie verification done **in-place**](https://github.com/midspiral/hono-lemmascript/blob/lemmascript/src/utils/cookie.ts#L79). Dafny only.
- **[charmchat](https://github.com/CHARM-BDF/charmchat/blob/lemma/README_LemmaScript.md)** — brownfield verification of an AI agent orchestration backend. `isEmptyResult` (string emptiness predicate, 8 postconditions, <1s) and `topologicalSort` (Kahn's algorithm — memory safety, output bounds, completeness via acyclicity ranking witness, termination). Full completeness proof: 23 helper lemmas, 14 opaque ghost predicates, 115 loop invariants; 736 VCs verified under `--isolate-assertions --verification-time-limit 600`. Key technique: snapshot-based inner invariants (`ghost var originalRemDeps := remDeps`) replace the mid-iteration SEEN/UNSEEN split so preservation is frame reasoning against a ghost-constant rather than set-subtraction against mutating state. Dafny only.
- **[xyflow-lemmascript](https://github.com/midspiral/xyflow-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [xyflow](https://github.com/xyflow/xyflow)'s core edge and geometry utilities. 9 functions verified: `addEdge` (dedup — never loses edges, adds at most one), `reconnectEdge` (replace — bounded length), `connectionExists`, `getEdgeCenter` (midpoint correctness), `clamp` (bounds), `rectToBox`/`boxToRect` (field arithmetic), `getBoundsOfBoxes` (enclosure), `getOverlappingArea` (non-negative), `areSetsEqual` (subset + same size). 14 Dafny proof obligations. Dafny only.

## Setup

**Prerequisites:** Node.js >= 18. For the Lean backend: [elan](https://github.com/leanprover/elan). For the Dafny backend: [Dafny](https://github.com/dafny-lang/dafny) >= 4.x.

**Install from npm:**

```sh
npm install lemmascript
```

**Or from source:**

```sh
git clone https://github.com/midspiral/LemmaScript.git
cd LemmaScript && npm install && npm run build
```

**Lean backend** additionally requires the Loom and Velvet forks:

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
```

## Usage

### Dafny backend

```sh
npx lsc gen --backend=dafny src/myModule.ts
npx lsc check --backend=dafny src/myModule.ts
npx lsc regen --backend=dafny src/myModule.ts
```

The Dafny backend generates two files per TS source: `foo.dfy.gen` (always regeneratable) and `foo.dfy` (source of truth, with LLM/user proof additions). The diff between them must be additions-only.

### Lean backend

```sh
npx lsc gen --backend=lean src/myModule.ts
lake build
```

## What's Supported

### Annotations

```typescript
//@ requires arr.length > 0
//@ ensures \result >= -1 && \result < arr.length
//@ invariant 0 <= i && i <= arr.length
//@ decreases arr.length - i
//@ type i nat
```

## File Structure

### Dafny backend

| File | Generated? | Purpose |
|------|-----------|---------|
| `foo.ts` | — | TypeScript source with `//@ ` annotations |
| `foo.dfy.gen` | Yes | Generated Dafny (merge base, always regeneratable) |
| `foo.dfy` | Yes (initial) | Annotated Dafny (gen + proof additions) |

### Lean backend

| File | Generated? | Purpose |
|------|-----------|---------|
| `foo.ts` | — | TypeScript source with `//@ ` annotations |
| `foo.types.lean` | Yes | Lean types, `namespace Pure` defs |
| `foo.spec.lean` | No | Ghost definitions, helper lemmas |
| `foo.def.lean` | Yes | Velvet method definitions |
| `foo.proof.lean` | No | `prove_correct` with proof tactics |

