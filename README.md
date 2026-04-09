# LemmaScript (Tech Preview)

A verification toolchain for TypeScript. Write ordinary TypeScript with `//@ ` specification annotations. The toolchain generates verifiable code from your TypeScript — either in Dafny or Lean 4 (with Velvet/Loom).

See [SPEC.md](SPEC.md) and [DESIGN.md](DESIGN.md).

This is a **Tech Preview**: the core idea is there, but support, semantics, and ergonomics are still evolving.

## Examples and Case Studies

Each example and case study is verified in both Lean 4 and Dafny from the same annotated TypeScript source.

See the internal [examples](examples).

See the external case studies:
- **[colorwheel-lemmascript](https://github.com/midspiral/colorwheel-lemmascript/)** — verified color palette generator with mood + harmony constraints. 31 Lean proofs + 18 behavioral properties, 115 Dafny lemmas (invariant preservation, commutativity, NoOp completeness).
- **[clear-split-lemmascript](https://github.com/midspiral/clear-split-lemmascript/)** — greenfield verified expense splitting web app. Conservation theorem, invariant preservation, delta laws — all proven in both Lean (no sorry) and Dafny (56 lemmas).
- **[node-casbin-lemmascript](https://github.com/midspiral/node-casbin-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [node-casbin](https://github.com/casbin/node-casbin). 5 functions verified, 217 existing tests pass. End-to-end correctness and order independence for all 4 effect modes in both Lean and Dafny (39 lemmas).

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
npx lsc gen src/myModule.ts
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

