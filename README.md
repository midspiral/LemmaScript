# LemmaScript

A verification toolchain for TypeScript. Write ordinary TypeScript with `//@ ` specification annotations. The toolchain generates verified code from your TypeScript — either Lean 4 (with Velvet/Loom) or Dafny (with Z3).

See [SPEC.md](SPEC.md) for the full specification, [DESIGN.md](DESIGN.md) for the Lean backend design, and [DESIGN_DAFNY.md](DESIGN_DAFNY.md) for the Dafny backend design.

## Case Studies

- **[casbin-lemmascript](https://github.com/midspiral/casbin-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of the [node-casbin](https://github.com/casbin/node-casbin) access control library. 5 functions verified (effector, keyMatch, keyGet, arrayEquals), 217 existing tests pass with verified code wired in.
- **[clear-split-lemmascript](https://github.com/midspiral/clear-split-lemmascript/)** — greenfield verified expense splitting web app. React frontend calling verified TS logic directly. Conservation theorem (sum of all balances = 0), invariant preservation, delta laws — all proven, no sorry.
- **[colorwheel-lemmascript](https://github.com/midspiral/colorwheel-lemmascript/)** — verified color palette generator with mood + harmony constraints. 30 functions, all proved with `loom_solve`.

## Setup

**Prerequisites:** Node.js >= 18. For the Lean backend: [elan](https://github.com/leanprover/elan). For the Dafny backend: [Dafny](https://github.com/dafny-lang/dafny) >= 4.x.

**Install Node.js dependencies:**

```sh
cd tools && npm install
```

**Lean backend** additionally requires the Loom and Velvet forks:

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
```

## Usage

### Lean backend (default)

```sh
# generate .def.lean
npx tsx tools/src/lsc.ts gen examples/binarySearch.ts
# verify with Lean
lake build
```

### Dafny backend

```sh
# generate .dfy.gen + .dfy
npx tsx tools/src/lsc.ts gen --backend=dafny examples/binarySearch.ts
# verify (--standard-libraries needed if file uses Seq.Map/Filter/All)
npx tsx tools/src/lsc.ts check --backend=dafny examples/binarySearch.ts
# regen with patch support after TS changes
npx tsx tools/src/lsc.ts regen --backend=dafny examples/binarySearch.ts
```

The Dafny backend generates two files per TS source: `foo.dfy.gen` (always regeneratable) and `foo.dfy` (source of truth, with LLM/user proof additions). The diff between them must be additions-only.

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

### Lean backend

| File | Generated? | Purpose |
|------|-----------|---------|
| `foo.ts` | — | TypeScript source with `//@ ` annotations |
| `foo.types.lean` | Yes | Lean types, `namespace Pure` defs |
| `foo.spec.lean` | No | Ghost definitions, helper lemmas |
| `foo.def.lean` | Yes | Velvet method definitions |
| `foo.proof.lean` | No | `prove_correct` with proof tactics |

### Dafny backend

| File | Generated? | Purpose |
|------|-----------|---------|
| `foo.ts` | — | TypeScript source with `//@ ` annotations |
| `foo.dfy.gen` | Yes | Generated Dafny (merge base, always regeneratable) |
| `foo.dfy` | Yes (initial) | Annotated Dafny (gen + proof additions) |

## Examples

| Example | Pattern |
|---------|---------|
| `binarySearch` | Array search, break, Int arithmetic |
| `linearSearch` | Loop with break, Nat index |
| `arraySum` | Accumulator, recursive ghost function |
| `transition` | State machine, enum ADT, inter-method call |
| `packet` | Discriminated union with data, if-chain → match |
| `isSorted` | Loop with break, existential in invariant |
| `maxElement` | If-without-else in loop |
| `arrayContains` | For-of loop, boolean flag |
