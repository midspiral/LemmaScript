# LemmaScript

A verification toolchain for TypeScript. Write ordinary TypeScript with `//@ ` specification annotations; write proofs in Lean 4. The toolchain generates Lean from your TypeScript and Lean checks it.

See [DESIGN.md](DESIGN.md) for why this exists and [SPEC.md](SPEC.md) for the implementation specification.

## Setup

**Prerequisites:** [elan](https://github.com/leanprover/elan) (Lean toolchain manager), Node.js ≥ 18.

**Clone with the Velvet fork:**

```sh
git clone https://github.com/namin/velvet.git -b lemma ../velvet
```

LemmaScript depends on Velvet (which depends on Loom). The fork has one change: `prove_correct` works across files.

**Install Node.js dependencies:**

```sh
cd tools && npm install
```

## Usage

**Generate Lean from TypeScript:**

```sh
cd tools
npx tsx src/lsc.ts gen ../examples/binarySearch.ts
```

This produces `binarySearch.types.lean` (if the TS has type declarations) and `binarySearch.def.lean` next to the TS file.

**Verify with Lean:**

```sh
lake build
```

Builds all examples. First run downloads mathlib cache and Z3/cvc5 (~5 min). Subsequent builds are fast (~5s per file).

## File Structure

For each verified function `foo.ts`:

| File | Generated? | Purpose |
|------|-----------|---------|
| `foo.ts` | — | TypeScript source with `//@ ` annotations |
| `foo.types.lean` | Yes (gitignored) | Lean types from TS type declarations |
| `foo.spec.lean` | No | Ghost definitions, helper lemmas |
| `foo.def.lean` | Yes (gitignored) | Velvet method definition |
| `foo.proof.lean` | No | `prove_correct` with proof tactics |

The user writes `.spec.lean` and `.proof.lean`. The codegen produces `.types.lean` and `.def.lean`.

## Examples

| Example | Pattern |
|---------|---------|
| `binarySearch` | Array search, break, Int arithmetic |
| `linearSearch` | Loop with break, Nat index |
| `arraySum` | Accumulator, recursive ghost function |
| `transition` | State machine, enum ADT, inter-method call |
| `packet` | Discriminated union with data, if-chain → match |
