# LemmaScript

A verification toolchain for TypeScript. Write ordinary TypeScript with `//@ ` specification annotations; write proofs in Lean 4. The toolchain generates Lean from your TypeScript and Lean checks it.

See [SPEC.md](SPEC.md) for the full specification and [DESIGN.md](DESIGN.md) for why this exists.

## Case Studies

- **[casbin-lemmascript](../casbin-lemmascript/)** — brownfield verification of the [node-casbin](https://github.com/casbin/node-casbin) access control library. 5 functions verified (effector, keyMatch, keyGet, arrayEquals), 217 existing tests pass with verified code wired in.
- **[clear-split-lemmascript](../clear-split-lemmascript/)** — greenfield verified expense splitting web app. React frontend calling verified TS logic directly. Conservation theorem (sum of all balances = 0), invariant preservation, delta laws — all proven, no sorry.

## Setup

**Prerequisites:** [elan](https://github.com/leanprover/elan) (Lean toolchain manager), Node.js >= 18.

**Clone the Loom and Velvet forks:**

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
```

LemmaScript depends on Velvet, which depends on Loom.

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

Builds all examples. First run downloads mathlib cache and Z3/cvc5 (~5 min). Subsequent builds are fast.

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

For each verified function `foo.ts`:

| File | Generated? | Purpose |
|------|-----------|---------|
| `foo.ts` | — | TypeScript source with `//@ ` annotations |
| `foo.types.lean` | Yes | Lean types, `namespace Pure` defs |
| `foo.spec.lean` | No | Ghost definitions, helper lemmas |
| `foo.def.lean` | Yes | Velvet method definitions |
| `foo.proof.lean` | No | `prove_correct` with proof tactics |

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
