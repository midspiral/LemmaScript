---
title: "How the loop works"
description: "Contracts, checks, and iteration — the concepts behind LemmaScript in five minutes, no setup required."
---

<!-- Hand-written manual page (concepts; no setup needed). -->

Four ideas explain almost everything else in these docs.

## 1. A contract is the function's API for correctness

Above a function, `//@ ` annotations state what it needs and what it promises:

```typescript
//@ contract Never lets the charge exceed the available balance.
//@ requires balance >= 0
//@ requires amount >= 0
//@ ensures amount <= balance ==> \result === balance - amount
//@ ensures amount > balance ==> \result === 0
function charge(balance: number, amount: number): number { /* … */ }
```

- `requires` — what callers must guarantee coming in
- `ensures` — what the function guarantees going out (`\result` is the return value)
- `contract` — the same promise in plain English, for the human reviewer

These are the three you'll see most. The full annotation list is in
[the specification](/spec/#2-the---annotation-language).

The implementation stays ordinary TypeScript. Contracts are comments, so they cost
nothing at runtime and change nothing about how the code builds or ships.

## 2. `lsc check` decides, it doesn't sample

Testing runs the code on chosen inputs; `lsc check` translates the function and its
contract to a prover (Dafny by default) and asks whether the implementation meets
the spec **for every input the contract admits**. The answer is a verdict, not a
survey: correct, or not correct yet — with the failing obligation to point at.

The two do different jobs, and both matter: contracts settle the core logic;
tests remain the right tool for integration, I/O, and everything outside the
verified boundary.

## 3. "Not correct yet" is a loop state, not a bug report

When a check fails, either the code doesn't do what the contract says, or the
contract doesn't say what you meant. The loop is: adjust one of them, re-run,
repeat. Agents drive this loop well — with the
[skills](https://github.com/midspiral/lemmascript-skills) installed, an agent writes the contract and the code
together and iterates until the check passes, so what surfaces is correct code.
Your job shifts to reviewing the contract: a few declarative lines that say
exactly what was guaranteed.

## 4. Generated files carry the proof work

For the Dafny backend, `lsc` writes two files next to your source: `foo.dfy.gen`
(always regeneratable — never edit) and `foo.dfy` (yours — helper lemmas and proof
additions accumulate here; the difference from `.dfy.gen` must be additions-only,
and `lsc check` enforces that). After editing the TypeScript, `lsc regen`
three-way-merges the new generated code into `foo.dfy` so proof work is never lost.
Precise rules live in the [Dafny backend spec](/spec-dafny/).

## Next

- [What TypeScript is supported](/subset/) — the subset the prover understands
- [CLI reference](/reference/cli/) — every command in the loop
