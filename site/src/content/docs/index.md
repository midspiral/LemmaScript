---
title: "What is LemmaScript?"
description: "TypeScript with syntax for contracts — an agent writes the contract and the code together, and only correct code ships."
---

<!-- Hand-written homepage (not synced). The repo README syncs to /case-studies/. -->

LemmaScript is **TypeScript with syntax for contracts** — the way TypeScript is
JavaScript with syntax for types. You (or your agent) write ordinary TypeScript and
add `//@ ` annotations stating what a function must do. The `lsc` toolchain
translates the code to a prover — Dafny or Lean 4 — and checks that the
implementation actually meets the spec. Contracts add **zero runtime cost** and work
on **existing codebases**, one function at a time.

It's built agent-first: the agent writes the contract and the implementation
together and iterates until the check passes. You review the contract — a few
declarative lines — instead of the implementation.

## What it looks like

An agent splitting 10 three ways once floored each share and called it done:
`[3, 3, 3]` — that's 9, not 10; a cent vanished. With a contract, that
implementation can't survive:

```typescript
//@ contract Splits total across weights so every unit is accounted for.
//@ requires total >= 0
//@ requires weights.length >= 1
//@ requires forall(k, 0 <= k && k < weights.length ==> weights[k] >= 0)
//@ requires sum(weights) >= 1
//@ ensures sum(\result) === total     // must sum to the whole
function allocate(total: number, weights: number[]): number[] {
  // the floor-and-forget version fails this ensures;
  // the fix hands the leftover back out — and passes
}
```

`lsc check` rejects the buggy version, the agent reads the failure and fixes the
code, and only the correct version surfaces.

## Where to start

- **[Installation](/installation/)** — Node, Dafny, the `lsc` toolchain, and the agent skills
- **[How the loop works](/how-the-loop-works/)** — the concepts in five minutes
- **[Add to an existing codebase](/getting-started/)** — start with one small function

Prefer the full story? Read the [design rationale](/design/), or see what's been
built with it in the [case studies](/case-studies/).
