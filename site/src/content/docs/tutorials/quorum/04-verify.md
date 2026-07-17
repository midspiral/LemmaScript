---
title: "Step 4: Verify the Domain"
description: "Run the LemmaScript toolchain, read errors, and iterate until proofs pass."
---

## The loop

Verification is iterative. You write annotations, generate Dafny, run the prover, read errors, fix, and repeat. Your agent handles most of this — your job is directing it and understanding what's happening.

## Tell your agent what to do

> Run lsc check on src/domain.ts with the Dafny backend. If verification fails,
> read the errors, fix the annotations or add proof helpers in the .dfy file,
> and re-run until everything passes.

The command:
```bash
lsc check --backend=dafny src/domain.ts
```

This does three things in sequence:
1. Generates `domain.dfy.gen` (the Dafny translation, never edit this) and, on the
   first run, creates `domain.dfy` as a copy of it (the working file where proof
   additions go)
2. Checks that the diff between `domain.dfy` and `domain.dfy.gen` is additions-only
3. Runs `dafny verify domain.dfy`

(Merging after a TypeScript change is `regen`'s job, covered below.)

## What success looks like

```
Dafny program verifier finished with N verified, 0 errors
```

Every `//@ ensures` and `//@ requires` has been proven to hold for all possible inputs. 

## What failure looks like

On the first run, expect many errors. Here's what a real first attempt looks like:

```
Generated: quorum/src/domain.dfy.gen
Created: domain.dfy
Running dafny verify...
domain.dfy(49,0): Error: a postcondition could not be proved on this return path
   |
49 | {
   | ^

domain.dfy(48,44): Related location: this is the postcondition that could not be proved
... +306 lines

57 verified, 40 errors
```

40 errors on the first run is normal. These are proof obligations that need inductive proofs in the `.dfy` file. The agent will iterate: read the errors, add proofs, re-run, repeat. This cycle might take many iterations — that's expected.

Dafny errors point to a specific line in `domain.dfy` and a specific clause that couldn't be proven. Common patterns:

### Postcondition might not hold

```
domain.dfy(42,0): Error: a postcondition might not hold on this return path
```

The prover can't confirm that an `//@ ensures` clause is satisfied. Causes:
- The annotation is wrong (claims something the code doesn't actually do)
- The annotation is right but the prover needs help (an intermediate assertion or a helper lemma)
- The function's logic has a subtle bug

**What to do:** The agent should complete the proof in Dafny properly; push it until it does. It could add proof hints directly in the TypeScript (like `//@ invariant` or `//@ assert`).


### Loop invariant might not hold on entry / might not be maintained

```
domain.dfy(58,0): Error: loop invariant might not hold on entry
domain.dfy(58,0): Error: loop invariant might not be maintained by the loop
```

The loop invariant doesn't hold when the loop starts, or an iteration breaks it.

**What to do:** The agent can add the loop invariant in TypeScript (via `//@ invariant`) or in Dafny. If the agent wrote loops, you could ask it to refactor to recursive functions with `//@ decreases`.

### Assertion might not hold

```
domain.dfy(73,0): Error: assertion might not hold
```

An `//@ assert` that the prover can't discharge.

**What to do:** The assertion may need to be broken into smaller steps, or a helper lemma may be needed in `domain.dfy`. The assertion might even not be needed at all for the end goal.

### Decreases expression might not decrease

```
domain.dfy(30,0): Error: decreases expression might not decrease
```

The prover can't confirm that a recursive function terminates.

**What to do:** Check that `//@ decreases` accurately reflects what shrinks on each call. For a function iterating from `i` to `arr.length`, the decreases expression is `arr.length - i`.

## A real iteration: missing length ensures

Here's a concrete example of the agent iterating. After several rounds, verification is at 82 verified, 10 errors. The agent analyzes the remaining failures:

> The problems are:
> 1. `heatmapUpto` needs a Dafny-level postcondition for its length
> 2. Missing length ensures before index access in `heatmapBatchOrderInvariant`
>    and `heatmapPermInvariant`
> 3. Proof fixes for `maxCount`, `replayPreservesInv`, `countFreeRemoveAt`,
>    `countFreePerm`

The issue: `heatmapBatchOrderInvariant` has an ensures clause that accesses `heatmap(a)[s]`:

```typescript
//@ ensures forall(s, 0 <= s && s < a.numSlots ==> heatmap(a)[s] === heatmap(b)[s])
```

Dafny needs to know that `s` is a valid index into `heatmap(a)`. That requires knowing `heatmap(a).length === a.numSlots`. The `heatmap` function proves this about itself, but because LemmaScript emits ensures as separate lemmas, that fact isn't automatically available here.

The fix: add the length fact directly to the annotations:

```typescript
//@ ensures heatmap(a).length === a.numSlots
//@ ensures heatmap(b).length === b.numSlots
//@ ensures forall(s, 0 <= s && s < a.numSlots ==> heatmap(a)[s] === heatmap(b)[s])
```

The agent then regenerates the Dafny (`regen`) and updates the proof file.

This is the typical pattern: **the code logic is fine, but the formal specification is incomplete.** The agent isn't fixing bugs in behavior — it's adding more specification so that Dafny has every fact it needs to complete the proof. Annotations need to be self-contained: if a function accesses an array at index `s`, the ensures must include the proof that `s` is in bounds.

## The .dfy file: where proofs live

When `lsc check` generates Dafny, it creates two files:

- `domain.dfy.gen` — auto-generated, always regenerated, never edit
- `domain.dfy` — your working file; starts as a copy of `.dfy.gen`

LemmaScript emits each function's `//@ ensures` as a separate `_ensures` lemma in Dafny. Simple ones auto-discharge. Complex ones need proof help: induction steps, intermediate assertions, or helper lemmas. These additions go in `domain.dfy`.

The agent adds proofs to `domain.dfy`. When you later change the TypeScript and regenerate, `lsc regen` does a three-way merge that preserves those proof additions.

**After any TypeScript change, always use regen (not gen):**
```bash
lsc regen --backend=dafny src/domain.ts
```

## Common gotchas

### Nonlinear arithmetic

Z3 (Dafny's solver) is nondeterministic with multiplication. A proof involving `a * b` may pass locally and fail in CI.

**Fix:** Prove multiplication facts with small inductive helper lemmas or with the standard Dafny library instead of relying on Z3 to figure them out.

### Stale .dfy.base

If `regen` produces duplicate declarations or strange merge artifacts, a stale `.dfy.base` file is the cause.

**Fix:**
```bash
rm -f src/domain.dfy.base
```
Then re-run regen.

### Callee ensures not available

LemmaScript emits `ensures` as separate lemmas, not Dafny postconditions. A function can't rely on a callee's `ensures` inside its own body.

**Fix:** Keep the counting kernel total so it composes freely. Discharge callee preconditions structurally. For `ensures` clauses which must be proved by separate lemmas in LemmaScript, you could also try to add them to the functions; they might be simple enough that it works this way with the boosted structure for recursive calls.

## What you've done

- Run `lsc check` on domain.ts for the first time
- Read and interpreted Dafny's error output
- Iterated: fixed annotations or added proof helpers until verification passes
- Understood the two-file system: `.dfy.gen` (generated) vs `.dfy` (with completed proofs)

## Next step

With a verified domain core, you'll build a thin React UI that imports it directly: dispatching Ops and rendering verified outputs.
