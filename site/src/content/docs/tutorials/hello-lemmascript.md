---
title: "Hello, LemmaScript"
description: "Write your first verified function and see what success and failure look like."
---

## What you'll learn

- How to annotate a TypeScript function for verification
- What the `gen → verify → fix` loop looks like
- What happens when verification succeeds
- What happens when it fails

## A function worth verifying

Create `src/hello.ts` in your project:

```typescript
export function clamp(value: number, min: number, max: number): number {
  //@ verify
  //@ requires min <= max
  //@ ensures \result >= min && \result <= max
  if (value < min) return min;
  if (value > max) return max;
  return value;
}
```

Three annotations:
- `//@ verify` — tells LemmaScript to include this function
- `//@ requires min <= max` — a **precondition**: this function only makes sense when min ≤ max
- `//@ ensures \result >= min && \result <= max` — a **postcondition**: the return value is always within bounds

These are TypeScript comments. Your code runs exactly the same with or without them.

## Generate and verify

```bash
npx tsx ../LemmaScript/tools/src/lsc.ts gen --backend=dafny src/hello.ts
dafny verify src/hello.dfy
```

Expected:
```
Dafny program verifier finished with 1 verified, 0 errors
```

Dafny just proved that `clamp` always returns a value between `min` and `max`, for every possible input where `min <= max`. Not for a few test cases — for all of them.

## See what failure looks like

Change the postcondition to something wrong:

```typescript
//@ ensures \result > min && \result <= max
```

(`>=` changed to `>` — now we're claiming the result is strictly greater than min, which fails when `value === min`.)

Regenerate and verify:

```bash
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny src/hello.ts
dafny verify src/hello.dfy
```

Dafny will report an error. It found a case where the postcondition doesn't hold. Fix it back to `>=` and re-verify to confirm it passes.

## What just happened

You used three pieces:
1. **Preconditions** (`requires`): what must be true before the function runs
2. **Postconditions** (`ensures`): what the function promises about its return value
3. **The loop**: annotate → generate → verify → fix

This is the same loop you'll use for the real domain model. The difference is scale, not process.

## Clean up

```bash
rm src/hello.ts src/hello.dfy src/hello.dfy.gen
```

## Next step

You'll translate your REQUIREMENTS.md into a `domain.ts` with real types, actions, and verification annotations.
