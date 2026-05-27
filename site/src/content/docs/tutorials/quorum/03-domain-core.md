---
title: "Step 3: Build the Domain Core"
description: "Translate the design document into a verified domain model."
---

## What this step produces

A single file: `src/domain.ts`.
[Sample.](https://github.com/midspiral/quorum-tutorial-lemmascript/blob/main/src/domain.dfy)
This is the verified core. Everything else in the app (UI, network, storage) will import from this file and should never duplicate its logic.

## Tell your agent what to do

With your DESIGN.md in place, tell your agent:

> Read DESIGN.md and create src/domain.ts. Translate the data model into
> TypeScript interfaces, the mutations into an Op union and apply function, and
> the properties into LemmaScript annotations. Follow the conventions: pure recursive functions, total counting kernel, Dafny backend.

## What the agent produces

Since LLMs are non-deterministic, from here on out your output — the exact TypeScript, the annotations, the UI, even the proofs — may differ from ours. However, regardless of the implementation, the core guarantees will hold. 

### Data model → interfaces

The data model from DESIGN.md becomes TypeScript interfaces. For Quorum, the core works in abstract slot indices `[0, numSlots)`:

```typescript
//@ backend dafny

interface Participant {
  id: string;
  name: string;
  avail: boolean[];  // length === numSlots; avail[s] === free at slot s
}

interface Event {
  id: string;
  title: string;
  numSlots: number;
  participants: Participant[];
}
```

No IDs pointing to other tables, no foreign keys. A dense `boolean[]` bitset makes well-formedness trivial: in-range and duplicate-free come for free from `length === numSlots`.

### Family A → the invariant

The well-formedness conditions from DESIGN.md §7 become a `wellFormed` function:

```typescript
function wellFormed(e: Event): boolean {
  //@ verify
  // A1: every participant's avail.length === numSlots
  // A3: numSlots >= 0
}
```

Built from a recursive predicate (`allAvailLen`) that carries a reflection lemma: a caller holding `allAvailLen` recovers the quantified per-participant fact.

### Family B → aggregation functions

The headline promise: the heatmap is the count, and the recommendation is the argmax.

```typescript
//@ ensures \result.length === e.numSlots
//@ ensures forall(s, 0 <= s && s < e.numSlots ==> \result[s] === countFree(e.participants, s))
function heatmap(e: Event): number[]

//@ ensures forall(s, 0 <= s && s < h.length ==> h[s] <= \result)
//@ ensures h.length > 0 ==> exists(s, 0 <= s && s < h.length && h[s] === \result)
function maxCount(h: number[]): number

//@ ensures \result.length === e.numSlots
//@ ensures forall(s, 0 <= s && s < e.numSlots ==>
//@           \result[s] === (heatmap(e)[s] === maxCount(heatmap(e)) && maxCount(heatmap(e)) > 0))
function isBest(e: Event): boolean[]
```

The counting kernel (`freeAt`, `countFree`) is total: no preconditions, so it composes freely inside other verified functions.

### Mutations → Op + apply

Each mutation from DESIGN.md becomes an Op variant. `apply` preserves the invariant:

```typescript
type Op =
  | { kind: "join"; id: string; name: string; avail: boolean[] }
  | { kind: "setAvail"; pid: string; newAvail: boolean[] }
  | { kind: "remove"; pid: string }

//@ verify
//@ requires wellFormed(e)
//@ ensures wellFormed(\result)
function applyOp(e: Event, op: Op): Event
```

### Family C → monotonicity lemmas

Relational properties use the pure-carrier technique: the TypeScript body is `return true`, and the real proof work happens in the generated `.dfy` file.

```typescript
//@ requires wellFormed(e) && p.avail.length === e.numSlots
//@ ensures forall(s, 0 <= s && s < e.numSlots ==>
//@           heatmap(addParticipant(e, p))[s] >= heatmap(e)[s])
function heatmapMonotoneUnderJoin(e: Event, p: Participant): boolean { return true; }
```

### Family D → convergence

The headline: `countFree` is a homomorphism, so participant order doesn't affect the heatmap.

```typescript
//@ ensures countFree(xs.concat(ys), s) === countFree(xs, s) + countFree(ys, s)
function countFreeConcat(xs: Participant[], ys: Participant[], s: number): boolean { return true; }
```

## Review the output

Before verifying, check domain.ts against DESIGN.md:

- Do the interfaces match §5?
- Does the invariant encode the conditions from §7 Family A?
- Do the `ensures` annotations match the property spec sketches?
- Are all functions pure and recursive (no loops)?
- Is the counting kernel total (no preconditions on `countFree`, `freeAt`)?

Tell the agent to adjust before moving on.

## What you've done

- Generated `src/domain.ts` from the design document
- Translated the data model into TypeScript interfaces
- Encoded the invariant, aggregation, mutations, and relational properties as LemmaScript annotations
- Reviewed the output against DESIGN.md

## Next step

You'll run the LemmaScript toolchain on domain.ts: generate Dafny, verify, and iterate until the proofs pass.
