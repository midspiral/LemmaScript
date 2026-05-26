---
title: "Step 7: Adding a Verified Feature"
description: "Walk through the full cycle of adding new verified capabilities to the domain core."
---

## The point of this step

You've built a verified core, audited it, and wired up a UI. Now you want to
add something new. This step walks through the full iteration cycle twice: once
for a simple function, once for something that surfaces a real proof challenge.

## The cycle

Adding a verified feature always follows the same steps:

1. Update DESIGN.md
2. Write the function in domain.ts with annotations
3. Verify (lsc regen → dafny verify → iterate on proofs)
4. Audit (re-run proof review if needed)
5. Use it in the UI

## Feature 1: participantCount

A simple query: how many participants have joined the event?

### Update the design

Add to DESIGN.md under a new query or as part of Family F:

```markdown
`participantCount(e)` returns the number of participants.
Ensures: result equals the length of the participant list.
```

Tell your agent:

> Add a participantCount function to domain.ts. It takes an Event and returns
> the number of participants. Add an ensures that the result equals
> e.participants.length. Then verify.

### What the agent writes

```typescript
export function participantCount(e: Event): number {
  //@ verify
  //@ ensures \result === e.participants.length
  return e.participants.length
}
```

### Verify

```bash
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny src/domain.ts
dafny verify src/domain.dfy
```

This one should auto-discharge: the body directly returns the ensures expression. No proof work needed in the `.dfy` file.

### Use it in the UI

```typescript
function ParticipantBadge({ event }: { event: Event }) {
  return <span>{participantCount(event)} participants</span>
}
```

Simple end-to-end: design → implement → verify → integrate.

## Feature 2: participationRate

Now something more interesting: for a given slot, what percentage of
participants are free there? This introduces arithmetic, a division-by-zero
guard, and multiplication — which is where Dafny gets tricky.

### Update the design

```markdown
`participationRate(e, s)` returns the percentage (0–100) of participants
free at slot s. Ensures: when participants exist, the result equals
(countFree(e.participants, s) * 100) / e.participants.length.
Returns 0 when there are no participants.
```

Tell your agent:

> Add a participationRate function to domain.ts. It takes an Event and a slot
> index, returns an integer 0–100 representing the percentage of participants
> free at that slot. Handle the zero-participants case. Ensure the result
> matches (countFree * 100) / participants.length. Then verify.

### What the agent writes

```typescript
export function participationRate(e: Event, s: number): number {
  //@ verify
  //@ requires e.numSlots >= 0 && 0 <= s && s < e.numSlots
  //@ ensures e.participants.length === 0 ==> \result === 0
  //@ ensures e.participants.length > 0 ==>
  //@   \result === (countFree(e.participants, s) * 100) / e.participants.length
  if (e.participants.length === 0) return 0
  return (countFree(e.participants, s) * 100) / e.participants.length
}
```

### Verify — expect a fight

```bash
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny src/domain.ts
dafny verify src/domain.dfy
```

This is where it gets real. The proof involves multiplication (`* 100`) and
division (`/ participants.length`). As discussed in Step 4, Z3 is
nondeterministic with nonlinear arithmetic. The prover may:

- Fail on the multiplication fact
- Fail to connect `countFree` bounds with the division result
- Pass locally but fail on a re-run

The agent will need to add helper lemmas in `domain.dfy` to guide the prover
through the arithmetic. This might take several iterations — that's expected
and normal for any proof involving multiplication or division.

### Use it in the UI

Once verified:

```typescript
function SlotRate({ event, slot }: { event: Event; slot: number }) {
  const rate = participationRate(event, slot)
  return <span>{rate}% available</span>
}
```

The percentage displayed is provably derived from the verified count. It can
never disagree with the heatmap.

## The pattern

Every new feature follows this cycle:

1. **Design**: add the property to DESIGN.md
2. **Implement**: write the function with annotations in domain.ts
3. **Verify**: regen + dafny verify, iterate on proofs
4. **Audit** (optional): re-run proof review for significant additions
5. **Integrate**: use the verified function in the UI via the hook

Some features verify instantly (`participantCount`). Others require real proof
work (`participationRate`). The cycle is the same either way — the only
variable is how many iterations Step 3 takes.

## What you've done

- Added two verified functions to the domain core
- Experienced instant verification (trivial ensures) and iterative proof work (nonlinear arithmetic)
- Integrated both into the UI through the hook
- Understood the design → implement → verify → integrate cycle for future features

## Next step

The app runs locally with a verified, extensible core. The final step connects
it to a backend for multi-participant use.
