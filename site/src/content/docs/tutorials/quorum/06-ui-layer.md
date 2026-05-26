---
title: "Step 6: The UI Layer"
description: "Build a thin React frontend that dispatches operations and renders verified outputs."
---

## The rule

The UI has two jobs:

1. Turn user actions into `Op`s
2. Render what the verified functions return

No counting, ranking, or domain logic in components. If you find yourself computing something in JSX, push it into `domain.ts` and verify it.

## Tell your agent what to do

> Set up a React + Vite + TypeScript project. Create a UI for Quorum: a
> scheduling grid where participants paint their availability and a live
> heatmap shows per-slot counts with best-time highlighting. Import from
> domain.ts: initEvent, applyOp, heatmap, isBest, and the view functions.
> Use a local store for now — hold the Event in React state via
> useSyncExternalStore. Follow the store seam pattern from DESIGN.md.

## The store seam

The greenfield pattern puts a small interface between the UI and the domain core. The UI only talks to this interface:

```typescript
interface Store {
  getSnapshot(): Event
  subscribe(fn: () => void): () => void
  dispatch(op: Op): void
}
```

`dispatch` is the only place that calls the verified `applyOp`. Today you implement a `LocalStore` (in-memory + localStorage). Later, a `RemoteStore` (WebSocket to a server) implements the same interface with no UI changes.

## What the agent produces

### The hook

A single hook wraps the store and exposes verified outputs:

```typescript
function useQuorum(store: Store) {
  const event = useSyncExternalStore(store.subscribe, store.getSnapshot)
  return {
    event,
    heatmap: heatmap(event),       // verified: exact per-slot counts
    best: isBest(event),           // verified: exact argmax mask
    dispatch: store.dispatch,
  }
}
```

This is the only module that calls the verified read functions. Components receive the results and render them — they never call `heatmap` or `isBest` themselves.

### Components render verified outputs

A grid cell renders the heatmap count and best-slot highlighting:

```typescript
function GridCell({ count, isBest }: { count: number; isBest: boolean }) {
  return (
    <div className={isBest ? 'best' : ''}>
      {count}
    </div>
  )
}
```

The `count` came from `heatmap(event)[s]`. The `isBest` came from `isBest(event)[s]`. The component has zero domain logic.

### Actions are data

When a participant paints availability, the component builds an Op:

```typescript
function handlePaint(participantId: string, newAvail: boolean[]) {
  dispatch({ kind: 'setAvail', pid: participantId, newAvail })
}
```

The button doesn't compute anything. It creates data (an Op) and hands it to the store, which calls the verified `applyOp`.

## What to check

After the agent builds the UI:

- Does `dispatch` go through the store, which calls `applyOp` and nothing else?
- Is the hook the only caller of `heatmap`, `isBest`, and other verified queries?
- Is there any counting, filtering, or comparison logic in the components?
- Does the store seam exist as a clear interface (not inlined into components)?

If domain logic crept into JSX, push it back into `domain.ts`.

## What you've done

- Set up a React + Vite project with the verified domain as its core
- Created a store seam: one interface, one local implementation for now
- Built a hook that exposes verified outputs (heatmap, best mask)
- Components render only what verified functions return
- Actions flow as data through the store to `applyOp`

## Next step

The app works locally. Next, you'll connect it to a backend so multiple participants can use the same event.
