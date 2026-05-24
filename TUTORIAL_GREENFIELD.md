# Building a verified web app with LemmaScript

A short, opinionated recipe. Three moves carry it: **write the domain core first and verify
it**, **keep the UI a thin layer over it**, and **put a swappable store between them** so
local ↔ remote (real multi-device sync) is a one-line change. This is the recipe behind
[`quorum-lemmascript`](https://github.com/midspiral/quorum-lemmascript), generalized for your
own app.

You'll likely drive the proof work with an agent — the inductive `.dfy` lemmas are exactly
the kind of grind it's good at. Keep it on a tight `lsc check` loop and it stays honest.

---

## 1. Find the answer, then model it as a pure core — *first*

Before any UI, ask: **what does my app compute that users act on?** A scheduler's heatmap, a
budget's balances, a poll's winner, a board's ordering. That aggregate — and the state
transitions that feed it — is your verified core. Put it in one `domain.ts` of pure
functions over plain data:

```ts
//@ backend dafny
export interface State { /* your model, as plain data */ }
export type Op = /* the mutations, as a discriminated union of data */

// The state machine: one pure transition, total where you can manage it.
export function apply(s: State, op: Op): State {
  //@ verify
  //@ requires inv(s)
  //@ ensures inv(\result)            // every transition preserves the invariant
  ...
}

// The answer users act on — characterized exactly, not just "computed".
export function summary(s: State): Answer {
  //@ verify
  //@ ensures /* a precise property: counts, bounds, argmax, round-trip, ... */
}
```

Verify this **before** writing a line of UI. The payoff is a contract you can build on: every
value the app later renders traces back to a proven function.

Conventions that keep proofs smooth (LemmaScript turns each `//@ ensures` into a *separate*
lemma, which a pure function can't call):

- **Pure recursive functions, not imperative loops** — loops can't take proof hints; the
  recursive shape composes with hand-written induction.
- **Keep core functions total** (precondition-free) where you can — total functions compose
  inside other verified functions; precondition-laden ones force lemma plumbing at every call.
- Discharge the inductive `*_ensures` lemmas in the companion `.dfy` (the generated `.dfy.gen`
  is never edited; your proofs are additions to `.dfy`).

## 2. Choose the verification boundary on purpose

You are **not** verifying the whole app — you're verifying the *meaning of the answer*.
Verify: the state transitions, the invariant, the aggregate, any codec you export through.
Trust (and say so, in a DESIGN doc): the UI, the network/storage I/O, serialization, and any
real-world labeling (dates, timezones, currency formatting). A verified core + a thin trusted
shell is the shape; getting that line right is most of the value. Don't claim
"verified end-to-end" — claim exactly what you proved.

## 3. Make the UI a thin layer

The UI does two things only: **turn user actions into `Op`s**, and **render what the verified
functions return**. No counting, ranking, or invariant logic in components — they call the
core. A single hook is a good home for the verified-function calls:

```ts
function useApp(store: Store) {
  const state = useSyncExternalStore(store.subscribe, store.getSnapshot)
  return {
    state,
    answer: summary(state),              // verified
    act: (op: Op) => store.dispatch(op), // the only way state changes
  }
}
```

If you ever find domain math creeping into JSX, push it back into `domain.ts` and prove it.

## 4. Put a swappable store between UI and state

This is the seam that makes everything else flexible. Define one tiny interface; the UI talks
only to it:

```ts
export interface Store {
  getSnapshot(): State
  subscribe(fn: () => void): () => void
  dispatch(op: Op): void   // the ONE place that calls the verified apply()
}
```

Then write two implementations behind the same interface:

- **Local store** — `dispatch(op)` = `apply(state, op)` → persist (`localStorage`) → notify.
  Perfect for dev, offline, and a single-device MVP.
- **Remote store** — `dispatch(op)` applies `apply` locally (optimistic, instant) **and**
  sends the op to the server; server broadcasts authoritative state, which the store adopts.

Because the UI only knows the interface, switching is one branch in your `createStore`/`load`
entry points (gate it on a build flag). The UI never changes.

## 5. Run the same core on the server

For real multi-device sync, the server holds the authoritative state and **imports the same
`domain.ts`** — it applies the *same* verified `apply()`. One core, client and server, no
second implementation and no drift. A Cloudflare **Durable Object** is an excellent fit: one
DO per "room"/document, single-threaded (a free total order), with a hibernatable WebSocket
fan-out.

```
Browser ── Store (remote) ──WebSocket──▶ Worker ─▶ Durable Object (one per room)
  optimistic apply() + send op                       canonical state; applies apply(); broadcasts
```

The big payoff, *if your transitions converge*: when concurrent ops commute (or resolve
last-writer-wins) — **and you've proven it** — the client can apply optimistically and the
server authoritatively with **no rollback and no operational transform**. The convergence
proof is what licenses the lock-free design. (If you can't prove convergence, fall back to
server-authoritative-only: `dispatch` just sends, and the UI renders broadcasts.)

## The loop

```sh
# write TS with //@ annotations, then:
lsc check  --backend=dafny src/domain.ts     # gen + verify; discharge inductive proofs in .dfy
lsc regen  --backend=dafny src/domain.ts     # after TS changes (merges your proof additions)
```

Wire CI to run `check.sh dafny` over a `LemmaScript-files.txt` manifest so the proofs (and the
"`.dfy.gen` hasn't drifted from the TS" check) run on every push.

Three gotchas worth knowing up front:

- **Nonlinear arithmetic is flaky.** A bare `assert a*b >= 0` can verify locally and fail in
  CI (Z3 is nondeterministic). Prove multiplication facts with tiny **inductive helper
  lemmas** instead — deterministic, and they pass `--isolate-assertions`.
- **`regen` duplicating declarations?** A stale `*.dfy.base` (the merge anchor) is the cause —
  `rm` it and re-run.
- **Not everything is expressible** in `//@` specs (e.g. no `multiset`). Find the strongest
  *statable* property, prove that, and note the gap.

---

That's it: a verified `domain.ts`, a thin UI that only renders its outputs, and a store seam
that swaps local for a same-core server. Build the core until it's solid; the app then grows
on top of it without ever putting the trustworthy logic at risk.
