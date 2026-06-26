/**
 * Lean gate for the targeted closure lift (DESIGN_CLOSURE_TARGET.md §6).
 *
 * This is the *post-lift* shape, written by hand (the lift pass doesn't exist yet):
 * a record-returning routine with a loop — which emits as a Velvet `method` returning
 * a structure — that is called from a loop-bearing caller threading the returned state
 * back into its own mutable locals. The open question was whether loom threads exactly
 * this (record return + call from inside a `for … do`). If `lake build` is green, it does.
 */

interface FlushState { result: number[]; pending: number[] }

/** The lifted thunk: captured state in by value, mutated state out as a record.
 *  A record-returning method carrying a postcondition through its loop. */
export function flush(result: number[], pending: number[]): FlushState {
  //@ verify
  //@ ensures \result.result.length >= result.length
  let out = result;
  for (const x of pending) {
    //@ invariant out.length >= result.length
    out = out.concat([x]);
  }
  return { result: out, pending: [] };
}

/** The loop-bearing caller: at each boundary, call flush and thread the record back. */
export function transform(items: number[][]): number[] {
  //@ verify
  let result: number[] = [];
  let pending: number[] = [];
  for (const batch of items) {
    for (const x of batch) {
      pending = pending.concat([x]);
    }
    const s = flush(result, pending);
    result = s.result;
    pending = s.pending;
  }
  return result;
}
