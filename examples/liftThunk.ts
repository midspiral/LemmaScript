/**
 * Closure lift, Slice 1 — a void parameterless thunk that captures and mutates
 * enclosing locals, called by name from several sites.
 *
 * `flush` captures `result` (mutated by push) and `pending` (read + reassigned),
 * and is called inside the loop and once at the end. The closure-lift pass lifts it
 * to a top-level routine taking the captures by value and returning the mutated ones
 * as a record, threading that record back at each call site. Without the pass this
 * function is skipped (`Unsupported: multi-statement lambda`).
 */

export function transform(items: number[][]): number[] {
  //@ verify
  let result: number[] = [];
  let pending: number[] = [];
  const flush = () => {
    for (const x of pending) {
      result.push(x);
    }
    pending = [];
  };
  for (const batch of items) {
    for (const x of batch) {
      pending = pending.concat([x]);
    }
    flush();
  }
  flush();
  return result;
}
