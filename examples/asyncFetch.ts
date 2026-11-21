/*
 * Awaiting external I/O in a loop, and promise parameters (SPEC §4.5).
 *
 * `fetchSize` is an impure extern: every call may return a different size, but
 * each satisfies its contract. The loop iterates a fresh copy of `ids`; looping
 * over `ids` itself while awaiting would be rejected, because the array iterator
 * would observe another task's mutations during a suspension.
 *
 * A promise parameter is modeled by its fulfillment value: a settled promise
 * never changes, so awaiting it twice yields the same value.
 */
//@ backend dafny

//@ extern
//@ impure
//@ ensures \result >= 0
export async function fetchSize(id: number): Promise<number> {
  return 0;  // the real implementation queries a remote store
}

export async function totalSize(ids: readonly number[], budget: number): Promise<number> {
  //@ requires budget >= 0
  //@ ensures 0 <= \result && \result <= budget
  let total = 0;
  for (const id of [...ids]) {
    //@ invariant 0 <= total && total <= budget
    const size = await fetchSize(id);
    if (total + size > budget) return budget;
    total = total + size;
  }
  return total;
}

export async function doubled(p: Promise<bigint>): Promise<bigint> {
  //@ ensures \result === 2n * p
  const first = await p;
  const second = await p;
  return first + second;
}

export async function doubledLater(p: Promise<bigint>): Promise<bigint> {
  //@ ensures \result === 2n * p
  await undefined;
  return await doubled(p);
}
