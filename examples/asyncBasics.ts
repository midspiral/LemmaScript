/*
 * Async functions (SPEC §4.5). `ensures` describes the fulfillment value;
 * each `await` of a same-file async call reasons against the callee's contract.
 * Locals of value type keep their facts across every suspension.
 */
//@ backend dafny

export async function increment(n: bigint): Promise<bigint> {
  //@ ensures \result === n + 1n
  return n + 1n;
}

export async function addTwice(n: bigint): Promise<bigint> {
  //@ ensures \result === n + 2n
  const once = await increment(n);
  return await increment(once);
}

export async function countUp(n: bigint): Promise<bigint> {
  //@ requires n >= 0n
  //@ ensures \result === n
  let total = 0n;
  let i = 0n;
  while (i < n) {
    //@ invariant 0n <= i && i <= n && total === i
    //@ decreases n - i
    total = await increment(total);
    await undefined;                 // a bare suspension point
    i = i + 1n;
  }
  return total;
}

export async function clampedSum(a: bigint, b: bigint, limit: bigint): Promise<bigint> {
  //@ requires limit >= 0n
  //@ ensures 0n <= \result && \result <= limit
  const x = await addTwice(a);
  const y = await increment(b);
  const sum = x + y;
  if (sum < 0n) return 0n;
  return sum > limit ? limit : sum;
}
