export async function increment(n: bigint): Promise<bigint> {
  //@ ensures \result === n + 1n
  const x = await Promise.resolve(n);
  return x + 1n;
}

export async function twice(n: bigint): Promise<bigint> {
  //@ ensures \result === n + 2n
  return await increment(await increment(n));
}

export async function eager(n: bigint): Promise<bigint> {
  //@ ensures \result === n
  return n;
}

export async function yieldPlain(n: bigint): Promise<bigint> {
  //@ ensures \result === n
  await undefined;
  return n;
}

export async function recover(): Promise<bigint> {
  //@ ensures \result === 7n
  try {
    await Promise.reject(0n);
    return 3n;
  } catch (reason) {
    return reason === 0n ? 7n : 9n;
  }
}

export async function adoptWithoutCatch(): Promise<bigint> {
  try {
    return Promise.reject(0n);
  } catch {
    return 7n;
  }
}

export async function returnBeforeFinally(): Promise<bigint> {
  //@ ensures \result === 1n
  let n = 1n;
  try {
    return n;
  } finally {
    await undefined;
    n = 2n;
  }
}

export async function finallyOverrides(): Promise<bigint> {
  //@ ensures \result === 5n
  try {
    throw "failure";
  } finally {
    await undefined;
    return 5n;
  }
}

export async function rethrow(): Promise<void> {
  try {
    await Promise.reject(undefined);
  } catch (reason) {
    throw reason;
  }
}

export async function truth(): Promise<boolean> {
  //@ ensures \result
  return true;
}

export async function shortCircuit(enabled: boolean): Promise<boolean> {
  //@ ensures \result === enabled
  return enabled && await truth();
}

export async function repeated(n: bigint): Promise<bigint> {
  //@ ensures \result === 2n * (n + 1n)
  const p = increment(n);
  const a = await p;
  const b = await p;
  return a + b;
}

export async function absolute(p: Promise<bigint>): Promise<bigint> {
  //@ native p
  //@ ensures \result >= 0n
  const value = await p;
  return value < 0n ? -value : value;
}

export async function cleanupBoth(first: Promise<void>, second: Promise<void>): Promise<void> {
  //@ native first second
  try {
    await first;
  } finally {
    await second;
  }
}

export async function positiveOnly(n: bigint): Promise<bigint> {
  //@ requires n > 0n
  //@ ensures \result > 0n
  return n;
}

export async function guarded(n: bigint): Promise<bigint> {
  //@ ensures \result >= 0n
  return n > 0n ? await positiveOnly(n) : 0n;
}
