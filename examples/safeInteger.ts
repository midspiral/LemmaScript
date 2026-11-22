// Number.isSafeInteger checks the Number type as well as the numeric range.
// Bigint values return false even when they fit within the Number safe range.

export function isSafeInteger(n: number): boolean {
  //@ ensures \result <==> -9007199254740991 <= n && n <= 9007199254740991
  return Number.isSafeInteger(n);
}

export function isSafeBigInt(n: bigint): boolean {
  //@ ensures !\result
  return Number.isSafeInteger(n);
}

export function integerBoundaries(): boolean {
  //@ ensures \result
  return Number.isSafeInteger(0)
    && Number.isSafeInteger(9007199254740991)
    && Number.isSafeInteger(-9007199254740991)
    && !Number.isSafeInteger(9007199254740992)
    && !Number.isSafeInteger(-9007199254740992)
    && !Number.isSafeInteger(0n)
    && !Number.isSafeInteger(1n)
    && !Number.isSafeInteger(9007199254740991n)
    && !Number.isSafeInteger(9007199254740992n);
}

export function isSafeBigIntQuotient(a: bigint, b: bigint): boolean {
  //@ requires b !== 0n
  //@ ensures !\result
  return Number.isSafeInteger(a / b);
}

// Local mutation makes this a method, whose call must be preserved even
// though Number.isSafeInteger returns false for its bigint result.
export function checkedBigInt(enabled: boolean, n: bigint): bigint {
  //@ requires enabled
  //@ ensures \result === n
  if (!enabled) throw new Error("disabled bigint call");
  let value = n;
  value += 0n;
  return value;
}

export function isSafeBigIntCall(enabled: boolean, n: bigint): boolean {
  //@ requires enabled
  //@ ensures !\result
  return Number.isSafeInteger(checkedBigInt(enabled, n));
}
