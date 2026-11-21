//@ backend dafny

// Real arithmetic is modeled exactly. These checks distinguish integral
// values from fractions before applying the inclusive Number safe range.

export function isSafeReal(x: number): boolean {
  //@ type x real
  //@ ensures \result <==> Math.floor(x) === x && -9007199254740991 <= x && x <= 9007199254740991
  return Number.isSafeInteger(x);
}

export function isSafeQuotient(a: number, b: number): boolean {
  //@ requires b !== 0
  //@ ensures \result ==> -9007199254740991 <= a / b && a / b <= 9007199254740991
  return Number.isSafeInteger(a / b);
}

export function realBoundaries(): boolean {
  //@ ensures \result
  return isSafeReal(0)
    && isSafeReal(9007199254740991)
    && isSafeReal(-9007199254740991)
    && !isSafeReal(9007199254740992)
    && !isSafeReal(-9007199254740992);
}

export function fractionalCases(): boolean {
  //@ ensures \result
  return !Number.isSafeInteger(1.5)
    && !Number.isSafeInteger(-0.5)
    && !Number.isSafeInteger(3 / 2)
    && Number.isSafeInteger(4 / 2)
    && Number.isSafeInteger(0.5 + 0.5)
    && !Number.isSafeInteger(-3 / 2)
    && Number.isSafeInteger(-4 / 2)
    && !Number.isSafeInteger(18014398509481984 / 2);
}

export function checkedHalfStep(enabled: boolean, x: number): number {
  //@ type x real
  //@ type \result real
  //@ requires enabled
  //@ ensures \result === x + 0.5
  if (!enabled) throw new Error("disabled real call");
  let value = x;
  value += 0.5;
  return value;
}

export function isSafeRealCall(enabled: boolean, x: number): boolean {
  //@ type x real
  //@ requires enabled
  //@ ensures x === 0.5 ==> \result
  //@ ensures x === 0 ==> !\result
  return Number.isSafeInteger(checkedHalfStep(enabled, x));
}
