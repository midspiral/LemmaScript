//@ backend dafny
//@ option safe-slice false

// Negative literal bounds count from the end. These preconditions keep the
// normalized bounds in range for direct Dafny slices, without clamping.

export function dropLast(xs: number[]): number[] {
  //@ requires xs.length > 0
  //@ ensures \result.length === xs.length - 1
  //@ ensures forall(i, 0 <= i && i < \result.length ==> \result[i] === xs[i])
  return xs.slice(0, -1);
}

export function lastTwo(xs: number[]): number[] {
  //@ requires xs.length >= 2
  //@ ensures \result === [xs[xs.length - 2], xs[xs.length - 1]]
  return xs.slice(-2);
}

export function lastTwoWithEnd(xs: number[]): number[] {
  //@ requires xs.length >= 2
  //@ ensures \result === [xs[xs.length - 2], xs[xs.length - 1]]
  return xs.slice(-2, xs.length);
}

export function thirdFromLast(xs: number[]): number[] {
  //@ requires xs.length >= 3
  //@ ensures \result === [xs[xs.length - 3]]
  return xs.slice(-3, -2);
}

export function trimEnds(xs: number[]): number[] {
  //@ requires xs.length >= 2
  //@ ensures \result.length === xs.length - 2
  //@ ensures forall(i, 0 <= i && i < \result.length ==> \result[i] === xs[i + 1])
  return xs.slice(1, -1);
}
