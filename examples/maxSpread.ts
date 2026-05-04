//@ backend dafny

// Verifies Math.max / Math.min with spread args. The spread is desugared at
// extract time to a MaxOfSeq / MinOfSeq call over an arrayConcat tree.

export function highScore(scores: number[]): number {
  //@ verify
  //@ requires scores.length > 0
  //@ ensures forall(i: nat, i < scores.length ==> scores[i] <= \result)
  return Math.max(...scores);
}

export function highScoreOrZero(scores: number[]): number {
  //@ verify
  //@ ensures \result >= 0
  //@ ensures forall(i: nat, i < scores.length ==> scores[i] <= \result)
  return Math.max(...scores, 0);
}

export function lowScore(scores: number[]): number {
  //@ verify
  //@ requires scores.length > 0
  //@ ensures forall(i: nat, i < scores.length ==> \result <= scores[i])
  return Math.min(...scores);
}

export function maxOfPrefixedAndSuffixed(
  prefix: number,
  scores: number[],
  suffix: number,
): number {
  //@ verify
  //@ ensures \result >= prefix
  //@ ensures \result >= suffix
  //@ ensures forall(i: nat, i < scores.length ==> scores[i] <= \result)
  return Math.max(prefix, ...scores, suffix);
}

export function maxOfTwoArrays(a: number[], b: number[]): number {
  //@ verify
  //@ requires a.length + b.length > 0
  //@ ensures forall(i: nat, i < a.length ==> a[i] <= \result)
  //@ ensures forall(i: nat, i < b.length ==> b[i] <= \result)
  return Math.max(...a, ...b);
}
