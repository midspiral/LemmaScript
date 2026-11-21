//@ backend dafny

// Scalar extrema fold through binary helpers; spreads aggregate a nonempty
// sequence. Real scores can be combined with integer scores without rounding.

export function singleScore(score: number): number {
  //@ verify
  //@ type score real
  //@ type \result real
  //@ ensures \result === score
  return Math.max(Math.min(score));
}

export function highestOfThree(a: number, b: number, c: number): number {
  //@ verify
  //@ ensures \result >= a && \result >= b && \result >= c
  //@ ensures \result === a || \result === b || \result === c
  return Math.max(a, b, c);
}

export function lowestOfFour(a: number, b: number, c: number, d: number): number {
  //@ verify
  //@ type a real
  //@ type b real
  //@ type c real
  //@ type d real
  //@ type \result real
  //@ ensures \result <= a && \result <= b && \result <= c && \result <= d
  //@ ensures \result === a || \result === b || \result === c || \result === d
  return Math.min(a, b, c, d);
}

export function highestScore(scores: number[]): number {
  //@ verify
  //@ type scores real[]
  //@ type \result real
  //@ requires scores.length > 0
  //@ ensures forall(i: nat, i < scores.length ==> scores[i] <= \result)
  //@ ensures exists(i: nat, i < scores.length && scores[i] === \result)
  return Math.max(...scores);
}

export function lowestScore(scores: number[]): number {
  //@ verify
  //@ type scores real[]
  //@ type \result real
  //@ requires scores.length > 0
  //@ ensures forall(i: nat, i < scores.length ==> \result <= scores[i])
  //@ ensures exists(i: nat, i < scores.length && scores[i] === \result)
  return Math.min(...scores);
}

export function highestScoreOrZero(scores: number[]): number {
  //@ verify
  //@ type scores real[]
  //@ type \result real
  //@ ensures \result >= 0
  //@ ensures forall(i: nat, i < scores.length ==> scores[i] <= \result)
  return Math.max(0, ...scores);
}

export function lowestScoreOrZero(scores: number[]): number {
  //@ verify
  //@ type scores real[]
  //@ type \result real
  //@ ensures \result <= 0
  //@ ensures forall(i: nat, i < scores.length ==> \result <= scores[i])
  return Math.min(...scores, 0);
}

export function highestMixedScore(whole: number[], fractional: number[]): number {
  //@ verify
  //@ type fractional real[]
  //@ type \result real
  //@ requires whole.length + fractional.length > 0
  //@ ensures forall(i: nat, i < whole.length ==> whole[i] <= \result)
  //@ ensures forall(i: nat, i < fractional.length ==> fractional[i] <= \result)
  return Math.max(...whole, ...fractional);
}
