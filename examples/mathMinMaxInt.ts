// Integer extrema shared by Dafny and Lean. Only the combined spread input
// must be nonempty; adding a scalar makes empty array segments safe.

export function singleValue(x: number): number {
  //@ verify
  //@ ensures \result === x
  return Math.min(Math.max(x));
}

export function highestInteger(a: number, b: number, c: number): number {
  //@ verify
  //@ ensures \result >= a && \result >= b && \result >= c
  //@ ensures \result === a || \result === b || \result === c
  return Math.max(a, b, c);
}

export function lowestNatural(a: number, b: number, c: number): number {
  //@ verify
  //@ type a nat
  //@ type b nat
  //@ type c nat
  //@ type \result nat
  //@ ensures \result <= a && \result <= b && \result <= c
  //@ ensures \result === a || \result === b || \result === c
  return Math.min(a, b, c);
}

export function lowestMixed(a: number, b: number): number {
  //@ verify
  //@ type a nat
  //@ ensures \result <= a && \result <= b
  //@ ensures \result === a || \result === b
  return Math.min(Math.max(a, a), b);
}

export function highestInArray(xs: number[]): number {
  //@ verify
  //@ requires xs.length > 0
  //@ ensures forall(i: nat, i < xs.length ==> xs[i] <= \result)
  //@ ensures exists(i: nat, i < xs.length && xs[i] === \result)
  return Math.max(...xs);
}

export function lowestInArray(xs: number[]): number {
  //@ verify
  //@ requires xs.length > 0
  //@ ensures forall(i: nat, i < xs.length ==> \result <= xs[i])
  //@ ensures exists(i: nat, i < xs.length && xs[i] === \result)
  return Math.min(...xs);
}

export function lowestOrZero(xs: number[]): number {
  //@ verify
  //@ ensures \result <= 0
  //@ ensures forall(i: nat, i < xs.length ==> \result <= xs[i])
  return Math.min(...[], ...xs, 0);
}

export function highestMixedArrays(ns: number[], xs: number[]): number {
  //@ verify
  //@ type ns nat[]
  //@ requires ns.length + xs.length > 0
  //@ ensures forall(i: nat, i < ns.length ==> ns[i] <= \result)
  //@ ensures forall(i: nat, i < xs.length ==> xs[i] <= \result)
  return Math.max(...ns, ...xs);
}

export function highestWithNatural(xs: number[], n: number): number {
  //@ verify
  //@ type n nat
  //@ ensures \result >= n
  //@ ensures forall(i: nat, i < xs.length ==> xs[i] <= \result)
  return Math.max(...xs, n);
}

export function arrayRange(xs: number[]): number {
  //@ verify
  //@ requires xs.length > 0
  //@ ensures \result >= 0
  return highestInArray(xs) - lowestInArray(xs);
}

export function guardedHighest(xs: number[]): number {
  //@ verify
  //@ ensures xs.length === 0 ==> \result === 0
  //@ ensures forall(i: nat, i < xs.length ==> xs[i] <= \result)
  return xs.length === 0 ? 0 : Math.max(...xs);
}
