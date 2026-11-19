export function magnitude(t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures \result >= 0
  //@ ensures \result === (t >= 0 ? t : -t)
  return Math.abs(t);
}

export function smaller(a: number, b: number): number {
  //@ verify
  //@ type a real
  //@ type b real
  //@ type \result real
  //@ ensures \result <= a && \result <= b
  //@ ensures \result === a || \result === b
  return Math.min(a, b);
}

export function larger(a: number, b: number): number {
  //@ verify
  //@ type a real
  //@ type b real
  //@ type \result real
  //@ ensures \result >= a && \result >= b
  //@ ensures \result === a || \result === b
  return Math.max(a, b);
}

export function clampUnit(t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures 0 <= \result && \result <= 1
  //@ ensures 0 <= t && t <= 1 ==> \result === t
  return Math.min(1, Math.max(0, t));
}

export function mixedMin(n: number, t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures \result <= n && \result <= t
  //@ ensures \result === n || \result === t
  //@ ensures \result === Math.min(t, n)
  return Math.min(n, t);
}

export function mixedMax(t: number, n: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures \result >= t && \result >= n
  //@ ensures \result === t || \result === n
  //@ ensures \result === Math.max(n, t)
  return Math.max(t, n);
}

export function atLeastLength(t: number, values: number[]): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures \result >= values.length && \result >= t
  //@ ensures \result === values.length || \result === t
  return Math.max(values.length, t);
}

export function fractional(): number {
  //@ verify
  //@ type \result real
  //@ ensures \result === 0.5
  return Math.min(Math.abs(-0.5), Math.max(0.25, 0.75));
}
