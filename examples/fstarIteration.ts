//@ backend fstar

// The callback guarantee is preserved through recursive composition.
export function repeat(n: number, f: (x: number) => number, x: number): number {
  //@ requires n >= 0
  //@ requires forall(y: int, f(y) >= y)
  //@ ensures \result >= x
  //@ decreases n
  if (n === 0) return x;
  return repeat(n - 1, f, f(x));
}

export function iterate(n: number, f: (x: number) => number): (x: number) => number {
  //@ requires n >= 0
  //@ requires forall(y: int, f(y) >= y)
  //@ ensures forall(x: int, \result(x) >= x)
  return (x: number): number => repeat(n, f, x);
}

export function incrementThreeTimes(x: number): number {
  //@ ensures \result >= x
  return iterate(3, (y: number): number => y + 1)(x);
}
