//@ backend fstar

// A generic combinator returns a function with a pointwise composition law.
export function compose<A, B, C>(
  outer: (value: B) => C,
  inner: (value: A) => B,
): (value: A) => C {
  //@ ensures forall(value: A, \result(value) === outer(inner(value)))
  return (value: A): C => outer(inner(value));
}

export function incrementThenDouble(x: number): number {
  //@ ensures \result === (x + 1) * 2
  return compose(
    (n: number): number => n * 2,
    (n: number): number => n + 1,
  )(x);
}

export function twice(f: (x: number) => number, x: number): number {
  //@ requires forall(y: int, f(y) >= y)
  //@ ensures \result >= x
  return f(f(x));
}
