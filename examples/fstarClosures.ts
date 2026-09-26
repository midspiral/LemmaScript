//@ backend fstar

// The returned closure carries a pointwise contract through nested application.
export function makeAdder(n: number): (x: number) => number {
  //@ ensures forall(x: int, \result(x) === x + n)
  return (x: number): number => x + n;
}

export function addThroughClosure(n: number, x: number): number {
  //@ ensures \result === x + n
  return makeAdder(n)(x);
}

export function addTwice(n: number, x: number): number {
  //@ ensures \result === x + n + n
  const add = makeAdder(n);
  return add(add(x));
}
