export interface Q { a?: number; b: number }

export function objectDefault(o: Q): number {
  //@ ensures o.a === undefined ==> \result === 5
  //@ ensures o.a === 2 ==> \result === 2
  const { a = 5 } = o;
  return a;
}

export function defaultIntoOptional(o: Q): number | undefined {
  //@ ensures o.a === undefined ==> \result === 5
  const { a = 5 } = o;
  return a;
}

export function renamedDefault(o: Q): number {
  //@ ensures o.a === undefined ==> \result === o.b + 5
  const { a: x = 5, b } = o;
  return x + b;
}

export function arrayDefault(xs: number[]): number {
  //@ ensures xs.length === 0 ==> \result === 7
  //@ ensures xs.length > 0 ==> \result === xs[0]
  const [a = 7] = xs;
  return a;
}

export function secondDefault(xs: number[]): number {
  //@ ensures xs.length < 2 ==> \result === 9
  const [, b = 9] = xs;
  return b;
}
