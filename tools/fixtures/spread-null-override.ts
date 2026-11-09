export interface N { a: number | null; b: number }
export interface U { a: number | undefined; b: number }
export interface K { a?: number; b: number }

export function mergeNull(x: N, y: N): number | null {
  //@ ensures x.a === 1 && y.a === null ==> \result === null
  //@ ensures y.a === 2 ==> \result === 2
  return ({ ...x, ...y }).a;
}

export function mergeUndefined(x: U, y: U): number | undefined {
  //@ ensures x.a === 1 && y.a === undefined ==> \result === undefined
  //@ ensures y.a === 2 ==> \result === 2
  return ({ ...x, ...y }).a;
}

export function mergeOptionalKey(x: K, y: K): number | undefined {
  //@ ensures x.a === 1 && y.a === undefined ==> \result === 1
  //@ ensures y.a === 2 ==> \result === 2
  return ({ ...x, ...y }).a;
}
