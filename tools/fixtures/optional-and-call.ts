// An optional that an earlier presence check narrows, read as the argument of
// a pure function call later in the same `&&` chain.

interface Leaf { value?: number }
export interface Box { inner?: Leaf }

function idn(k: number): number { return k; }

export function callArg(o: number | undefined, x: number): boolean {
  return o !== undefined && idn(o) > x;
}

export function callArgIfElse(o: number | undefined, x: number): number {
  if (o !== undefined && idn(o) > x) return 1;
  else return 0;
}

export function callArgTernary(o: number | undefined, x: number): number {
  return o !== undefined && idn(o) > x ? 1 : 0;
}

export function nestedCallArg(a: Box, x: number): boolean {
  return a.inner !== undefined && a.inner.value !== undefined && idn(a.inner.value) > x;
}

export function nestedCallArgIfElse(a: Box, x: number): number {
  if (a.inner !== undefined && a.inner.value !== undefined && idn(a.inner.value) > x) return 1;
  else return 0;
}
