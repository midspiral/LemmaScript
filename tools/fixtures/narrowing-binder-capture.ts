// The `ensures` clauses here are deliberately false. An array-union match on
// `m.u` mints the same binder name as the narrowing of the outer `u`. If the
// inner binder captures the outer reference, `m.u.length - u.length` becomes
// the length of `m.u` minus itself, and Dafny proves the false claim.

export type Msg = { u: number[] | number };

//@ ensures \result === 0
export function capturedInTernary(u: number[] | number, m: Msg): number {
  if (Array.isArray(u)) {
    return Array.isArray(m.u) ? m.u.length - u.length : 0;
  }
  return 0;
}

//@ ensures forall(i, 0 <= i && i < \result.length ==> \result[i] === 0)
export function capturedInCallback(u: number[] | number, ms: Msg[]): number[] {
  if (Array.isArray(u)) {
    return ms.map(m => (Array.isArray(m.u) ? m.u.length - u.length : 0));
  }
  return [];
}
