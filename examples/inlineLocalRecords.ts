// Regression for #276: inline parameter and local annotations both acquire
// named records, so constructors and field accesses have matching types.

export function sumA(p: { x: number; y: number }): number {
  //@ ensures \result === p.x + p.y
  return p.x + p.y;
}

export function mk(n: number): number {
  //@ ensures \result === n
  const r: { k: number } = { k: n };
  return r.k;
}

export function localAfterAssignment(n: number): number {
  //@ ensures \result === n + 1
  let value = n;
  value += 1;
  const r: { k: number } = { k: value };
  return r.k;
}

export function optionalLocal(n: number, present: boolean): number {
  //@ ensures present ==> \result === n
  //@ ensures !present ==> \result === -1
  const r: { k: number } | undefined = present ? { k: n } : undefined;
  if (r !== undefined) return r.k;
  return -1;
}

export function localFallback(n: number, present: boolean): number {
  //@ ensures present ==> \result === n
  //@ ensures !present ==> \result === -1
  const r: { k?: number } = { k: present ? n : undefined };
  return r.k ?? -1;
}
