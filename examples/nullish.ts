export function classify(x: number | null | undefined): number {
  //@ ensures x === undefined ==> \result === 1
  //@ ensures x === null ==> \result === 2
  //@ ensures x !== undefined && x !== null ==> \result === x
  if (x === undefined) return 1;
  if (x === null) return 2;
  return x;
}
export function reverse(x: number | null | undefined): number {
  //@ ensures x === null ==> \result === 2
  //@ ensures x === undefined ==> \result === 1
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x === null) return 2;
  if (x === undefined) return 1;
  return x;
}
export function disjunction(x: number | null | undefined): number {
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x === null || x === undefined) return 0;
  return x;
}
export function retainNull(x: number | null | undefined): number | null {
  //@ ensures x !== undefined ==> \result === x
  if (x === undefined) return null;
  return x;
}
export function retainUndefined(x: number | null | undefined): number | undefined {
  //@ ensures x !== null ==> \result === x
  if (x === null) return undefined;
  return x;
}
export function positive(x: number | null | undefined): boolean {
  //@ ensures x === null || x === undefined ==> !\result
  //@ ensures x !== null && x !== undefined ==> (\result === (x > 0))
  return x !== null && x !== undefined && x > 0;
}
export function absentOrPositive(x: number | null | undefined): boolean {
  //@ ensures x === null || x === undefined ==> \result
  //@ ensures x !== null && x !== undefined ==> (\result === (x > 0))
  return x === null || x === undefined || x > 0;
}
