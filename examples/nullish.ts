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

export function isUndefined(x: number | null | undefined): boolean {
  //@ ensures \result === (x === undefined)
  return x === undefined;
}

export function isNull(x: number | null | undefined): boolean {
  //@ ensures \result === (x === null)
  return x === null;
}

export function widenUndefined(x: number | undefined): number | null | undefined {
  //@ ensures \result === x
  return x;
}

export function widenNull(x: number | null): number | null | undefined {
  //@ ensures \result === x
  return x;
}

export function classifyMethod(x: number | null | undefined): number {
  //@ ensures x === undefined ==> \result === 1
  //@ ensures x === null ==> \result === 2
  //@ ensures x !== undefined && x !== null ==> \result === x
  let result = 0;
  if (x === undefined) result = 1;
  else if (x === null) result = 2;
  else result = x;
  return result;
}

export function lookupNullable(m: Map<string, number | null>, key: string): number | null | undefined {
  //@ ensures !m.has(key) ==> \result === undefined
  //@ ensures m.has(key) ==> \result === m.get(key)
  return m.get(key);
}
