// Loose equality matches both nullish values; zero is still a present value.
export function looseIsNullish(x: number | null | undefined): boolean {
  //@ ensures \result === (x === null || x === undefined)
  return x == null;
}

export function looseOptional(x: number | undefined): boolean {
  //@ ensures \result === (x === undefined)
  return x == null;
}

export function looseNullable(x: number | null): boolean {
  //@ ensures \result === (x !== null)
  return undefined != x;
}

export function looseDefault(x: number | null | undefined): number {
  //@ ensures x == null ==> \result === 7
  //@ ensures x != null ==> \result === x
  if (x != null) return x;
  return 7;
}

export function looseEarlyReturn(x: number | null | undefined): number {
  //@ ensures x === null || x === undefined ==> \result === 7
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (undefined == x) return 7;
  return x;
}

export function loosePositive(x: number | null | undefined): boolean {
  //@ ensures x == undefined ==> !\result
  //@ ensures x != undefined ==> (\result === (x > 0))
  return null != x && x > 0;
}

export function looseAbsentOrPositive(x: number | null | undefined): boolean {
  //@ ensures x == null ==> \result
  //@ ensures x != null ==> (\result === (x > 0))
  return x == null || x > 0;
}

interface LooseBox { value?: number | null }

export function looseField(box: LooseBox): number {
  //@ ensures box.value == null ==> \result === 7
  //@ ensures box.value != null ==> \result === box.value
  if (box.value != null) return box.value;
  return 7;
}

export function looseCompare(a: number | null, b: number | undefined): boolean {
  //@ ensures a === null ==> (\result === (b === undefined))
  //@ ensures a !== null ==> (\result === (b !== undefined && a === b))
  return a == b;
}
