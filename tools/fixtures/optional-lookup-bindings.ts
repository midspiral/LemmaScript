export function guardedLookup(values: Record<string, number>, key: string): number {
  //@ ensures !(key in values) ==> \result === -1
  //@ ensures key in values && values[key] >= 0 ==> \result === values[key]
  const value = values[key];
  if (value !== undefined && value >= 0) return value;
  return -1;
}

export function annotatedLookup(values: Record<string, number>, key: string): number {
  //@ ensures !(key in values) ==> \result === 7
  //@ ensures key in values ==> \result === values[key]
  const value: number = values[key];
  if (value === undefined) return 7;
  return value;
}

interface Cell { value: number }

export function lastMatch(values: Cell[], target: number): Cell {
  //@ ensures \result.value === target
  const match = values.findLast(cell => cell.value === target);
  return match ?? { value: target };
}
