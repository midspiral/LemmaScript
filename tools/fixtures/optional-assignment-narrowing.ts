export function coalescedNull(flag: boolean): number {
  //@ ensures flag ==> \result === 7
  //@ ensures !flag ==> \result === 5
  let p: number | null = flag ? null : 5;
  p = p ?? 7;
  return p;
}

export function coalescedUndefined(flag: boolean): number {
  //@ ensures flag ==> \result === 7
  //@ ensures !flag ==> \result === 5
  let p: number | undefined = flag ? undefined : 5;
  p = p ?? 7;
  return p;
}

export function repeatedWrites(): number {
  //@ ensures \result === 8
  let p: number | undefined = undefined;
  p = 5;
  p = undefined;
  p = p ?? 7;
  p = p + 1;
  return p;
}

export function conditionalReset(flag: boolean): number {
  //@ ensures flag ==> \result === 7
  //@ ensures !flag ==> \result === 5
  let p: number | undefined = 5;
  if (flag) p = undefined;
  return p ?? 7;
}

export function optionalFallback(flag: boolean): number | undefined {
  //@ ensures flag ==> \result === 5
  //@ ensures !flag ==> \result === undefined
  let p: number | undefined = undefined;
  let fallback: number | undefined = undefined;
  if (flag) fallback = 5;
  return p ?? fallback;
}

export function compoundWrites(): number {
  //@ ensures \result === 10
  let p: number | undefined = undefined;
  p = 7;
  p += 1;
  p++;
  ++p;
  return p;
}

interface Cell { value: number }

export function guardedCell(cell: Cell | undefined): number {
  //@ ensures cell === undefined ==> \result === 7
  //@ ensures cell !== undefined && cell.value < 0 ==> \result === 7
  //@ ensures cell !== undefined && cell.value >= 0 ==> \result === cell.value
  if (!cell || cell.value < 0) return 7;
  return cell.value;
}

export function nestedReads(): number {
  //@ ensures \result === 8
  let value: number | undefined = undefined;
  value = 7;
  let cell: Cell | undefined = undefined;
  cell = { value };
  let index: number | undefined = undefined;
  index = 0;
  const values = [cell.value];
  return values[index] + 1;
}
