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

export function reassignedParameter(value: number | undefined): number {
  //@ ensures value !== undefined ==> \result === 7
  //@ ensures value === undefined ==> \result === 0
  if (value !== undefined) {
    value = 7;
    return value;
  }
  return 0;
}

export function clearAfterGuard(value: number | undefined): number {
  //@ ensures \result === 9
  if (value !== undefined) value = undefined;
  return value ?? 9;
}

export function mutateOptionalArray(): number {
  //@ ensures \result === 1
  const values: number[] | undefined = [];
  if (values !== undefined) {
    values.push(7);
    return values.length;
  }
  return 0;
}

interface ArrayBox { values?: number[] }

export function mutateOptionalField(): number {
  //@ ensures \result === 2
  const box: ArrayBox | undefined = { values: [] };
  if (box !== undefined && box.values !== undefined) {
    box.values.push(7);
    box.values.push(9);
    return box.values.length;
  }
  return 0;
}

export function optionalLoop(): number {
  //@ ensures \result === 9
  let value: number | undefined = 1;
  while (value !== undefined) {
    //@ invariant value === undefined || value === 1
    //@ decreases value === undefined ? 0 : 1
    value = undefined;
  }
  return value ?? 9;
}

export function guardedCallback(value: number | undefined): number[] {
  //@ ensures value === undefined ==> \result.length === 0
  //@ ensures value !== undefined ==> \result.length === 2
  if (value === undefined) return [];
  return [1, 2].map(n => n + value);
}

export function mutateOptionalChain(): number {
  //@ ensures \result === 2
  let values: number[] | undefined = [];
  values?.push(7);
  values !== undefined && values.push(9);
  return values.length;
}

export function mutateLookupArray(): number {
  //@ ensures \result === 2
  const values = new Map<string, number[]>();
  values.set("present", []);
  values.get("present")?.push(7, 9);
  return values.get("present")!.length;
}

export function replaceParent(): number {
  //@ ensures \result === 9
  let cell: Cell | undefined = { value: 3 };
  if (cell !== undefined) {
    cell = { value: 9 };
    return cell.value;
  }
  return 0;
}

export function updateOptionalRecord(): number {
  //@ ensures \result === 9
  let cell: Cell | undefined = { value: 3 };
  if (cell !== undefined) cell = { ...cell, value: 9 };
  return cell.value;
}

export function optionalBuiltinArgument(): number {
  //@ ensures \result === 3
  let value: number | undefined = -3;
  if (value === undefined) return 0;
  return Math.max(value, 3);
}

export function spreadOptional(): number {
  //@ ensures \result === 3
  const values: number[] | undefined = [1, 2];
  if (values === undefined) return 0;
  return [...values, 3].length;
}

export function optionalCountdown(): number {
  //@ ensures \result === 0
  let value: number | undefined = 3;
  while (value !== undefined && value > 0) {
    //@ invariant value !== undefined && value >= 0
    //@ decreases value === undefined ? 0 : value + 0
    //@ done_with value !== undefined && value === 0
    value--;
  }
  return value;
}

export function optionalForOf(): number {
  //@ ensures \result === 7
  let value: number | undefined = 7;
  for (const ignored of [1, 2]) {
    //@ invariant value !== undefined && value === 7
    //@ done_with value !== undefined && value === 7
    value = 7;
  }
  return value;
}

export function clearIterable(): number {
  //@ ensures \result === 2
  let values: number[] | undefined = [1, 2];
  let count = 0;
  for (const item of values) {
    //@ invariant count === _item_idx
    //@ done_with count === 2
    values = undefined;
    count++;
  }
  return count;
}

export function falsyValues(): number {
  //@ ensures \result === 9
  const zero: number | undefined = 0;
  const empty: string | undefined = "";
  const no: boolean | undefined = false;
  const n = zero && 4;
  const text = empty || "hi";
  const flag = no && true;
  return n === 0 && text === "hi" && flag === false ? 9 : 0;
}
