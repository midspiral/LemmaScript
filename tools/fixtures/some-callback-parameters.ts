export function capturedIndex(index: number): boolean {
  //@ requires index === 1
  //@ ensures \result === false
  return [7].some((value, index) => index === 1);
}

export function arrayArgument(items: number[]): boolean {
  //@ ensures \result === true
  return [7].some((value, index, items) => items.length === 1 && items[index] === value);
}

export function duplicateValues(): boolean {
  //@ ensures \result === true
  return [7, 7].some((value, index, items) => index === 1 && items[index] === value);
}

export function emptyArray(): boolean {
  //@ ensures \result === false
  return ([] as number[]).some((value, index) => index === 0);
}

export function receiverScope(s_some: number[], i_some: number): boolean {
  //@ requires s_some.length > 1
  //@ ensures \result === true
  return s_some.slice(1).some((s_some, i_some, items) => i_some === 0 && items[i_some] === s_some);
}
