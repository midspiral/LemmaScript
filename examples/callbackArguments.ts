//@ backend dafny

// Callback parameters bind the element, index, and original array supplied by
// JavaScript. Unused bindings disappear; rest observations use that same list.
export function unusedRest(xs: number[]): number[] {
  return xs.map((value, ..._rest: [number, number[]]) => value + 1);
}

export function restCount(): number[] {
  //@ ensures \result[0] === 3
  // The rest array contains three arguments, even though the element has length 1.
  return [[7]].map((...args: (number | number[] | number[][])[]) => args.length);
}

export function tailCount(): number[] {
  //@ ensures \result[0] === 2
  return [7].map((value, ...tail: [number, number[]]) => tail.length);
}

export function unusedRestOnly(): number[] {
  //@ ensures \result[0] === 42
  return [7].map((..._args: [number, number, number[]]) => 42);
}

export function indexedMap(): number[] {
  //@ ensures \result[0] === 7 && \result[1] === 8
  // Equal elements still have distinct positions.
  return [7, 7].map((value, index) => value + index);
}

export function restIndex(): number[] {
  //@ ensures \result[0] === 0 && \result[1] === 1
  return [7, 7].map((value, ...tail: [number, number[]]) => tail[0]);
}

export function sourceArgument(): number[] {
  //@ ensures \result[0] === 7 && \result[1] === 8
  return [7, 8].map((value, index, source) => source[index]);
}

export function capturedIndex(index: number): boolean {
  //@ requires index === 1
  //@ ensures \result === false
  // The callback index shadows the outer index and is zero for the only element.
  return [7].some((value, index) => index === 1);
}

export function indexedSome(): boolean {
  //@ ensures \result === true
  return [7, 7].some((value, index) => index === 1);
}

export function defaultFromIndex(): number[] {
  //@ ensures \result[0] === 0 && \result[1] === 1
  // map supplies only three arguments, so the fourth parameter takes its default.
  return [7, 7].map((value, index, source, extra = index) => extra);
}

export function indexedEvery(): boolean {
  //@ ensures \result === true
  return [7, 8].every((value, index, source) => source[index] === value);
}

export function indexedFilter(): number[] {
  return [7, 8, 9].filter((value, index) => index !== 1);
}

export function indexedFind(): number | undefined {
  return [7, 8, 9].find((value, index) => index === 1);
}

export function indexedFindIndex(): number {
  return [7, 8, 9].findIndex((value, index) => index === 1);
}

export function indexedReduce(): number {
  return [4, 4].reduce((acc, value, index) => acc + value + index, 0);
}

export function reduceRestCount(): number {
  return [4, 4].reduce((acc, ...rest: [number, number, number[]]) => acc + rest.length, 0);
}

export function nestedShadow(): number[] {
  //@ ensures \result[0] === 2
  return [[7]].map((...args: [number[], number, number[][]]) => [1].map(args => args + 1)[0]);
}

export function nestedCapture(): number[] {
  //@ ensures \result[0] === 2
  return [7].map((value, ...rest: [number, number[]]) => [1].map(inner => rest.length)[0]);
}

export function unusedPositional(): number[] {
  //@ ensures \result[0] === 8
  return [7].map((value, _index, _source) => value + 1);
}
