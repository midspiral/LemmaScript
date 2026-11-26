// Strict checks distinguish null from undefined; loose checks and ?? accept both.
export function classifyNullish(value: number | null | undefined): number {
  //@ ensures value === null ==> \result === 1
  //@ ensures value === undefined ==> \result === 2
  //@ ensures value != null ==> \result === value + 10
  if (value === null) return 1;
  if (value === undefined) return 2;
  return value + 10;
}

// Nullish coalescing preserves present values, including zero.
export function defaultNullish(value: number | null | undefined, fallback: number): number {
  //@ ensures value == null ==> \result === fallback
  //@ ensures value != undefined ==> \result === value
  return value ?? fallback;
}

// Widening single-sentinel optionals must preserve which sentinel they contain.
export function widenNullish(
  value: number | null,
  fallback: number | undefined,
  useValue: boolean,
): number | null | undefined {
  //@ ensures useValue && value === null ==> \result === null
  //@ ensures useValue && value !== null ==> \result === value
  //@ ensures !useValue && fallback === undefined ==> \result === undefined
  //@ ensures !useValue && fallback !== undefined ==> \result === fallback
  return useValue ? value : fallback;
}

// Local mutation exercises Velvet's method verification as well as pure mirrors.
export function incrementNullish(value: number | null | undefined): number | null | undefined {
  //@ ensures value === null ==> \result === null
  //@ ensures value === undefined ==> \result === undefined
  //@ ensures value != null ==> \result === value + 1
  let result: number | null | undefined = value;
  if (value !== null && value !== undefined) {
    result = value + 1;
  }
  return result;
}
