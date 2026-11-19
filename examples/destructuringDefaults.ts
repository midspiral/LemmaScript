// Destructuring defaults use Option coalescing when the source can be undefined.
// Mixed null/undefined types share None in the model; required nullable fields
// keep their values because their defaults cannot run.

export interface DefaultOptions { value?: number }
export interface NullableOptions { value: number | null }
export interface NullishOptions { value?: number | null }

export function optionalDefault(options: DefaultOptions): number {
  //@ ensures options.value === undefined ==> \result === 5
  //@ ensures options.value !== undefined ==> \result === options.value
  const { value = 5 } = options;
  return value;
}

export function nullableDefault(options: NullableOptions): number | null {
  //@ ensures \result === options.value
  const { value: result = 5 } = options;
  return result;
}

export function nullDefault(options: DefaultOptions): number | null {
  //@ ensures options.value === undefined ==> \result === null
  //@ ensures options.value !== undefined ==> \result === options.value
  const { value = null } = options;
  return value;
}

export function nullishDefault(options: NullishOptions): number | null {
  //@ ensures options.value === undefined ==> \result === null
  //@ ensures options.value !== undefined ==> \result === options.value
  const { value = null } = options;
  return value;
}

export function nullishArrayDefault(values: (number | null | undefined)[]): number | null {
  //@ ensures values.length === 0 ==> \result === null
  //@ ensures values.length > 0 && values[0] === undefined ==> \result === null
  //@ ensures values.length > 0 && values[0] !== undefined ==> \result === values[0]
  const [value = null] = values;
  return value;
}

// These contracts describe the shared Option model: None takes the default.
// JavaScript itself preserves an explicit null in these mixed-type cases.
export function mixedDefault(options: NullishOptions): number | null {
  //@ ensures options.value === undefined ==> \result === 5
  //@ ensures options.value !== undefined ==> \result === options.value
  const { value = 5 } = options;
  return value;
}

export function mixedArrayDefault(values: (number | null | undefined)[]): number | null {
  //@ ensures values.length === 0 ==> \result === 7
  //@ ensures values.length > 0 && values[0] === undefined ==> \result === 7
  //@ ensures values.length > 0 && values[0] !== undefined ==> \result === values[0]
  const [value = 7] = values;
  return value;
}

export function nullableArrayDefault(values: (number | null)[]): number | null {
  //@ ensures values.length === 0 ==> \result === 7
  //@ ensures values.length > 0 ==> \result === values[0]
  const [value = 7] = values;
  return value;
}

export function optionalArrayDefault(values: (number | undefined)[]): number {
  //@ ensures values.length === 0 ==> \result === 7
  //@ ensures values.length > 0 && values[0] === undefined ==> \result === 7
  //@ ensures values.length > 0 && values[0] !== undefined ==> \result === values[0]
  const [value = 7] = values;
  return value;
}

export function nullableParameterDefault({ value = 5 }: NullableOptions): number | null {
  //@ ensures \result === value
  return value;
}

export function renamedNullableParameterDefault({ value: result = 5 }: NullableOptions): number | null {
  //@ ensures \result === result
  return result;
}

export function nullishParameterDefault({ value = null }: NullishOptions): number | null {
  //@ ensures \result === value
  return value;
}

// Flattened prover parameters are initialized bindings. Their source defaults
// remain metadata for TypeScript callers; the proof starts at the function body.
export function parameterDefault({ value = 5 }: DefaultOptions): number {
  //@ ensures \result === value
  return value;
}

export function renamedParameterDefault({ value: selected = 5 }: NullishOptions): number | null {
  //@ ensures \result === selected
  return selected;
}

export function genericParameterDefault<T extends number>(fallback: T, { value = fallback }: { value?: T }): T {
  //@ ensures \result === value
  return value;
}

// This regex is never evaluated: a required nullable field is always defined.
export function unreachableDefault(options: NullableOptions): number | null {
  //@ ensures \result === options.value
  const { value = /unused/.test("unused") ? 5 : 6 } = options;
  return value;
}
