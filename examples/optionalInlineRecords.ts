// Optional inline records distinguish an absent fallback from a present
// fallback with no value. Regression tests also verify this example with
// exactOptionalPropertyTypes enabled.
//@ backend dafny

export interface Api {
  readonly name: string;
  readonly fallback?: { readonly value?: string };
}

export function hasFallback(api: Api): boolean {
  //@ ensures \result === (api.fallback !== undefined)
  return api.fallback !== undefined;
}

export function hasFallbackValue(api: Api): boolean {
  if (api.fallback === undefined) return false;
  return api.fallback.value !== undefined;
}

export function noFallback(name: string): Api {
  //@ ensures \result.name === name && \result.fallback === undefined
  return { name };
}

export function emptyFallback(name: string): Api {
  //@ ensures \result.name === name
  //@ ensures hasFallback(\result) && !hasFallbackValue(\result)
  return { name, fallback: {} };
}

export function withFallback(name: string, value: string): Api {
  //@ ensures \result.name === name
  //@ ensures hasFallbackValue(\result) && fallbackValue(\result) === value
  return { name, fallback: { value } };
}

export function fallbackValue(api: Api): string {
  //@ ensures api.fallback === undefined ==> \result === api.name
  //@ ensures api.fallback !== undefined && api.fallback.value === undefined ==> \result === api.name
  //@ ensures api.fallback !== undefined && api.fallback.value !== undefined ==> \result === api.fallback.value
  return api.fallback?.value ?? api.name;
}
