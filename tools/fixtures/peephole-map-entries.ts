//@ backend dafny

export function flags(first: boolean, second: boolean): Record<string, boolean> {
  return { first: first ? true : false, second: second ? true : false };
}

export function lookups(values: Map<string, number>, key: string): Record<string, number> {
  return { value: values.get(key) ?? 0 };
}
