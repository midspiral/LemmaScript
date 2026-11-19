export function optionalFlag(enabled: boolean, flag: boolean): boolean | undefined {
  return enabled ? (flag ? true : false) : undefined;
}

export function optionalLookup(enabled: boolean, values: Map<string, number>, key: string): number | undefined {
  return enabled ? (values.get(key) ?? 0) : undefined;
}
