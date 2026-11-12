// The map-get rewrite runs inside the optional result's Some constructor.
// Lean must parenthesize the rewritten conditional constructor argument.
export function optionalLookup(
  enabled: boolean,
  values: Map<string, number>,
  key: string,
): number | undefined {
  //@ ensures !enabled ==> \result === undefined
  //@ ensures enabled && !values.has(key) ==> \result === 0
  //@ ensures enabled && values.has(key) ==> \result === values.get(key)
  return enabled ? (values.get(key) ?? 0) : undefined;
}
