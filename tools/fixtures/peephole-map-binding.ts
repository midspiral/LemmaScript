export function lookup(values: Map<string, number>, key: string): number | undefined {
  //@ ensures values.has(key) ==> \result === values.get(key)
  //@ ensures !values.has(key) ==> \result === undefined
  let result: number | undefined = undefined;
  const cached = values.get(key);
  if (cached !== undefined) {
    result = cached;
  } else {
    // This use survives narrowing and still needs the original Option binding.
    result = cached;
  }
  return result;
}
