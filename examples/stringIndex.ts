/**
 * String indexing returns a string. Bounds refer to positions in the selected
 * string model; these examples use the default Unicode-scalar model.
 */

export function firstIsA(s: string): boolean {
  //@ ensures \result === (s.length > 0 && s[0] === "a")
  return s.length > 0 && s[0] === "a";
}

export function sameAt(s: string, t: string, i: number, j: number): boolean {
  //@ requires 0 <= i && i < s.length && 0 <= j && j < t.length
  //@ ensures \result === (s.slice(i, i + 1) === t.slice(j, j + 1))
  return s[i] === t[j];
}

export function indexedChar(s: string, i: number): string {
  //@ requires 0 <= i && i < s.length
  //@ ensures \result.length === 1
  //@ ensures \result === s.slice(i, i + 1)
  return s[i];
}
