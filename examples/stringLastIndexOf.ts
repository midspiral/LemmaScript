//@ backend dafny
// String `lastIndexOf` lowers to the StringLastIndexOf helper in the Dafny
// backend. Its postconditions say the result is either -1 or the start of a
// match, and that no match starts later, so callers can rely on both the
// found and the not-found result.

export function lastDot(name: string): number {
  //@ verify
  //@ ensures \result === -1 || (0 <= \result && \result < name.length)
  return name.lastIndexOf(".");
}

// Found: the text after the last slash. Not found: the whole path.
export function baseName(path: string): string {
  //@ verify
  //@ ensures \result.length <= path.length
  const slash = path.lastIndexOf("/");
  return slash >= 0 ? path.slice(slash + 1) : path;
}

// A negative position searches from 0, as in JavaScript, so a match at index 0
// is found: ".ab".lastIndexOf(".", -5) === 0.
export function lastDotBefore(name: string, position: number): number {
  //@ verify
  //@ ensures \result <= position || \result <= 0
  return name.lastIndexOf(".", position);
}
