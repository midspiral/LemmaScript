/**
 * Abstract function example — verify logic around opaque functions.
 * Demonstrates //@ abstract for functions outside the LS fragment.
 */
//@ backend dafny

//@ abstract
declare function parseNames(text: string): string[];

//@ abstract
declare function cleanText(text: string): string;

export function countValidNames(
  text: string,
  knownNames: Set<string>
): number {
  //@ verify
  //@ ensures \result >= 0
  const names = parseNames(text);
  let count = 0;
  for (const name of names) {
    //@ invariant count >= 0
    if (knownNames.has(cleanText(name))) {
      count = count + 1;
    }
  }
  return count;
}
