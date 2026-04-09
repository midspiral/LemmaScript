/**
 * Havoc example — verify logic around havoced expressions.
 * The regex result is havoced; the set membership check is verified.
 */
//@ backend dafny

export function countMatches(
  items: string[],
  validKeys: Set<string>
): number {
  //@ verify
  //@ ensures \result >= 0
  let count = 0;
  for (const item of items) {
    //@ invariant count >= 0
    //@ havoc
    const cleaned = item.replace(/[^a-z]/g, '');
    if (validKeys.has(cleaned)) {
      count = count + 1;
    }
  }
  return count;
}
