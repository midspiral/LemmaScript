/**
 * `array.find` — first match as an Option (E4).
 *
 * `find` returns `T | undefined`, so its result feeds the optional-narrowing
 * rules: the optChain + nullish on the result exercise `ruleOptChain` /
 * `ruleNullish` over a `SeqFind` scrutinee. Dafny lowers to the `SeqFind`
 * preamble helper (first-match ensures); Lean lowers to `.find?`.
 */

type Entry = { key: string; val: number };

function lookup(entries: Entry[], key: string): number {
  //@ verify
  const e = entries.find(x => x.key === key);
  return e?.val ?? 0;
}

function hasEntry(entries: Entry[], key: string): boolean {
  //@ verify
  return entries.find(x => x.key === key) !== undefined;
}
