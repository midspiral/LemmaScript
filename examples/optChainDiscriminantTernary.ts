/**
 * `x?.disc === 'lit'` narrowing in expression position — the ternary sibling of
 * the `if (x?.disc !== 'lit') return` statement rule (`ruleConditionalOptChainCompare`
 * / `ruleEarlyReturnOptChainCompare`, sharing `parseOptChainLitCompare`). Covers
 * optChain on either side, a discriminant vs. a plain field, and the `===`
 * ternary and `!==` statement forms. Mirrors flue's `classifySubmissionState`
 * (`assistantEntry?.type === 'message' ? assistantEntry.message : undefined`).
 */

type Entry = { kind: 'msg'; text: string } | { kind: 'sep' };
type Rec = { tag: string; body: string };

// `===` ternary, optChain on the left, discriminant field.
export function textOr(e: Entry | undefined, dflt: string): string {
  //@ verify
  //@ ensures e === undefined ==> \result === dflt
  const t = e?.kind === 'msg' ? e.text : undefined;
  return t ?? dflt;
}

// optChain on the right (`'lit' === x?.disc`).
export function textOrFlipped(e: Entry | undefined, dflt: string): string {
  //@ verify
  //@ ensures e === undefined ==> \result === dflt
  const t = 'msg' === e?.kind ? e.text : undefined;
  return t ?? dflt;
}

// Plain (non-discriminant) field on a record — the unwrapped guard stays a field
// read, not a discriminant test.
export function bodyOr(r: Rec | undefined, dflt: string): string {
  //@ verify
  //@ ensures r === undefined ==> \result === dflt
  const b = r?.tag === 'x' ? r.body : undefined;
  return b ?? dflt;
}

// `!==` statement form (early return) — exercises the shared helper's other arm.
export function firstText(e: Entry | undefined, dflt: string): string {
  //@ verify
  //@ ensures e === undefined ==> \result === dflt
  if (e?.kind !== 'msg') return dflt;
  return e.text;
}
