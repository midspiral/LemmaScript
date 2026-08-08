/**
 * Truthiness — how LemmaScript models JavaScript truthiness in conditions
 * (`if` / `while` / `?:`) and under `!`.
 *
 * A value is falsy in JS iff it is `false`, `0`, `""`, `null`, or `undefined`.
 * Everything else is truthy — notably *every* array, even `[]`. Each function
 * below pins the modeled semantics with an `ensures`, so the proof IS the
 * faithfulness check: regress a coercion and verification fails.
 */

// ── boolean: identity ───────────────────────────────────────
function boolCond(b: boolean): number {
  //@ ensures b ==> $result === 1
  //@ ensures !b ==> $result === 0
  if (b) return 1;
  return 0;
}

// ── number: falsy iff 0 — negatives are truthy ──────────────
function numCond(n: number): number {
  //@ ensures n !== 0 ==> $result === 1
  //@ ensures n === 0 ==> $result === 0
  if (n) return 1;
  return 0;
}

function numNot(n: number): number {
  //@ ensures n === 0 ==> $result === 1
  //@ ensures n !== 0 ==> $result === 0
  if (!n) return 1;
  return 0;
}

function numTernary(n: number): number {
  //@ ensures n !== 0 ==> $result === 1
  //@ ensures n === 0 ==> $result === 0
  return n ? 1 : 0;
}

// ── string: falsy iff empty ─────────────────────────────────
function strCond(s: string): number {
  //@ ensures s.length > 0 ==> $result === 1
  //@ ensures s.length === 0 ==> $result === 0
  if (s) return 1;
  return 0;
}

function strNot(s: string): number {
  //@ ensures s.length === 0 ==> $result === 1
  //@ ensures s.length > 0 ==> $result === 0
  if (!s) return 1;
  return 0;
}

// ── array: always truthy, even [] ───────────────────────────
function arrCond(xs: number[]): number {
  //@ ensures $result === 1
  if (xs) return 1;
  return 0;
}

function arrNot(xs: number[]): number {
  //@ ensures $result === 0
  if (!xs) return 1;
  return 0;
}

// ── && / || : each operand is coerced on its own ────────────
// The operands need not share a type — `i >= 0 && carry` is a bool conjoined
// with a number. JS puts each side in condition position separately, so this
// means `i >= 0 && carry !== 0`, NOT `(i >= 0 && carry) !== 0`.
function andMixed(i: number, carry: number): number {
  //@ ensures i >= 0 && carry !== 0 ==> $result === 1
  //@ ensures i < 0 || carry === 0 ==> $result === 0
  if (i >= 0 && carry) return 1;
  return 0;
}

function orMixed(s: string, n: number): number {
  //@ ensures s.length > 0 || n !== 0 ==> $result === 1
  //@ ensures s.length === 0 && n === 0 ==> $result === 0
  if (s || n) return 1;
  return 0;
}

// Coercion distributes through nested connectives; `c` is an array, so always
// truthy, and the whole condition reduces to the disjunction on the left.
function andOrNested(a: number, b: string, c: number[]): number {
  //@ ensures a !== 0 || b.length > 0 ==> $result === 1
  //@ ensures a === 0 && b.length === 0 ==> $result === 0
  if ((a || b) && c) return 1;
  return 0;
}

// Same rule in a `while` guard — the shape that motivated this: a carry loop
// scanning right-to-left runs while the index is in range and carry is set.
function carryScan(digits: number[]): number {
  //@ requires digits.length > 0
  //@ ensures $result >= -1 && $result < digits.length
  let i = digits.length - 1;
  let carry = 1;
  while (i >= 0 && carry) {
    //@ invariant i >= -1 && i < digits.length
    //@ decreases (i + 1).toNat
    if (digits[i] === 0) {
      carry = 0;
    }
    i = i - 1;
  }
  return i;
}

// ── optional number: falsy iff absent OR 0 ──────────────────
function optNumCond(o: number | undefined): number {
  //@ ensures o === undefined ==> $result === 0
  //@ ensures o === 0 ==> $result === 0
  //@ ensures o !== undefined && o !== 0 ==> $result === 1
  if (o) return 1;
  return 0;
}

function optNumNot(o: number | undefined): number {
  //@ ensures o === undefined ==> $result === 1
  //@ ensures o === 0 ==> $result === 1
  //@ ensures o !== undefined && o !== 0 ==> $result === 0
  if (!o) return 1;
  return 0;
}

// ── optional string: falsy iff absent OR empty ──────────────
function optStrCond(o: string | undefined): number {
  //@ ensures o === undefined ==> $result === 0
  //@ ensures o === "" ==> $result === 0
  //@ ensures o !== undefined && o !== "" ==> $result === 1
  if (o) return 1;
  return 0;
}

// ── explicit presence is NOT truthiness: Some(0) is present ──
function optPresent(o: number | undefined): number {
  //@ ensures o !== undefined ==> $result === 1
  //@ ensures o === undefined ==> $result === 0
  if (o !== undefined) return 1;
  return 0;
}
