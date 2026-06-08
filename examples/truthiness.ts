/**
 * Truthiness — how LemmaScript models JavaScript truthiness in conditions
 * (`if` / `while` / `?:`) and under `!`.
 *
 * A value is falsy in JS iff it is `false`, `0`, `""`, `null`, or `undefined`.
 * Everything else is truthy — notably *every* array, even `[]`. Each function
 * below pins the modeled semantics with an `ensures`, so the proof IS the
 * faithfulness check: regress a coercion and verification fails.
 */
//@ backend dafny

// ── boolean: identity ───────────────────────────────────────
function boolCond(b: boolean): number {
  //@ ensures b ==> \result === 1
  //@ ensures !b ==> \result === 0
  if (b) return 1;
  return 0;
}

// ── number: falsy iff 0 — negatives are truthy ──────────────
function numCond(n: number): number {
  //@ ensures (n !== 0) ==> \result === 1
  //@ ensures (n === 0) ==> \result === 0
  if (n) return 1;
  return 0;
}

function numNot(n: number): number {
  //@ ensures (n === 0) ==> \result === 1
  //@ ensures (n !== 0) ==> \result === 0
  if (!n) return 1;
  return 0;
}

function numTernary(n: number): number {
  //@ ensures (n !== 0) ==> \result === 1
  //@ ensures (n === 0) ==> \result === 0
  return n ? 1 : 0;
}

// ── string: falsy iff empty ─────────────────────────────────
function strCond(s: string): number {
  //@ ensures (s.length > 0) ==> \result === 1
  //@ ensures (s.length === 0) ==> \result === 0
  if (s) return 1;
  return 0;
}

function strNot(s: string): number {
  //@ ensures (s.length === 0) ==> \result === 1
  //@ ensures (s.length > 0) ==> \result === 0
  if (!s) return 1;
  return 0;
}

// ── array: always truthy, even [] ───────────────────────────
function arrCond(xs: number[]): number {
  //@ ensures \result === 1
  if (xs) return 1;
  return 0;
}

function arrNot(xs: number[]): number {
  //@ ensures \result === 0
  if (!xs) return 1;
  return 0;
}

// ── optional number: falsy iff absent OR 0 ──────────────────
function optNumCond(o: number | undefined): number {
  //@ ensures o === undefined ==> \result === 0
  //@ ensures o === 0 ==> \result === 0
  //@ ensures (o !== undefined && o !== 0) ==> \result === 1
  if (o) return 1;
  return 0;
}

function optNumNot(o: number | undefined): number {
  //@ ensures o === undefined ==> \result === 1
  //@ ensures o === 0 ==> \result === 1
  //@ ensures (o !== undefined && o !== 0) ==> \result === 0
  if (!o) return 1;
  return 0;
}

// ── optional string: falsy iff absent OR empty ──────────────
function optStrCond(o: string | undefined): number {
  //@ ensures o === undefined ==> \result === 0
  //@ ensures o === "" ==> \result === 0
  //@ ensures (o !== undefined && o !== "") ==> \result === 1
  if (o) return 1;
  return 0;
}

// ── explicit presence is NOT truthiness: Some(0) is present ──
function optPresent(o: number | undefined): number {
  //@ ensures o !== undefined ==> \result === 1
  //@ ensures o === undefined ==> \result === 0
  if (o !== undefined) return 1;
  return 0;
}
