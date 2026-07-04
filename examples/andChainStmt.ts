/**
 * `&&`-chain narrowing in statement position.
 *
 * `x !== undefined && x.f()` used as a bare statement is the `if`-less guard
 * idiom — TS-equivalent to `if (x !== undefined) x.f();`. Like the `if` and the
 * ternary (`x !== undefined ? x.f() : ...`) forms, the left conjunct narrows
 * `x` in the right conjunct, so the guarded effect sees the unwrapped value and
 * only runs when `x` is present.
 *
 * Without structural narrowing of this shape the guarded call would be lifted
 * out of the `&&` (running unconditionally, against the un-narrowed optional) —
 * so the proof IS the faithfulness check: the generated code type-checks and
 * verifies only because narrowing kept the call guarded and unwrapped.
 */

//@ backend dafny

type Inner = { val: number };
type Box = { items: number[]; inner: Inner | undefined };

function total(xs: number[]): number {
  //@ verify
  //@ ensures \result === 0
  return 0;
}

function use(v: number): number {
  //@ verify
  //@ ensures \result === v
  return v;
}

// Single optional check guarding a call on the narrowed value.
function single(b: Box | undefined): void {
  //@ verify
  b !== undefined && total(b.items);
}

// Chained checks nest into narrowings: `b`, then `b.inner`.
function chained(b: Box | undefined): void {
  //@ verify
  b !== undefined && b.inner !== undefined && use(b.inner.val);
}

// The scrutinee may be any pure access path, not just a bare var.
function fieldPath(b: Box): void {
  //@ verify
  b.inner !== undefined && use(b.inner.val);
}

// A `&&` with no optional check is left untouched (still a plain conjunction).
function plain(p: boolean, q: boolean): boolean {
  //@ verify
  //@ ensures \result === (p && q)
  return p && q;
}
