// A presence check in a `while` guard narrows the rest of the guard and the
// body, until the body assigns the variable.

// The issue reproduction: the body reads the narrowed index, then clears it.
export function whileIdx(a: number[], i?: number): number {
  let s = 0;
  while (i !== undefined && i >= 0 && i < a.length) {
    s = a[i];
    i = undefined;
  }
  return s;
}

// Assigning a present value keeps the variable optional: `i := Some(...)`.
export function sumFrom(a: number[], i?: number): number {
  let s = 0;
  while (i !== undefined && i >= 0 && i < a.length) {
    //@ decreases i === undefined ? 0 : a.length - i
    s = s + a[i];
    i = i + 1;
  }
  return s;
}

// After the assignment, a read sees the new value, not the guard's.
export function countCleared(i?: number): number {
  let n = 0;
  while (i !== undefined && i > 0) {
    i = undefined;
    if (i === undefined) n = n + 1;
  }
  return n;
}

// A later check narrows the new value again.
export function stepUntilGone(a: number[], i?: number): number {
  let s = 0;
  while (i !== undefined && i >= 0 && i < a.length) {
    //@ decreases i === undefined ? 0 : a.length - i
    //@ done_with true
    s = s + a[i];
    i = i + 1 < a.length ? i + 1 : undefined;
    if (i === undefined) break;
    s = s + a[i];
  }
  return s;
}

export type Cursor = { pos?: number };

// A field path narrows too; assigning its root ends the narrowing.
export function fieldPath(a: number[], c: Cursor): number {
  let s = 0;
  while (c.pos !== undefined && c.pos >= 0 && c.pos < a.length) {
    s = s + a[c.pos];
    c = { pos: undefined };
  }
  return s;
}

// A truthiness guard also stops at 0.
export function truthy(a: number[], i?: number): number {
  let s = 0;
  while (i && i > 0 && i < a.length) {
    //@ decreases i === undefined ? 0 : i
    s = s + a[i];
    i = i - 1;
  }
  return s;
}
