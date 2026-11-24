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

// Shadowing a guard-narrowed variable inside the loop body keeps the inner
// binding distinct from the outer narrowed value.
export function shadow(i?: number): number {
  //@ requires i !== undefined && i === 1
  //@ ensures \result === 2
  while (i !== undefined) {
    //@ done_with true
    const i = 2;
    return i;
  }
  return 0;
}

// A lambda inside the loop body sees the narrowed binding, while a shadowing
// callback parameter stays distinct.
export function lambdaInWhile(a: number[], i?: number): number {
  //@ requires a.length === 1 && a[0] === 10
  //@ requires i !== undefined && i === 3
  //@ ensures \result === 18
  while (i !== undefined) {
    //@ done_with true
    const shifted = a.map((x: number): number => x + i);
    const shadowed = [5].map((i: number): number => i);
    return shifted[0] + shadowed[0];
  }
  return 0;
}

// Reassigning the guard variable and then narrowing it again reads the new
// value, not the guard's binder.
export function reassignThenNarrow(i?: number): number {
  //@ requires i !== undefined && i === 1
  //@ ensures \result === 2
  while (i !== undefined) {
    //@ done_with true
    i = 2;
    if (i !== undefined) {
      return i;
    }
  }
  return 0;
}

export type State = "some" | "none";

// String-union tags named "some" and "none" keep their own Dafny
// discriminators (`s.some?`, `s.none?`), distinct from `Option.Some?`.
export function isSome(s: State): boolean {
  return s === "some";
}

export function isNotNone(s: State): boolean {
  return s !== "none";
}
