/**
 * Block-scoped `let` reuse across sibling scopes.
 *
 * TypeScript scopes a `for (let i …)`'s counter to the loop, so a later
 * `let i` in the same function is a *distinct* binding. Lowering hoists the
 * for-counter into the enclosing block, so both would become `var i` in one
 * Dafny method scope — `Error: Duplicate local-variable name: i`. The de-dup
 * pass (transform.ts `dedupeMethodLocals`) renames only a binding that clashes
 * with one already live in the SAME flattened scope (→ `i_2`, `i_3`, …) and
 * rewrites that binding's references. Non-conflicting code is untouched, and
 * Dafny's legal nested-block shadowing is left alone.
 */

//@ backend dafny

// A counting `for` then a separate `while`, both written with `i`. The `while`'s
// `i` is renamed (→ `i_2`) so the two no longer collide.
export function sumThenCount(xs: number[]): number {
  //@ verify
  //@ type i nat
  //@ ensures \result >= 0
  let total = 0;
  for (let i = 0; i < xs.length; i = i + 1) {
    //@ invariant i <= xs.length
    //@ invariant total >= 0
    //@ decreases xs.length - i
    if (xs[i]! > 0) { total = total + 1; }
  }
  let i = 0;
  while (i < total) {
    //@ invariant 0 <= i && i <= total
    //@ invariant total >= 0
    //@ decreases total - i
    i = i + 1;
  }
  return total;
}

// A synthesized name must dodge identifiers already in use: `i_2` is taken, so
// the two reused `i`s become `i_3` and `i_4`.
export function dodgeTakenName(n: number): number {
  //@ verify
  //@ type i nat
  //@ type i_2 nat
  //@ requires n >= 0
  //@ ensures \result >= 0
  let acc = 0;
  let i_2 = n;
  for (let i = 0; i < n; i = i + 1) {
    //@ invariant i <= n
    //@ invariant acc >= 0
    //@ decreases n - i
    acc = acc + 1;
  }
  let i = 0;
  while (i < n) {
    //@ invariant 0 <= i && i <= n
    //@ invariant acc >= 0
    //@ decreases n - i
    acc = acc + 1;
    i = i + 1;
  }
  return acc + (i_2 - i_2);
}
