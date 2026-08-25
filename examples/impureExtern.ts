/**
 * Cross-file `//@ impure` extern.
 *
 * The imported declaration is opaque to this verification target, but its
 * marker prevents two calls from being collapsed by extensional equality.
 * Each roll is arbitrary and independently constrained to [1, 6].
 */

//@ backend dafny

import { rollDie } from "./support/impureDie.js";

export function sumTwoRolls(): number {
  //@ verify
  //@ ensures 2 <= \result && \result <= 12
  const a = rollDie();
  const b = rollDie();
  return a + b;
}
