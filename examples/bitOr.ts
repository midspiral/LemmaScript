//@ backend dafny
// Bitwise OR (`|`) on non-negative bigints lowers to the recursive BitOr helper
// in the Dafny backend (the twin of BitAnd). Dafny has no `|` on `int`, only on
// bitvectors, so the operator is modeled arithmetically.

export function orZero(x: bigint): bigint {
  //@ verify
  //@ requires x >= 0
  //@ ensures \result === x
  return x | 0n
}

export function zeroOr(x: bigint): bigint {
  //@ verify
  //@ requires x >= 0
  //@ ensures \result === x
  return 0n | x
}
