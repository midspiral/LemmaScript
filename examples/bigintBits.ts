//@ backend dafny
// Shifts and masks by a literal fold to exact arithmetic. The literal is read
// as a compiler-side BigInt, so both the shift factor and the mask modulus stay
// exact past 2^53 — a `Math.pow`/32-bit-`&` fold would emit `1.18e+21` for the
// shift below and the wrong modulus (…552000) for the 64-bit mask.

export function shiftWide(x: bigint): bigint {
  //@ verify
  //@ requires x >= 0
  //@ ensures $result >= x
  return x << 70n
}

export function low64(x: bigint): bigint {
  //@ verify
  //@ requires x >= 0
  //@ ensures $result < 18446744073709551616n
  //@ ensures $result >= 0
  return x & 0xffffffffffffffffn
}
