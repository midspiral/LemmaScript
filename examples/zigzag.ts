/**
 * ZigZag encoding — the trick Protocol Buffers uses to store signed integers as
 * unsigned varints without wasting bytes on the sign. It folds the signed line
 * onto the non-negatives so small magnitudes stay small:
 *
 *     n:   0  -1   1  -2   2  -3   3
 *     enc: 0   1   2   3   4   5   6
 *
 * The point of the file is the pair of round-trip laws — `encode`/`decode` are a
 * genuine bijection between the integers and the non-negatives, proven in both
 * directions. `decode` uses `Math.floor(_/2)` (integer division; bare `/` is
 * real in JS — see division.ts), which is exact here because every encoded
 * value is non-negative.
 */

//@ backend dafny

// Fold a signed integer onto a non-negative "zigzag" code.
function encode(n: number): number {
  //@ verify
  //@ ensures \result >= 0
  return n >= 0 ? 2 * n : -2 * n - 1;
}

// Invert `encode`: unfold a non-negative code back to its signed integer.
function decode(z: number): number {
  //@ verify
  //@ requires z >= 0
  return z % 2 === 0 ? Math.floor(z / 2) : -Math.floor((z + 1) / 2);
}

// Round-trip law, forward: decoding an encoded integer recovers it — for every n.
function roundTrip(n: number): number {
  //@ verify
  //@ ensures \result === n
  return decode(encode(n));
}

// Round-trip law, backward: encoding a decoded code recovers it — for every
// non-negative z. Together with `roundTrip`, this pins a full bijection.
function reverseRoundTrip(z: number): number {
  //@ verify
  //@ requires z >= 0
  //@ ensures \result === z
  return encode(decode(z));
}
