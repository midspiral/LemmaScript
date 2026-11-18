/**
 * Array binding pattern in an arrow parameter. The pattern becomes one
 * synthetic parameter, and each named position is bound by index at the start
 * of the body; an elided position (`[, v]`) binds nothing.
 *
 *   ([k, v]) => e   →   (p) => { const k = p[0]; const v = p[1]; return e }
 */

//@ backend dafny

export function values(pairs: Array<[string, number]>): number[] {
  //@ verify
  //@ ensures \result.length === pairs.length
  //@ ensures forall(i, 0 <= i && i < pairs.length ==> \result[i] === pairs[i][1])
  return pairs.map(([, v]) => v);
}

export function swapped(pairs: Array<[string, number]>): Array<[number, string]> {
  //@ verify
  //@ ensures \result.length === pairs.length
  //@ ensures forall(i, 0 <= i && i < pairs.length ==> \result[i][0] === pairs[i][1] && \result[i][1] === pairs[i][0])
  return pairs.map(([k, v]): [number, string] => [v, k]);
}
