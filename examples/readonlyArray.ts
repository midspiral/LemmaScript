//@ backend dafny
// Regression: `readonly` array parameter types must translate to `seq`,
// identically to their mutable forms. Both spellings are covered:
//   - `readonly T[]`     — a `readonly` TypeOperator wrapping an ArrayType
//   - `ReadonlyArray<T>` — a type reference
// Previously the `readonly` operator fell through to an opaque user type,
// emitting invalid Dafny (`array: readonly T[]`, `|array|` on a non-seq).

export function firstOrZero(xs: readonly number[]): number {
  //@ ensures xs.length > 0 ==> \result === xs[0]
  //@ ensures xs.length === 0 ==> \result === 0
  return xs.length > 0 ? xs[0] : 0;
}

export function lengthOf<T>(xs: ReadonlyArray<T>): number {
  //@ ensures \result === xs.length
  //@ type T
  return xs.length;
}
