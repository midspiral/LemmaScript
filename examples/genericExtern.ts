/**
 * Generic `//@ extern`.
 *
 * `step` is an opaque, generic operation: `//@ extern` skips its body and
 * `//@ pure` makes lsc emit the uninterpreted Dafny function axiom
 * `function {:axiom} step<S, A>(s: S, a: A): S`. The verifier reasons about it
 * by its signature alone. The generic type parameters `<S, A>` must be carried
 * onto the axiom, or the `S`/`A` in its parameter and return types are
 * undeclared. A verified generic caller then reasons against that axiom.
 */

//@ backend dafny

//@ extern
//@ pure
export function step<S, A>(s: S, a: A): S {
  return s;
}

export function applyTwice<S, A>(s: S, a: A): S {
  //@ verify
  //@ type S (==)
  //@ ensures \result === step(step(s, a), a)
  const s1 = step(s, a);
  return step(s1, a);
}
