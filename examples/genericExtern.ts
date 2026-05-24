/**
 * Generic `//@ extern`.
 *
 * `step` is an opaque, generic operation: `//@ extern` makes lsc emit it as a
 * body-less Dafny `function {:axiom} step<S, A>(s: S, a: A): S` — an
 * uninterpreted symbol the verifier reasons about by its signature alone. The
 * generic type parameters `<S, A>` must be carried onto the axiom, or the `S`/`A`
 * in its parameter and return types are undeclared. A verified generic caller
 * then reasons against that axiom.
 */

//@ backend dafny

//@ extern
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
