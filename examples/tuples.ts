/**
 * Tuples — heterogeneous `[A, B]` map to native tuples (Dafny `(A, B)` /
 * Lean `A × B`), while homogeneous tuples stay `seq`. Element access needs a
 * compile-time integer-literal index (`t[0]`, `t[1]`).
 */

// Construct a heterogeneous tuple literal and project its slots (spec + body).
function swap(p: [number, string]): [string, number] {
  //@ ensures \result[0] === p[1]
  //@ ensures \result[1] === p[0]
  return [p[1], p[0]];
}

// Projection at arity 3 — exercises Lean's nested `.1` / `.2.1` / `.2.2`.
function middle(t: [number, string, boolean]): string {
  //@ ensures \result === t[1]
  return t[1];
}

// `const [a, b] = t` destructuring desugars to per-slot projections.
function addFirstTwo(p: [number, number, string]): number {
  //@ ensures \result === p[0] + p[1]
  const [a, b] = p;
  return a + b;
}

// for-of over an array of tuples, destructuring each element.
function sumFirsts(pairs: [number, string][]): number[] {
  const out: number[] = [];
  for (const [n, label] of pairs) {
    out.push(n);
  }
  return out;
}

// Homogeneous `[number, number]` lowers to `seq` — it has `.length` and needs
// a bounds fact for indexing, unlike a fixed-arity tuple.
function homogeneousStaysSeq(xs: [number, number]): number {
  //@ requires xs.length === 2
  //@ ensures \result === xs[0] + xs[1]
  return xs[0] + xs[1];
}
