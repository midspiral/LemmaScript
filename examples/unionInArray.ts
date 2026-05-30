/**
 * Constructing discriminated-union values INSIDE ARRAY LITERALS.
 *
 * Regression test: a union object-literal used as an array element must resolve
 * to its named datatype constructor (`circle(...)` / `rect(...)`), not an
 * anonymous tuple. The fix threads the expected element type through
 * `case "arrayLiteral"` (and the array branch of `let`) in resolve.ts. Both
 * return-position and const-position arrays are covered. Under the old behavior
 * these arrays generated tuples and failed to resolve as `seq<Shape>`; `total`
 * additionally consumes the elements back through `area`.
 */

type Shape =
  | { kind: "circle"; r: number }
  | { kind: "rect"; w: number; h: number }

function area(s: Shape): number {
  if (s.kind === "circle") return 3 * s.r * s.r
  return s.w * s.h
}

// Union literals as elements of a RETURN-position array literal.
export function shapes(): Shape[] {
  return [{ kind: "circle", r: 2 }, { kind: "rect", w: 3, h: 4 }]
}

// Union literal as an element of a CONST-annotated array literal.
export function oneRect(): Shape[] {
  const xs: Shape[] = [{ kind: "rect", w: 1, h: 5 }]
  return xs
}

// Consume the constructed elements (only valid if they are real `Shape` values).
export function total(): number {
  const xs = shapes()
  return area(xs[0]) + area(xs[1])
}
