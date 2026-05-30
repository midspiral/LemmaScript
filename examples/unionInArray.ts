/**
 * Constructing discriminated-union values INSIDE ARRAY LITERALS.
 *
 * Regression test: a union object-literal used as an array element must resolve
 * to its named datatype constructor (`circle(...)`), not an anonymous tuple. The
 * fix threads the expected element type through `case "arrayLiteral"` (and the
 * array branch of `let`) in resolve.ts. Both return-position and const-position
 * arrays are covered; `firstArea`'s `ensures` only holds if the elements are real
 * `Shape` variants (a tuple wouldn't typecheck through `area`).
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

// Only provable if shapes()[0] is genuinely Shape.circle(2): 3*2*2 = 12.
export function firstArea(): number {
  //@ ensures \result === 12
  return area(shapes()[0])
}
