// `null` and `undefined` both lower to `None`, so for a `T | undefined` value
// the loose checks `e != null` / `e != undefined` and the negated strict check
// `!(e === undefined)` narrow exactly like `e !== undefined`, and `e == null` /
// `e == undefined` narrow like `e === undefined`.

export function ifLooseNull(o: number | undefined, x: number): number {
  if (o != null) return o - x;
  return 0;
}

export function ifLooseUndefined(o: number | undefined, x: number): number {
  if (o != undefined) return o - x;
  return 0;
}

export function ifNegatedStrict(o: number | undefined, x: number): number {
  if (!(o === undefined)) return o - x;
  return 0;
}

export function ifReversed(o: number | undefined, x: number): number {
  if (null != o) return o - x;
  return 0;
}

export function returnLooseNull(o?: number): number {
  if (o != null) return o;
  return 0;
}

export function returnLooseUndefined(o?: number): number {
  if (o != undefined) return o;
  return 0;
}

export function chainLooseNull(a: number[], i?: number): number {
  if (i != null && i >= 0 && i < a.length) return a[i];
  return 0;
}

export function chainLooseUndefined(a: number[], i?: number): number {
  if (undefined != i && i >= 0 && i < a.length) return a[i];
  return 0;
}

export function chainNegatedStrict(a: number[], i?: number): number {
  if (!(i === undefined) && i >= 0 && i < a.length) return a[i];
  return 0;
}

export function ternaryLooseNull(o: number | undefined, x: number): number {
  return o != null ? o - x : 0;
}

export function ternaryLooseUndefined(o: number | undefined, x: number): number {
  return o != undefined ? o - x : 0;
}

export function ternaryNegatedStrict(o: number | undefined, x: number): number {
  return !(o === undefined) ? o - x : 0;
}

export function earlyLooseNull(o: number | undefined, x: number): number {
  if (o == null) return 0;
  return o - x;
}

export function earlyLooseUndefined(o: number | undefined, x: number): number {
  if (o == undefined) return 0;
  return o - x;
}

export function earlyReversed(o: number | undefined, x: number): number {
  if (null == o) return 0;
  return o - x;
}

export function earlyNegatedStrict(o: number | undefined, x: number): number {
  if (!(o !== undefined)) return 0;
  return o - x;
}

export function earlyIndexLooseNull(a: number[], i?: number): number {
  if (i == null) return 0;
  if (i < a.length && i >= 0) return a[i];
  return 0;
}

export function ternaryEqNull(o: number | undefined, x: number): number {
  return o == null ? 0 : o - x;
}

export function ternaryEqUndefined(o: number | undefined, x: number): number {
  return undefined == o ? 0 : o - x;
}

type Color = "red" | "green";

export function looseColor(c: Color): boolean {
  return c == "red";
}
