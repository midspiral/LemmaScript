export type Msg = { u: number[] | number };

//@ ensures \result === (Array.isArray(u) ? (Array.isArray(m.u) ? m.u.length - u.length : 0) : 0)
export function nestedTernary(u: number[] | number, m: Msg): number {
  if (Array.isArray(u)) {
    return Array.isArray(m.u) ? m.u.length - u.length : 0;
  }
  return 0;
}

//@ ensures \result === (Array.isArray(u) ? (Array.isArray(m.u) ? m.u.length - u.length : 0) : 0)
export function nestedStatement(u: number[] | number, m: Msg): number {
  let result = 0;
  if (Array.isArray(u)) {
    result = Array.isArray(m.u) ? m.u.length - u.length : 0;
  }
  return result;
}
