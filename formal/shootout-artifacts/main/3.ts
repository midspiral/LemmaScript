//@ requires ok
export function guard(ok: boolean, v: number): number {
  return v;
}
export function target(x?: number): boolean {
  return x === guard(false, 2);
}
