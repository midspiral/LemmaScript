// `!!o` has the truth value of `o`, and TypeScript narrows `o` under it.

export function ifThen(o: number | undefined, x: number): number {
  if (!!o) return o - x;
  return 0;
}

export function earlyReturn(o: number | undefined, x: number): number {
  if (!!!o) return 0;
  return o - x;
}

export function ternary(o: number | undefined, x: number): number {
  return !!o ? o - x : 0;
}
