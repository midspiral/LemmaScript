export function target(a: number[]): number {
  const b = a;
  b.push(-7);
  return a.length;
}
