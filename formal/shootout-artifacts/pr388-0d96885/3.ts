export function target(a: number[]): number {
  const b = a;
  b.push(0);
  return a.length;
}
