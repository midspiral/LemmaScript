export function target(arr?: number[]): number {
  if (arr !== undefined) {
    arr.push(9);
  }
  return arr !== undefined ? arr.length : 0;
}
