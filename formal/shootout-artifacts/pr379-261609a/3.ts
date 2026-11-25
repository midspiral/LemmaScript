export function target(arr?: number[]): number {
  if (arr !== undefined && arr.length > 0) {
    arr[0] = 10;
    return arr[0];
  }
  return -1;
}
