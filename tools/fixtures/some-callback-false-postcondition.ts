export function capturedIndex(index: number): boolean {
  //@ requires index === 1
  //@ ensures \result === true
  return [7].some((value, index) => index === 1);
}
