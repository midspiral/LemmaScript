export function usesSqrt(n: number): number {
  //@ verify
  //@ ensures \result >= 0
  const root = Math.sqrt(n);
  return root > 0 ? root : 0;
}
