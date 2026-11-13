//@ backend dafny

// Reproductions from https://github.com/midspiral/LemmaScript/issues/288.
// Callback indices refer to positions, including when element values repeat.
export function pairwiseAtMost(a: number[], b: number[]): boolean {
  return a.length === b.length && a.every((x, i) => x <= b[i]);
}

export function plusIndex(a: number[]): number[] {
  return a.map((x, i) => x + i);
}
