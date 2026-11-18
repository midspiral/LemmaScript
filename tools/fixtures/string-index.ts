export function firstIsA(s: string): boolean {
  //@ ensures \result === (s.length > 0 && s[0] === "a")
  return s.length > 0 && s[0] === "a";
}

export function sameElement(s: string, t: string, i: number, j: number): boolean {
  //@ requires 0 <= i && i < s.length && 0 <= j && j < t.length
  //@ ensures \result === (s.slice(i, i + 1) === t.slice(j, j + 1))
  return s[i] === t[j];
}

export function beforeElement(s: string, t: string, i: number, j: number): boolean {
  //@ requires 0 <= i && i < s.length && 0 <= j && j < t.length
  //@ ensures \result === (s.slice(i, i + 1) < t.slice(j, j + 1))
  return s[i] < t[j];
}

export function agreesAt(s: string, t: string, i: number, j: number, expected: boolean): boolean {
  //@ requires 0 <= i && i < s.length && 0 <= j && j < t.length
  //@ ensures \result === (expected === (s.slice(i, i + 1) === t.slice(j, j + 1)))
  return expected === (s[i] === t[j]);
}

export function stringAt(s: string, i: number): string {
  //@ requires 0 <= i && i < s.length
  //@ ensures \result === s.slice(i, i + 1)
  return s[i];
}

export function doubledIndex(s: string, i: number): string {
  //@ requires 0 <= i && i < s.length
  //@ ensures \result === s.slice(i, i + 1) + s.slice(i, i + 1)
  const c = s[i];
  return c + c;
}

export function indexLength(s: string, i: number): number {
  //@ requires 0 <= i && i < s.length
  //@ ensures \result === 1
  return s[i].length;
}

export function matchesElement(s: string, i: number, needle: string): boolean {
  //@ requires 0 <= i && i < s.length
  //@ ensures \result === (s.slice(i, i + 1) === needle)
  return s[i] === needle && needle === s[i];
}

export function optionalFirst(s?: string): string | undefined {
  //@ requires s !== undefined ==> s.length > 0
  //@ ensures s === undefined ==> \result === undefined
  //@ ensures s !== undefined ==> \result === s.slice(0, 1)
  return s?.[0];
}

export function selectedFirst(s: string, t: string, choose: boolean): string {
  //@ requires s.length > 0 && t.length > 0
  //@ ensures \result === (choose ? s.slice(0, 1) : t.slice(0, 1))
  return (choose ? s : t)[0];
}

export function classifyFirst(s: string): number {
  //@ requires s.length > 0
  //@ ensures \result === (s.slice(0, 1) === "a" ? 1 : (s.slice(0, 1) === "\n" ? 2 : 0))
  const c = s[0];
  switch (c) {
    case "a": return 1;
    case "\n": return 2;
    default: return 0;
  }
}

export function nestedIndex(s: string, i: number): string {
  //@ requires 0 <= i && i < s.length
  //@ ensures \result === s.slice(i, i + 1)
  return s[i][0];
}

export function indexedResult(s: string): string {
  //@ requires s.length > 0
  //@ ensures \result.length === 1 && \result[0] === s[0]
  return s[0];
}

export function arrayElement(xs: string[], i: number, j: number): string {
  //@ requires 0 <= i && i < xs.length && 0 <= j && j < xs[i].length
  //@ ensures \result === xs[i].slice(j, j + 1)
  return xs[i][j];
}

export function sameArrayElements(xs: number[], i: number, j: number): boolean {
  //@ requires 0 <= i && i < xs.length && 0 <= j && j < xs.length
  //@ ensures \result === (xs[i] === xs[j])
  return xs[i] === xs[j];
}
