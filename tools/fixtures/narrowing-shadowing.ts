// Narrowing replaces a narrowed name with its match binder. An inner
// declaration of the same name must stop that replacement (#351).

export type Shape = { kind: "a"; v: number } | { kind: "b"; w: number };

//@ ensures p !== undefined ==> \result === 1
export function shadowLet(p: number | undefined): number {
  if (p !== undefined) {
    const p = 1;
    return p;
  }
  return 0;
}

//@ ensures p !== undefined && flag ==> \result === p * 10 + 1
//@ ensures p !== undefined && !flag ==> \result === p
export function shadowInNestedBlock(p: number | undefined, flag: boolean): number {
  if (p !== undefined) {
    const before = p;
    if (flag) {
      const p = 1;
      return before * 10 + p;
    }
    return p;
  }
  return 0;
}

// The loop variable is a number and the narrowed `p` is a string, so Dafny
// rejects the loop body if it reads the binder of the outer `p`.
export function shadowForOf(p: string | undefined, xs: number[]): number {
  if (p !== undefined) {
    let total = 0;
    for (const p of xs) {
      total = total + p;
    }
    return total + p.length;
  }
  return 0;
}

// The quantifier variable is an int and the narrowed `p` is a string, so
// Dafny rejects the assertion if its body reads the binder of the outer `p`.
//@ ensures p !== undefined ==> \result === p.length
export function shadowQuantifier(p: string | undefined, xs: number[]): number {
  if (p !== undefined) {
    //@ assert forall(p: int, 0 <= p && p < xs.length ==> xs[p] === xs[p])
    return p.length;
  }
  return 0;
}

// The `if` without `else` makes this a method, which narrows `s` through a
// different path than the pure functions above.
//@ ensures s.kind === "a" && flag ==> \result === 1
export function shadowUnion(s: Shape, flag: boolean): number {
  if (s.kind === "a") {
    if (flag) {
      const s: Shape = { kind: "a", v: 1 };
      return s.v;
    }
  }
  return 0;
}

//@ ensures s.kind === "a" && flag ==> \result === s.v * 10 + 1
//@ ensures s.kind === "a" && !flag ==> \result === s.v
export function shadowUnionInNestedBlock(s: Shape, flag: boolean): number {
  if (s.kind === "a") {
    const before = s.v;
    if (flag) {
      const s: Shape = { kind: "a", v: 1 };
      return before * 10 + s.v;
    }
    return s.v;
  }
  return 0;
}
