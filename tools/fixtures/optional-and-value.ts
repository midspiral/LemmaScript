export interface Box { v?: number }

export function belowSet(x: number, opt?: number): boolean {
  //@ ensures x === 1 && opt === 5 ==> \result
  //@ ensures x === 5 && opt === 1 ==> !\result
  //@ ensures opt === undefined ==> !\result
  return opt !== undefined && x < opt;
}

export function nullable(x: number, opt: number | null): boolean {
  //@ ensures x === 1 && opt === 5 ==> \result
  //@ ensures opt === null ==> !\result
  return opt !== null && x < opt;
}

export function arithmetic(x: number, opt?: number): boolean {
  //@ ensures x === 5 && opt === 5 ==> \result
  //@ ensures x === 6 && opt === 5 ==> !\result
  const ok = opt !== undefined && opt + 1 > x;
  return ok;
}

export function both(x: number, a?: number, b?: number): boolean {
  //@ ensures x === 1 && a === 1 && b === 1 ==> \result
  //@ ensures x === 2 && a === 1 && b === 1 ==> !\result
  //@ ensures b === undefined ==> !\result
  return a !== undefined && b !== undefined && x < a + b;
}

export function field(box: Box): boolean {
  //@ ensures box.v === 3 ==> \result
  //@ ensures box.v === 0 ==> !\result
  return box.v !== undefined && box.v > 0;
}

export function inContract(x: number, opt?: number): boolean {
  //@ ensures \result === (opt !== undefined && x < opt)
  if (opt === undefined) return false;
  return x < opt;
}

export function unsetOrAbove(x: number, opt?: number): boolean {
  //@ ensures opt === undefined ==> \result
  //@ ensures x === 5 && opt === 5 ==> \result
  //@ ensures x === 6 && opt === 5 ==> !\result
  return opt === undefined || opt + 1 > x;
}

export function zeroOrAbove(x: number, opt?: number): boolean {
  //@ ensures opt === 0 ==> \result
  //@ ensures x === 6 && opt === 5 ==> !\result
  return !opt || opt + 1 > x;
}

export function orEarlyReturn(x: number, opt?: number): number {
  //@ ensures opt === undefined ==> \result === 1
  //@ ensures x === 6 && opt === 5 ==> \result === 0
  if (opt === undefined || opt + 1 > x) return 1;
  return 0;
}

export function orTernary(x: number, opt?: number): number {
  //@ ensures opt === undefined ==> \result === 1
  //@ ensures x === 6 && opt === 5 ==> \result === 0
  return opt === undefined || opt + 1 > x ? 1 : 0;
}

export function andIfElse(x: number, opt?: number): number {
  //@ ensures opt === undefined ==> \result === 0
  //@ ensures x === 5 && opt === 5 ==> \result === 1
  if (opt !== undefined && opt + 1 > x) {
    return 1;
  } else {
    return 0;
  }
}

export function lowest(xs: number[]): number | null {
  //@ ensures xs.length === 0 ==> \result === null
  //@ ensures xs.length > 0 ==> \result !== null
  //@ ensures forall(k: nat, k < xs.length && \result !== null ==> \result <= xs[k])
  //@ type i nat
  let m: number | null = null;
  for (let i = 0; i < xs.length; i++) {
    //@ invariant 0 <= i && i <= xs.length
    //@ invariant i === 0 ==> m === null
    //@ invariant i > 0 ==> m !== null
    //@ invariant forall(k: nat, k < i && m !== null ==> m <= xs[k])
    //@ decreases xs.length - i
    const x = xs[i]!;
    if (m === null || x < m) m = x;
  }
  return m;
}

export function countAbove(xs: number[], floor?: number): number {
  //@ ensures 0 <= \result && \result <= xs.length
  //@ ensures floor === undefined ==> \result === xs.length
  //@ type i nat
  let n = 0;
  for (let i = 0; i < xs.length; i++) {
    //@ invariant 0 <= i && i <= xs.length
    //@ invariant 0 <= n && n <= i
    //@ invariant floor === undefined ==> n === i
    //@ decreases xs.length - i
    if (floor === undefined || xs[i]! - floor > 0) n = n + 1;
  }
  return n;
}
