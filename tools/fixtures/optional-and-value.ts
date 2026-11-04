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
