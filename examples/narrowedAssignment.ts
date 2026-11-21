// Assigning to a variable narrowed by `!== undefined` ends the narrowing:
// later reads see the assigned value, never the stale match binder (#342).

export function assignDefined(p: number | undefined): number {
  //@ ensures p !== undefined ==> \result === 5
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o !== undefined) { o = 5; return o; }
  return 0;
}

export function assignFromSelf(p: number | undefined): number {
  //@ ensures p !== undefined ==> \result === p + 2
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o === undefined) return 0;
  o = o + 2;
  return o;
}

export function assignInNestedIf(p: number | undefined, c: boolean): number {
  //@ ensures p !== undefined && c ==> \result === p + 1
  //@ ensures p !== undefined && !c ==> \result === p
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o !== undefined) {
    if (c) { o = o + 1; }
    return o;
  }
  return 0;
}

export function assignInBranchAtTail(p: number | undefined, c: boolean): number {
  //@ ensures p !== undefined && c ==> \result === p + 1
  //@ ensures p !== undefined && !c ==> \result === p
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o === undefined) return 0;
  if (c) { o = o + 1; }
  return o;
}

export function assignUndefinedInBranch(p: number | undefined, c: boolean): number {
  //@ ensures p !== undefined && c ==> \result === 9
  //@ ensures p !== undefined && !c ==> \result === p
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o !== undefined) {
    if (c) { o = undefined; }
    return o ?? 9;
  }
  return 0;
}

export function assignUndefined(p: number | undefined): number {
  //@ ensures p !== undefined ==> \result === 7
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o !== undefined) { o = undefined; return o ?? 7; }
  return 0;
}

export function compareAfterUndefined(p: number | undefined): number {
  //@ ensures p !== undefined ==> \result === 1
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  let t = 0;
  if (o !== undefined) { o = undefined; t = o === undefined ? 1 : 2; }
  return t;
}

export function clearInExitingBranch(p: number | undefined, c: boolean): number {
  //@ ensures p !== undefined && c ==> \result === 1
  //@ ensures p !== undefined && !c ==> \result === p + 1
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o !== undefined) {
    if (c) {
      o = undefined;
      return 1;
    }
    return o + 1;
  }
  return 0;
}

export function assignAndReturnInBranch(p: number | undefined, c: boolean): number {
  //@ ensures p !== undefined && c ==> \result === 5
  //@ ensures p !== undefined && !c ==> \result === p
  //@ ensures p === undefined ==> \result === 0
  let o = p;
  if (o !== undefined) {
    if (c) {
      o = 5;
      return o;
    }
    return o;
  }
  return 0;
}

export interface Box {
  v?: number;
}

export function replaceOwnerInExitingBranch(p: Box, c: boolean): number {
  //@ ensures p.v !== undefined && c ==> \result === 0
  //@ ensures p.v !== undefined && !c ==> \result === p.v + 1
  let b = p;
  if (b.v !== undefined) {
    if (c) {
      b = { v: undefined };
      return 0;
    }
    return b.v + 1;
  }
  return 0;
}

export function rebindGeneric<T>(p: T | undefined, q: T): T | undefined {
  //@ ensures p !== undefined ==> \result === q
  //@ ensures p === undefined ==> \result === undefined
  let o = p;
  if (o !== undefined) {
    o = q;
    return o;
  }
  return undefined;
}
