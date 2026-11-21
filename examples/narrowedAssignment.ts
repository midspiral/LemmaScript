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
