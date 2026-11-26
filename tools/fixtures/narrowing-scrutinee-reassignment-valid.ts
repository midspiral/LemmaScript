// Positive verification regression fixture: after a union switch/tagMatch
// scrutinee is reassigned, reads (direct and in callbacks) and subsequent field
// writes observe the reassigned value rather than stale match binders.

export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
export type PairShape = { kind: "a"; x: number; y: number } | { kind: "b"; n: number };
export type Msg = { u: number[] | number };

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1 && \result[0] === 5
export function callbackAfterReassignmentOk(input: Shape, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, n: 5 };
      return xs.map(x => x + sh.n);
    case "b":
      return [];
  }
}

//@ requires input.kind === "a" && input.n === 2
//@ ensures \result === 7
export function rhsReadsOldBinder(input: Shape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, n: sh.n + 5 };
      return sh.n;
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.x === 0 && input.y === 0
//@ ensures \result === 15
export function fieldWriteAfterReassignmentOk(input: PairShape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, x: 5 };
      sh.y = 10;
      return sh.x + sh.y;
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.x === 0 && input.y === 0
//@ ensures \result === 15
export function fieldWriteBeforeReassignmentOk(input: PairShape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh.y = 10;
      sh = { ...sh, x: 5 };
      return sh.x + sh.y;
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1
//@ ensures flag ==> \result[0] === 5
//@ ensures !flag ==> \result[0] === 0
export function elseBranchStillUsesBinder(input: Shape, flag: boolean, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "a":
      if (flag) {
        sh = { ...sh, n: 5 };
      } else {
        return xs.map(x => x + sh.n);
      }
      return xs.map(x => x + sh.n);
    case "b":
      return [];
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1 && \result[0] === 5
export function crossVariantReassignmentOk(input: Shape, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { kind: "b", n: 5 };
      return xs.map(x => x + sh.n);
    case "b":
      return [];
  }
}

//@ requires Array.isArray(input)
//@ ensures !Array.isArray(\result)
export function synthArrayUnionReassigned(input: number[] | number): number[] | number {
  let u = input;
  if (Array.isArray(u)) {
    u = 42;
    return u;
  }
  return 0;
}

//@ requires Array.isArray(input.u)
//@ ensures !Array.isArray(\result)
export function pathSynthArrayUnionReassigned(input: Msg): number[] | number {
  let m = input;
  if (Array.isArray(m.u)) {
    m = { u: 42 };
    return m.u;
  }
  return m.u;
}
