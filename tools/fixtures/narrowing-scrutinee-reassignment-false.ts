// Negative verification regression fixture: every `ensures` clause here is
// deliberately FALSE in JavaScript. If a switch/tagMatch arm keeps substituting
// its stale match binder (or keeps its variant write-back frame active) after
// reassigning the scrutinee variable, Dafny unsoundly proves the false contract.

export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
export type PairShape = { kind: "a"; x: number; y: number } | { kind: "b"; n: number };

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1 && \result[0] === 0
export function callbackAfterReassignment(input: Shape, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, n: 5 };
      return xs.map(x => x + sh.n);
    case "b":
      return [];
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ ensures \result === 0
export function directAfterReassignment(input: Shape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, n: 5 };
      return sh.n;
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1 && \result[0] === 0
export function ifTagAfterReassignment(input: Shape, xs: number[]): number[] {
  let sh = input;
  if (sh.kind === "a") {
    sh = { ...sh, n: 5 };
    return xs.map(x => x + sh.n);
  }
  return [];
}

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1 && \result[0] === 0
export function defaultArmAfterReassignment(input: Shape, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "b":
      return [];
    default:
      sh = { ...sh, n: 5 };
      return xs.map(x => x + sh.n);
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ requires flag === true
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1 && \result[0] === 0
export function conditionalReassignment(input: Shape, flag: boolean, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "a":
      if (flag) {
        sh = { ...sh, n: 5 };
      }
      return xs.map(x => x + sh.n);
    case "b":
      return [];
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ ensures \result === 0
export function whileLoopReassignment(input: Shape): number {
  let sh = input;
  switch (sh.kind) {
    case "a": {
      let sum = 0;
      let i = 0;
      while (i < 2) {
        //@ invariant 0 <= i && i <= 2
        //@ invariant sh.kind === "a"
        //@ decreases 2 - i
        sum = sum + sh.n;
        sh = { ...sh, n: 5 };
        i = i + 1;
      }
      return sum;
    }
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.x === 0 && input.y === 0
//@ ensures \result === 10
export function fieldWriteAfterReassignment(input: PairShape): number {
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

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \result.length === 1 && \result[0] === 0
export function crossVariantReassignment(input: Shape, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { kind: "b", n: 5 };
      return xs.map(x => x + sh.n);
    case "b":
      return [];
  }
}
