export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
export type Pair = { kind: "a"; x: number; y: number } | { kind: "b"; z: number };

//@ requires input.kind === "a" && input.n === 0
//@ requires next.kind === "b" && next.n === 7
//@ ensures \result === 7
export function sharedFieldAfterReassignToNext(input: Shape, next: Shape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = next;
      return sh.n;
    case "b":
      return sh.n;
  }
}

//@ requires input.kind === "a" && input.n === 7
//@ ensures \result.kind === "b" && \result.n === 7
export function tagChangingSpread(input: Shape): Shape {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, kind: "b" };
      return sh;
    case "b":
      return sh;
  }
}

//@ requires input.kind === "a" && input.x === 1 && input.y === 2
//@ requires _f1 === 9
//@ ensures \result.kind === "a" && \result.x === 9 && \result.y === 2
export function binderNoCapture(input: Pair, _f1: number): Pair {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh.x = _f1;
      return sh;
    case "b":
      return sh;
  }
}
