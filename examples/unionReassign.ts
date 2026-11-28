export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
export type Pair = { kind: "a"; x: number; y: number } | { kind: "b"; z: number };
export type Bag = { kind: "empty" } | { kind: "list"; items: number[] };
export type Colliding = { kind: "a"; value: number } | { kind: "b"; value: string };
export type MixedOpt = { kind: "a"; value: number } | { kind: "b"; value: number | undefined };

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

//@ requires input.kind === "list" && input.items.length === 2
//@ ensures \result === 1
export function popUnionField(input: Bag): number {
  let b = input;
  if (b.kind === "list") {
    const last = b.items.pop()!;
    return b.items.length;
  }
  return 0;
}

//@ ensures \result.kind === "a" && \result.value === 5
export function makeA(): Colliding {
  return { kind: "a", value: 5 };
}

//@ ensures sh.kind === "a" ==> (\result.kind === "a" && \result.value === nextVal)
//@ ensures sh.kind === "b" ==> (\result.kind === "b" && \result.value === nextVal)
export function bumpMixed(sh: MixedOpt, nextVal: number): MixedOpt {
  return { ...sh, value: nextVal };
}
