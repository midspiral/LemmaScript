export interface Box { val?: number }

//@ requires input === 1
//@ ensures \result === 5
export function reassignInIf(input?: number): number {
  let x = input;
  if (x !== undefined) {
    x = 5;
    return x;
  }
  return 0;
}

//@ requires input === 1
//@ ensures \result === 5
export function reassignAfterEarlyReturn(input?: number): number {
  let x = input;
  if (x === undefined) {
    return 0;
  }
  x = 5;
  return x;
}

//@ requires input.val === 1
//@ ensures \result === 5
export function reassignOptionalField(input: Box): number {
  let box = input;
  if (box.val !== undefined) {
    box.val = 5;
    return box.val;
  }
  return 0;
}
