const UNUSED_PATTERN = /outside/;
const BASE = 2;
const STEP = BASE + 1;
const MINIMUM = 0;

//@ verify
const EXPLICIT = BASE + 2;

export function advance(n: number): number {
  //@ verify
  //@ requires n >= MINIMUM
  //@ ensures \result === n + STEP && \result >= MINIMUM
  return n + STEP;
}

function unrelated(): RegExp {
  return /unrelated/;
}
