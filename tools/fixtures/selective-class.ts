//@ backend dafny

const UNUSED_PATTERN = /outside/;
const BASE = 1;
const STEP = BASE + 1;
const LIMIT = 100;

export class Counter {
  count = 0;
  max = 10;
  written = 0;
  unused: (value: string) => RegExp = value => new RegExp(value);

  increment(): number {
    //@ verify
    //@ requires this.count + STEP <= this.max && this.max <= LIMIT
    //@ ensures this.count <= this.max
    this.written = 1;
    this.count = this.count + STEP;
    return this.count;
  }

  unrelated(): RegExp {
    return /unrelated/;
  }
}
