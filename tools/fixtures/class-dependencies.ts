const PREFIX = "__";
const INACTIVE = PREFIX + "INACTIVE__";
const LIMIT = 10;
const UNUSED = 99;

interface Runner { epoch: string }
interface Unused { detail: string }

export class State {
  runner!: Runner;
  background!: Promise<Unused>; //@ type unknown

  active(): boolean {
    //@ verify
    //@ ensures \result === (this.runner.epoch !== INACTIVE)
    return this.runner.epoch !== INACTIVE;
  }

  bounded(value: number): number {
    //@ verify
    //@ requires value <= LIMIT
    //@ ensures \result <= LIMIT
    return value;
  }

  async unrelated() {
    await this.background;
  }
}
