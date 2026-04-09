/**
 * Simple class example — verified counter with bounds.
 * Dafny backend only (Lean class support not yet implemented).
 */
//@ backend dafny

export class Counter {
  private count: number;
  private max: number;

  constructor(max: number) {
    this.count = 0;
    this.max = max;
  }

  increment(): number {
    //@ verify
    //@ requires this.count < this.max
    //@ ensures this.count <= this.max
    const old = this.count;
    this.count = this.count + 1;
    return old;
  }

  getCount(): number {
    //@ verify
    //@ ensures \result === this.count
    return this.count;
  }

  isAtMax(): boolean {
    //@ verify
    //@ ensures \result === (this.count >= this.max)
    return this.count >= this.max;
  }
}
