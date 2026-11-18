//@ backend dafny

// Regression for #258: optional fields of an inline parameter record retain
// their types throughout a chained ??. A present zero wins over later defaults.

interface Context {
  a?: number;
  b?: number;
}

export function choose(entry: { x: number; y?: number } | undefined, context: Context): number {
  //@ verify
  //@ ensures entry === undefined ==> \result === -1
  //@ ensures entry !== undefined && context.a !== undefined ==> \result === context.a
  //@ ensures entry !== undefined && context.a === undefined && entry.y !== undefined ==> \result === entry.y
  //@ ensures entry !== undefined && context.a === undefined && entry.y === undefined && context.b !== undefined ==> \result === context.b
  //@ ensures entry !== undefined && context.a === undefined && entry.y === undefined && context.b === undefined ==> \result === 0
  if (entry !== undefined) {
    const w = context.a ?? entry.y ?? context.b ?? 0;
    return w;
  }
  return -1;
}

export function keepZero(): number {
  //@ verify
  //@ ensures \result === 0
  return choose({ x: 1, y: 2 }, { a: 0, b: 3 });
}

export function useDefault(): number {
  //@ verify
  //@ ensures \result === 0
  return choose({ x: 1 }, { a: undefined, b: undefined });
}
