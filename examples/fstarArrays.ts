//@ backend fstar

// Capture an immutable array, then supply the transformation separately.
export function mapper<A>(items: A[]): (f: (x: A) => A) => A[] {
  return (f: (x: A) => A): A[] => items.map(f);
}

export function incrementAll(items: number[]): number[] {
  //@ ensures \result.length === items.length
  return mapper(items)((x: number): number => x + 1);
}

export function doublePositives(items: number[]): number[] {
  //@ ensures \result.length <= items.length
  return mapper(items.filter((x: number): boolean => x > 0))(
    (x: number): number => x * 2,
  );
}
