// The `ensures` clauses here are deliberately false. Each function declares a
// `const` inside a bare block with the name of an outer variable and reads the
// outer variable after the block. If extract flattens the block without
// renaming, the read after the block sees the inner `const`, and Dafny proves
// the false claim.

//@ ensures \result === 5
export function bareBlock(p: number): number {
  {
    const p = 5;
  }
  return p;
}

//@ ensures \result === 5
export function bareBlockMethod(p: number): number {
  let r = 0;
  {
    const p = 5;
    r = r + p;
  }
  return p;
}

//@ ensures p !== undefined ==> \result === 1
export function bareBlockNarrowed(p: number | undefined): number {
  if (p !== undefined) {
    {
      const p = 1;
    }
    return p;
  }
  return 1;
}
