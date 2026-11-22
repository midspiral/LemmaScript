// Regression fixture for #353: narrowing substitution must reach lambda bodies
// and loop decreases/done_with clauses, and must stop at a lambda parameter
// that rebinds the narrowed name.

export function closureReadsNarrowed(o: number | undefined, xs: number[]): number[] {
  if (o !== undefined) {
    return xs.map((x) => x + o);
  }
  return [];
}

export function blockClosureReadsNarrowed(o: number | undefined, xs: number[]): number[] {
  if (o !== undefined) {
    return xs.map((x) => {
      const y = x + o;
      return y;
    });
  }
  return [];
}

export function predicateReadsNarrowed(o: number | undefined, xs: number[]): boolean {
  if (o !== undefined) {
    return xs.every((x) => x > o);
  }
  return false;
}

export function lambdaParamShadows(p: string | undefined, xs: number[]): number[] {
  if (p !== undefined) {
    return xs.map((p) => p + 1);
  }
  return [];
}

export function whileDecreasesNarrowed(o: number | undefined): number {
  //@ ensures o !== undefined && o >= 0 ==> \result === o
  if (o !== undefined && o >= 0) {
    let i = 0;
    while (i < o) {
      //@ invariant 0 <= i && i <= o
      //@ decreases o - i
      //@ done_with i === o
      i = i + 1;
    }
    return i;
  }
  return 0;
}
