const outer = 13;

//@ ensures \result === p
export function bareBlock(p: number): number {
  { const p = 5; }
  return p;
}

//@ ensures \result === p
export function branchLocal(p: number, flag: boolean): number {
  if (flag) { const p = 5; }
  else { const p = 6; }
  return p;
}

//@ ensures \result === p
export function lambdaBranch(p: number, flag: boolean): number {
  return [0].map((x: number): number => {
    if (flag) { const p = 5; }
    return p;
  })[0];
}

//@ ensures p !== undefined ==> \result === p
export function narrowedBlock(p: number | undefined): number {
  if (p !== undefined) {
    { const p = 5; }
    return p;
  }
  return 0;
}

//@ ensures p !== undefined ==> \result === p
export function narrowedBranch(p: number | undefined, flag: boolean): number {
  if (p !== undefined) {
    if (flag) { const p = 5; }
    return p;
  }
  return 0;
}

type Choice = "a" | "b";

//@ ensures \result === p
export function lambdaSwitch(p: number, choice: Choice): number {
  return [0].map((x: number): number => {
    switch (choice) {
      case "a": { const p = 5; break; }
      case "b": { const p = 6; break; }
    }
    return p;
  })[0];
}

//@ ensures \result === p + 7
export function siblingBlocks(p: number): number {
  let total = 0;
  { let p = 2; p++; total += p; }
  { const p = 4; total += p; }
  return total + p;
}

//@ ensures \result === 13
export function globalShadow(): number {
  { const outer = 5; }
  return outer;
}

type Pair = { p: number; text: string };

//@ ensures \result === p
export function destructuredShadow(p: number): number {
  let total = 0;
  {
    const { p }: Pair = { p: 5, text: "p" };
    const record: Pair = { p, text: "p" };
    //@ assert record.p === p && record.text === "p"
    total += record.p;
  }
  {
    const [p] = [7];
    total += p;
  }
  //@ assert total === 12
  return p;
}

//@ ensures \result === p
export function ghostScopes(p: number): number {
  let total = 0;
  //@ ghost let p = 7
  //@ assert p === 7
  {
    //@ ghost let p = 9
    //@ assert p === 9
    const dummy = 0;
    total += dummy;
  }
  //@ assert p === 7
  {
    const p = 11;
    //@ assert p === 11
    total += p;
  }
  //@ assert p === 7
  //@ assert total === 11
  return p;
}

//@ ensures \result === 2 * p + 5
export function initializedClosure(p: number): number {
  let total = 0;
  {
    const before = p;
    const read = (): number => before;
    { const p = 5; total += p; }
    total += read();
  }
  return total + p;
}

//@ ensures \result === p + 2
export function counterScope(p: number): number {
  let total = 0;
  for (let p = 0; p < 2; p++) {
    //@ invariant 0 <= p && p <= 2
    //@ invariant total === p
    { const p = 9; }
    total++;
  }
  return total + p;
}
