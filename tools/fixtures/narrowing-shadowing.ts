export function whileShadow(p: number | undefined): number {
  //@ type i nat
  //@ requires p !== undefined && p === 3
  //@ ensures \result === 5
  if (p !== undefined) {
    let total = 0;
    let i = 0;
    while (i < 1) {
      //@ invariant 0 <= i && i <= 1
      //@ invariant total === i * 5
      //@ decreases 1 - i
      const p = 5;
      total += p;
      i++;
    }
    return total;
  }
  return 0;
}

export function forOfShadow(p: number | undefined): number {
  //@ requires p !== undefined && p === 3
  //@ ensures \result === 5
  if (p !== undefined) {
    let total = 0;
    for (const p of [5]) {
      //@ invariant total === _p_idx * 5
      total += p;
    }
    return total;
  }
  return 0;
}

type OptionalValue = { value: number | undefined };
type ConcreteValue = { value: number };

function concreteValue(value: number): ConcreteValue {
  return { value };
}

export function fieldShadow(box: OptionalValue): number {
  //@ type i nat
  //@ requires box.value !== undefined && box.value === 3
  //@ ensures \result === 8
  if (box.value !== undefined) {
    let total = 0;
    let i = 0;
    while (i < 1) {
      //@ invariant 0 <= i && i <= 1
      //@ invariant total === i * 5
      //@ decreases 1 - i
      const box = concreteValue(5);
      total += box.value;
      i++;
    }
    return total + box.value;
  }
  return 0;
}

export function lambdaScopes(p: number | undefined): number {
  //@ requires p !== undefined && p === 3
  //@ ensures \result === 13
  if (p !== undefined) {
    const read = (_: number): number => p;
    const readLocal = (_: number): number => { const p = 5; return p; };
    return [5].map((p: number): number => p)[0] + read(0) + readLocal(0);
  }
  return 0;
}

export function lambdaTernary(p: number | undefined): number {
  //@ requires p !== undefined && p === 3
  //@ ensures \result === 8
  return p !== undefined
    ? [5].map((p: number): number => p)[0] + [0].map((): number => p)[0]
    : 0;
}

export function quantifierScope(p: number | undefined): number {
  //@ requires p !== undefined && p === 3
  //@ ensures \result === 3
  if (p !== undefined) {
    const xs = [5];
    //@ assert xs[0] === 5
    //@ assert exists(p: int, 0 <= p && p < xs.length && xs[p] === 5)
    //@ assert forall(q: int, 0 <= q && q < xs.length ==> xs[q] === p + 2)
    return p;
  }
  return 0;
}
