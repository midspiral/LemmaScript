// A call's precondition must hold only when its source branch is selected.
// Local mutation makes checkedIncrement a method in both verification backends.
export function checkedIncrement(enabled: boolean, value: number): number {
  //@ requires enabled
  //@ ensures \result === value + 1
  if (!enabled) throw new Error("unselected call");
  let result = value;
  result += 1;
  return result;
}

export function chooseThen(enabled: boolean): number {
  //@ ensures enabled ==> \result === 1
  //@ ensures !enabled ==> \result === -1
  return enabled ? checkedIncrement(enabled, 0) : -1;
}

export function chooseElse(enabled: boolean): number {
  //@ ensures enabled ==> \result === -1
  //@ ensures !enabled ==> \result === 1
  return enabled ? -1 : checkedIncrement(!enabled, 0);
}

export function chooseBoth(enabled: boolean): number {
  //@ ensures enabled ==> \result === 1
  //@ ensures !enabled ==> \result === 2
  return enabled ? checkedIncrement(enabled, 0) : checkedIncrement(!enabled, 1);
}

export function guardedAnd(enabled: boolean): boolean {
  //@ ensures \result === enabled
  return enabled && checkedIncrement(enabled, 0) === 1;
}

export function guardedOr(enabled: boolean): boolean {
  //@ ensures \result
  return enabled || checkedIncrement(!enabled, 0) === 1;
}

export function nestedChoice(first: boolean, second: boolean): number {
  //@ ensures first && second ==> \result === 1
  //@ ensures first && !second ==> \result === 2
  //@ ensures !first ==> \result === 3
  return first
    ? second ? checkedIncrement(first && second, 0) : checkedIncrement(first && !second, 1)
    : checkedIncrement(!first, 2);
}

export function choiceArgument(enabled: boolean): number {
  //@ ensures enabled ==> \result === 2
  //@ ensures !enabled ==> \result === 0
  return checkedIncrement(true, enabled ? checkedIncrement(enabled, 0) : -1);
}

export function optionalChoice(enabled: boolean): number | undefined {
  //@ ensures enabled ==> \result === 1
  //@ ensures !enabled ==> \result === undefined
  return enabled ? checkedIncrement(enabled, 0) : undefined;
}
