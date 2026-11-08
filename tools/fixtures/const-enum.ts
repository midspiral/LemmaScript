export const enum Phase {
  Idle,
  Loading,
  Active = 4,
  Alias = Active,
  Next,
  Flag = 1 << 5,
  Negative = -2,
}

export function active(): Phase {
  //@ verify
  //@ ensures \result === Phase.Active
  //@ ensures \result === 4
  return Phase.Active;
}

export function valuesAgree(): boolean {
  //@ verify
  //@ ensures \result
  return Phase.Idle === 0 && Phase.Loading === 1 && Phase.Alias === 4
    && Phase.Next === 5 && Phase.Flag === 32 && Phase.Negative === -2;
}

export function isTruthy(phase: Phase): boolean {
  //@ verify
  //@ ensures \result === (phase !== Phase.Idle)
  if (phase) return true;
  return false;
}

export function bracket(): Phase.Active {
  //@ verify
  //@ ensures \result === Phase["Active"]
  return Phase["Active"];
}
