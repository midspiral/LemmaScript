import { stableValue } from "./pure-cross-file-source.js";

export function twoReadsAgree(): boolean {
  //@ verify
  //@ ensures \result === true
  const a = stableValue();
  const b = stableValue();
  return a === b;
}
