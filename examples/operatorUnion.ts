//@ backend dafny
export type Op = "==" | "!=";

export function negate(op: Op): Op {
  //@ verify
  //@ ensures \result !== op
  return op === "==" ? "!=" : "==";
}
