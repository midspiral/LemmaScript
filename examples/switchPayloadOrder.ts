//@ backend dafny
//@ option string-semantics javascript-utf16

interface Deadline { day: string }
type Bound = { tag: "always"; value: boolean } | { tag: "until"; value: Deadline };

function before(bound: Bound, cutoff: string): boolean {
  //@ verify
  switch (bound.tag) {
    case "always": return false;
    case "until": return bound.value.day < cutoff;
  }
}

export function beforeDeadline(day: string, cutoff: string): boolean {
  //@ verify
  //@ ensures \result === (day < cutoff)
  return before({ tag: "until", value: { day } }, cutoff);
}
