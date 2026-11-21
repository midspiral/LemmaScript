//@ backend dafny

// JavaScript case conversion is Unicode-aware ("ß".toUpperCase() is "SS"), so
// the model only pins it down for ASCII input. These facts hold for any ASCII
// string; dropping the ASCII precondition makes them unprovable.

export function lowerKeepsAsciiLength(s: string): boolean {
  //@ requires forall(i: nat, i < s.length ==> s.charCodeAt(i) < 128)
  //@ ensures \result === true
  return s.toLowerCase().length === s.length;
}

export function upperKeepsAsciiLength(s: string): boolean {
  //@ requires forall(i: nat, i < s.length ==> s.charCodeAt(i) < 128)
  //@ ensures \result === true
  return s.toUpperCase().length === s.length;
}

export function shout(): string {
  //@ ensures \result === "HELLO, WORLD!"
  return "Hello, World!".toUpperCase();
}

export function sameLetters(a: string, b: string): boolean {
  //@ ensures a === b ==> \result === true
  return a.toLowerCase() === b.toLowerCase();
}
