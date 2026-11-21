//@ backend dafny

// An audience can be a single string or a list. Construct both forms and
// normalize them to arrays, preserving the audience values.

export interface Claims {
  readonly aud: string | readonly string[];
}

export function makeLiteralClaims(): Claims {
  //@ verify
  return { aud: "one" };
}

export function makeStringClaims(aud: string): Claims {
  //@ verify
  return { aud };
}

export function makeArrayClaims(): Claims {
  //@ verify
  return { aud: ["one", "two"] };
}

function audiences(aud: string | readonly string[]): string[] {
  //@ verify
  if (Array.isArray(aud)) return [...aud];
  return [`${aud}`];
}

// The literal is a string payload in the union, and arrives unchanged.
export function literalAudiences(): string[] {
  //@ verify
  //@ ensures \result.length === 1
  //@ ensures \result[0] === "one"
  return audiences(makeLiteralClaims().aud);
}

// The same conversion works for any supplied string, including the empty one.
export function stringAudiences(aud: string): string[] {
  //@ verify
  //@ ensures \result.length === 1
  //@ ensures \result[0] === aud
  return audiences(makeStringClaims(aud).aud);
}

// The array branch preserves both entries and their order.
export function arrayAudiences(): string[] {
  //@ verify
  //@ ensures \result.length === 2
  //@ ensures \result[0] === "one" && \result[1] === "two"
  return audiences(makeArrayClaims().aud);
}
