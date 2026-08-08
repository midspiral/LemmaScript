/**
 * Union tags that are not valid identifiers.
 *
 * A discriminated union's tag is a source string and may contain characters no
 * identifier has (`"spec-pure"`). The declaration, the patterns, and the
 * constructor *applications* must all spell it the same sanitized way —
 * `spec_pure` in Dafny, `«spec-pure»` in Lean. Applications are the easy one to
 * miss: they go through a different emit path than declarations and patterns.
 */

type CallKind =
  | { kind: "spec-pure"; depth: number }
  | { kind: "plain" };

export function depthOf(k: CallKind): number {
  //@ verify
  //@ ensures $result >= 0
  switch (k.kind) {
    case "spec-pure":
      return k.depth >= 0 ? k.depth : 0;
    case "plain":
      return 0;
  }
}

// Populated constructor application — the case the sanitizer originally missed.
export function specPure(depth: number): CallKind {
  //@ verify
  return { kind: "spec-pure", depth };
}

// Nullary constructor application, for contrast.
export function plain(): CallKind {
  //@ verify
  return { kind: "plain" };
}
