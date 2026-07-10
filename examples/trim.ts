//@ backend dafny
/**
 * trim — String.prototype.trim() strips the full ECMAScript WhiteSpace ∪
 * LineTerminator set: ASCII \t \n \v \f \r and space, plus Unicode NBSP,
 * U+1680, the U+2000–U+200A spaces, the line/paragraph separators U+2028/U+2029,
 * U+202F, U+205F, the ideographic space U+3000, and the BOM U+FEFF. It does NOT
 * strip U+0085 (NEL) or U+200B (ZWSP).
 *
 * The Dafny model (StringTrim preamble) mirrors that exact set via
 * IsJSWhitespace. `trimAsciiWs` below is the regression test for the earlier
 * space-only model: it cannot verify unless tab and newline are also stripped.
 * The `//@ skip` runtimeSanityCheck (run via `tsx examples/trim.ts`) exercises
 * the non-ASCII code points against real TS semantics.
 */

export function trimmed(s: string): string {
  //@ ensures \result.length <= s.length
  return s.trim();
}

// Concrete evaluation forces the verifier to strip a leading tab and a trailing
// newline — neither of which the previous space-only StringTrim model removed,
// so this postcondition is the regression test for the discrepancy.
export function trimAsciiWs(): string {
  //@ ensures \result === 'x'
  return '\tx\n'.trim();
}

//@ skip
export function runtimeSanityCheck(): boolean {
  // Code points TS trim() MUST strip (the modeled IsJSWhitespace set).
  const strip = [
    0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x20, 0xa0, 0x1680,
    0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005, 0x2006,
    0x2007, 0x2008, 0x2009, 0x200a,
    0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff,
  ];
  // Common near-misses TS trim() must KEEP (NEL, ZWSP, word-joiner, a letter).
  const keep = [0x85, 0x200b, 0x2060, 0x41];
  for (const cp of strip) {
    const ch = String.fromCharCode(cp);
    if ((ch + "x" + ch).trim() !== "x") return false;
  }
  for (const cp of keep) {
    const ch = String.fromCharCode(cp);
    if ((ch + "x" + ch).trim() === "x") return false;
  }
  return true;
}

//@ skip
if (!runtimeSanityCheck()) {
  throw new Error("trim(): TS runtime disagrees with the verified whitespace model");
}
