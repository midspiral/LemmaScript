//@ backend dafny

// Control characters must be escaped in generated Dafny string literals.
export function isBlank(c: string): boolean {
  //@ verify
  //@ ensures \result === (c.length === 1 && (c.charCodeAt(0) === 9 || c.charCodeAt(0) === 10 || c.charCodeAt(0) === 13))
  return c === "\t" || c === "\n" || c === "\r";
}

// Numeric codes check the decoded values independently of literal spelling.
export function controlCodes(): boolean {
  //@ verify
  //@ ensures \result === true
  const text = "\0\t\n\r\b\v\f\x1b\x1f\x7f\u0085\u009f\u2028\u2029";
  return text.length === 14
    && text.charCodeAt(0) === 0
    && text.charCodeAt(1) === 9
    && text.charCodeAt(2) === 10
    && text.charCodeAt(3) === 13
    && text.charCodeAt(4) === 8
    && text.charCodeAt(5) === 11
    && text.charCodeAt(6) === 12
    && text.charCodeAt(7) === 27
    && text.charCodeAt(8) === 31
    && text.charCodeAt(9) === 127
    && text.charCodeAt(10) === 133
    && text.charCodeAt(11) === 159
    && text.charCodeAt(12) === 8232
    && text.charCodeAt(13) === 8233;
}

// Preserve quotes, literal backslashes, and printable Unicode beside controls.
export function mixedText(): boolean {
  //@ verify
  //@ ensures \result === true
  const text = "\t\"é\"\\t\r\n\0" + "7";
  return text.length === 10
    && text.charCodeAt(0) === 9
    && text.charCodeAt(1) === 34
    && text.charCodeAt(2) === 233
    && text.charCodeAt(3) === 34
    && text.charCodeAt(4) === 92
    && text.charCodeAt(5) === 116
    && text.charCodeAt(6) === 13
    && text.charCodeAt(7) === 10
    && text.charCodeAt(8) === 0
    && text.charCodeAt(9) === 55;
}
