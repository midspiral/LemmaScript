/**
 * `typeof x === "string"` as the string-branch discriminator for a `string | T[]`
 * union — the dual of `Array.isArray`. LemmaScript synthesizes the tagged union at
 * the boundary, and `typeof x === "string" ? a : b` lowers to a tag match on the
 * `NonArrayBranch` (string) side: `a` sees `x` as the string payload, `b` as the
 * array payload.
 *
 * The narrowing fires ONLY when the non-array branch is actually `string` — the
 * runtime `=== "string"` test matches that branch only then. For e.g. `number | T[]`
 * it would never hold, so LemmaScript does not narrow (and `typeof` stays
 * unsupported there). Mirrors the brownfield shape in pi's `convertToLlm`, where
 * `content: string | (TextContent | ImageContent)[]` is dispatched with `typeof`.
 */

//@ backend dafny

interface Part {
  type: string;
  toolCallId: string;
}

/** Length of the text when content is a string, else the number of parts. The
 *  `typeof` test narrows `content` to the string payload in the then-branch and
 *  to the array payload in the else-branch (both arms get a binder). */
function contentLength(content: string | Part[]): number {
  //@ verify
  //@ ensures !Array.isArray(content) ==> \result === content.length
  //@ ensures Array.isArray(content) ==> \result === content.length
  return typeof content === "string" ? content.length : content.length;
}
