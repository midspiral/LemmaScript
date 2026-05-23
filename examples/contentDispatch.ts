/**
 * Plain TS union `string | Part[]` discriminated by Array.isArray.
 *
 * LemmaScript synthesizes a tagged datatype at the boundary, narrowing on
 * `Array.isArray(x)` lowers to a tag-predicate (`x.ArrayBranch?` in Dafny),
 * and bare references inside the array branch use the variant's payload
 * binder. Spec implications `Array.isArray(x) ==> B` and `!Array.isArray(x) ==> B`
 * narrow x inside the conclusion.
 *
 * Mirrors the brownfield shape from mastra-ai/mastra
 * `sanitizeOrphanedToolPairs` (PR #16201) where `m.content: string | Part[]`.
 */

//@ backend dafny

interface Part {
  type: string;
  toolCallId: string;
}

/**
 * Return the parts if content is an array, otherwise empty.
 */
function partsOrEmpty(content: string | Part[]): Part[] {
  //@ verify
  //@ ensures Array.isArray(content) ==> \result.length === content.length
  //@ ensures !Array.isArray(content) ==> \result.length === 0
  if (Array.isArray(content)) {
    return content;
  }
  return [];
}
