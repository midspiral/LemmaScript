/**
 * Discriminated-union variants that share a field *name* with different types.
 *
 * `LabelEntry.targetId` is `string`; `LeafEntry.targetId` is `string |
 * undefined`. Dafny requires a destructor shared across a datatype's
 * constructors to have a single type, so the naive lowering
 * (`label(targetId: string) | leaf(targetId: string?)`) is rejected. LemmaScript
 * detects the collision and makes those destructors per-constructor unique
 * (`targetId_label` / `targetId_leaf`). Safe because variant-field reads lower
 * to positional match bindings — a name shared with differing types isn't even
 * accessible on the union in TS, so nothing references the old destructor.
 */

//@ backend dafny

interface LabelEntry { type: "label"; targetId: string }
interface LeafEntry { type: "leaf"; targetId: string | undefined }
type TreeEntry = LabelEntry | LeafEntry;

export function countLabels(entries: TreeEntry[]): number {
  //@ verify
  //@ ensures \result >= 0
  let n = 0;
  for (let i = 0; i < entries.length; i++) {
    //@ invariant 0 <= n
    if (entries[i].type === "label") {
      n = n + 1;
    }
  }
  return n;
}
