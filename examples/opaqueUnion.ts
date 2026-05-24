/**
 * Opaque fall-through for a union LemmaScript can't model as a tagged union.
 *
 * `content` below is `string | (TextContent | ImageContent)[]`. The array
 * element `TextContent | ImageContent` has no runtime test LemmaScript can map
 * to a tag (in real code these are often unreachable imports), so it can't be
 * lowered to a discriminated `datatype`. Rather than emit invalid raw-union
 * Dafny — or unsoundly drop the field, which would collapse distinct entries —
 * LemmaScript synthesizes a single opaque `type Opaque_…(==)`. The field stays
 * present (injectivity preserved); only its contents are uninspectable.
 *
 * Soundness is self-enforcing: an opaque type has no constructor and no tag
 * predicate, so any attempt to build or type-test the value fails to lower. It
 * can only be passed through — the one sound use of a union we can't
 * discriminate. Here `countCustom` reads only the `type` discriminant, never
 * `content`, so it verifies.
 */

//@ backend dafny

interface TextContent { kind: "text"; text: string }
interface ImageContent { kind: "image"; url: string }

interface MessageEntry { type: "message"; role: string }
interface CustomMessageEntry {
  type: "custom_message";
  content: string | (TextContent | ImageContent)[];
  display: boolean;
}
type Entry = MessageEntry | CustomMessageEntry;

export function countCustom(entries: Entry[]): number {
  //@ verify
  //@ ensures \result >= 0
  let n = 0;
  for (let i = 0; i < entries.length; i++) {
    //@ invariant 0 <= n
    if (entries[i].type === "custom_message") {
      n = n + 1;
    }
  }
  return n;
}
