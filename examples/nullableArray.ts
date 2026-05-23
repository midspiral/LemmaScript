/**
 * `T[] | null` lowering — parallel-array accumulator pattern.
 *
 * Companion to contentDispatch.ts: that example handles `string | Part[]`
 * (a value-level union). This one targets `(Part[] | null)[]` — an array of
 * nullable arrays, used as scratch state alongside the input. The shape
 * mirrors mastra-ai/mastra `sanitizeOrphanedToolPairs` (PR #16201):
 *
 *   const filteredContents = messages.map(m =>
 *     Array.isArray(m.content) ? [...m.content] : null);
 *   for (let i = 0; i < messages.length; i++) {
 *     const cur = filteredContents[i];
 *     if (cur !== null) {
 *       filteredContents[i] = cur.filter(keep);
 *     }
 *   }
 *
 * Status: currently fails. `T | null` already parses as `optional<T>` and
 * lowers to `Option<T>` in Dafny, but several emit/inference paths don't
 * carry the wrap through arrays, narrowed-union payloads, or signatures.
 * See TOOLCHAIN gap notes below — kept in source so the example is the
 * regression target.
 *
 * Gaps surfaced (each independently verifiable by trimming this file):
 *   (a) `messages.map(m => Array.isArray(m.content) ? [...m.content] : null)`
 *       — inside the true branch, `m.content` is narrowed to the synthesized
 *       `ArrayBranch` variant; spread `[...m.content]` should lower to
 *       `m.content.arr` but currently emits `m.content`, leaving the map
 *       result typed as `seq<ArrayOf_..._Or_...>` rather than
 *       `seq<Option<seq<Part>>>`.
 *   (b) `filteredContents[i]!.filter(...)` — the non-null unwrap of an
 *       `optional<array<T>>` indexed cell isn't propagated through the
 *       method-call resolver; the emit reports "Unsupported Dafny method
 *       call: .filter() on user".
 *   (c) Return-type signature `(Part[] | null)[]` round-trips literal TS
 *       syntax to Dafny (`seq<(Part[] | null)>`) instead of
 *       `seq<Option<seq<Part>>>`.
 */

//@ backend dafny

interface Part {
  type: string;
  toolCallId: string;
}

interface Message {
  role: string;
  content: string | Part[];
}

function keep(p: Part): boolean {
  //@ verify
  return p.type !== "tool-call";
}

/**
 * Drop orphan tool-call parts from every assistant message, leaving
 * string-content messages untouched.
 */
export function dropOrphans(messages: Message[]): Message[] {
  //@ verify
  //@ ensures \result.length <= messages.length
  const filteredContents: (Part[] | null)[] = messages.map(m =>
    Array.isArray(m.content) ? [...m.content] : null
  );

  let i = 0;
  while (i < messages.length) {
    //@ type i nat
    //@ invariant i <= messages.length
    //@ invariant filteredContents.length === messages.length
    const cur = filteredContents[i];
    if (cur !== null) {
      filteredContents[i] = cur.filter(keep);
    }
    i = i + 1;
  }

  const result: Message[] = [];
  let j = 0;
  while (j < messages.length) {
    //@ type j nat
    //@ invariant j <= messages.length
    //@ invariant result.length <= j
    const f = filteredContents[j];
    if (f === null) {
      result.push(messages[j]);
    } else if (f.length > 0) {
      result.push({ role: messages[j].role, content: f });
    }
    j = j + 1;
  }
  return result;
}
