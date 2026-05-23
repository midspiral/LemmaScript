/**
 * `Array.isArray` narrowing where the scrutinee is a field-access *path*
 * (`m.content`) rather than a bare variable, inside an `&&` condition.
 *
 * `if (m.role === 'assistant' && Array.isArray(m.content)) { ...m.content... }`
 * narrows via `ruleIfAndArrayIsArray` to a `tagMatch` whose scrutinee is the
 * path `m.content`. The transform must emit `match m.content { ... }` and
 * substitute `m.content` references in the matched arm with the variant's
 * payload binder — mirroring how `someMatch` already handles path scrutinees.
 *
 * Mirrors mastra's `sanitizeOrphanedToolPairs`, where
 * `if (current.role === 'assistant' && Array.isArray(current.content))` reads
 * `current.content` (a path) in the body.
 */

//@ backend dafny

//@ declare-type Part { type: string }
//@ declare-type Msg { role: string, content: string | Part[] }

export function countAssistantParts(msgs: Msg[]): number {
  //@ verify
  //@ type i nat
  //@ ensures \result >= 0
  let n = 0;
  for (let i = 0; i < msgs.length; i = i + 1) {
    //@ invariant i <= msgs.length
    //@ invariant n >= 0
    //@ decreases msgs.length - i
    const m = msgs[i]!;
    if (m.role === 'assistant' && Array.isArray(m.content)) {
      n = n + m.content.length;
    }
  }
  return n;
}
