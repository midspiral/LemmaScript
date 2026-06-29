/**
 * Faithful JS-`switch` → Dafny `match`: C-style fall-through and `break` as the
 * switch exit (not a loop break).
 *
 * - Stacked `case "a": case "b": case "c": body` — the leading labels have no
 *   statements and fall through, so all three share the body (the `match` gets
 *   an arm per label).
 * - A *non-empty* case with no trailing break/return also falls through: its
 *   statements run, then control continues into the next case (`score`).
 * - The body is a `{ … break }` block; that `break` is the *switch* exit and is
 *   dropped, NOT emitted as a `break` of the enclosing `while`. A `break` inside
 *   a nested loop would be kept. See the switch handling in extract.ts.
 */

//@ backend dafny

type Tag = "a" | "b" | "c" | "skip";
interface Item { tag: Tag }

export function collect(items: Item[]): number[] {
  //@ verify
  //@ ensures \result.length <= items.length
  const out: number[] = [];
  let i = 0;
  while (i < items.length) {
    //@ invariant 0 <= i && i <= items.length
    //@ invariant out.length <= i
    //@ decreases items.length - i
    const t = items[i]!.tag;
    switch (t) {
      case "a":
      case "b":
      case "c": {
        out.push(i);
        break;
      }
      case "skip":
        break;
    }
    i = i + 1;
  }
  return out;
}

// Non-empty fall-through: "a" runs `r += 1`, then continues into "b" (`r += 10`);
// "b" stops at its break. Mirrors partial-json-parser's `strip`, where a complete
// "number" token falls into the "string" handling.
export function score(tag: Tag): number {
  //@ verify
  //@ ensures \result >= 0
  let r = 0;
  switch (tag) {
    case "a":
      r = r + 1;
    case "b":
      r = r + 10;
      break;
    case "c":
      r = r + 100;
      break;
    case "skip":
      break;
  }
  return r;
}
