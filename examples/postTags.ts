/**
 * Tag queries over posts — pins the builtin-registry classification paths
 * end to end (builtins.ts):
 *
 * - `hasTagFrom`: two-arg `includes` with an int-typed `from` — the `from`
 *   argument is `intArgPositions` (nat-coerced on Lean, `x in s[from..]`
 *   on Dafny, whose slice bound the requires discharges). An int-typed
 *   `from` matters: a literal is already nat and would skip the coercion.
 * - `visibility`: `includes` in the residual of an
 *   `x !== undefined && rest ? a : b` condition — the ternary rule rewrites
 *   the presence check, and the narrowed path still reaches the call.
 * - `hasTag`: a builtin call as an optional-chain step — the `BuiltinId`
 *   stamp must survive narrow's chain reconstruction (`applyChain`).
 */

interface Post {
  title: string;
  tags?: string[];
}

/** Is `tag` present at or after position `from`? (Resuming a tag scan.) */
export function hasTagFrom(tags: string[], tag: string, from: number): boolean {
  //@ verify
  //@ requires 0 <= from && from <= tags.length
  //@ ensures \result === true ==> exists(k: nat, k < tags.length && tags[k] === tag)
  return tags.includes(tag, from);
}

/** Draft-tagged posts render as drafts; anything else is live. */
export function visibility(post: Post): string {
  //@ verify
  //@ ensures \result === "draft" || \result === "live"
  return post.tags !== undefined && post.tags.includes("draft") ? "draft" : "live";
}

/** Untagged posts have no tags. */
export function hasTag(post: Post, tag: string): boolean {
  //@ verify
  //@ ensures post.tags === undefined ==> \result === false
  return post.tags?.includes(tag) ?? false;
}
