/**
 * Pins the registry's `pure` bit (builtins.ts) at the one position that
 * consults it: narrow's `containsMethodCall`, guarding the
 * `x !== undefined && rest ? a : b` ternary rule.
 *
 * Only calls rebuilt from an optional chain carry `callKind: "method"`, so
 * this shape — a builtin reached through `?.`, inside the residual of a
 * presence check — is what reaches the flag. A direct `post.title.endsWith(s)`
 * never does.
 *
 * If `string.endsWith` were marked impure the rule would decline, leaving the
 * guard to reference the still-optional `suffix`: `|suffix|` on an
 * `Option<string>`, which Dafny rejects. Declining is not a safe fallback.
 */

//@ backend dafny

interface Post {
  title?: string;
}

export function suffixed(post: Post, suffix: string | undefined): string {
  //@ verify
  //@ ensures \result === "yes" || \result === "no"
  return suffix !== undefined && (post.title?.endsWith(suffix) ?? false) ? "yes" : "no";
}
