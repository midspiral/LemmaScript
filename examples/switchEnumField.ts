/**
 * `switch` on an enum-typed field of a plain record (not a discriminated union).
 * `switch(it.tag)` is matched on the enum value `it.tag` directly — earlier it was
 * mis-lowered to `match it` (treating `it` as a union with `tag` as discriminant),
 * which Dafny rejected. The fix: only treat `x.f` as a discriminant access when
 * `x` is actually a discriminated union with discriminant `f`.
 */

type Tag = "read" | "write" | "exec";
interface Perm { tag: Tag; level: number }

/** Numeric weight per permission tag. */
export function weight(p: Perm): number {
  //@ verify
  //@ ensures \result >= 1
  switch (p.tag) {
    case "read":
      return 1;
    case "write":
      return 2;
    case "exec":
      return 3;
  }
}

/** Plain strings use literal-valued cases, not datatype constructors. */
export function pickPlainString(kind: string): number {
  //@ verify
  //@ ensures \result >= 0
  switch (kind) {
    case "small":  return 1;
    case "medium": return 2;
    case "large":  return 3;
    case "15m":    return 4;
    default:       return 0;
  }
}
