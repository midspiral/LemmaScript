/**
 * A chain of `if (s.kind === "v")` lowers to a tag-match. Trailing statements
 * after the chain run for every variant, so a non-terminating case body must
 * continue into them — not have the tail mis-routed into the default arm only.
 */

type Shape = { kind: "circle" } | { kind: "square" } | { kind: "triangle" };

export function classify(s: Shape): string {
  if (s.kind === "circle") return "round";
  if (s.kind === "square") return "boxy";
  return "other";
}

export function tally(s: Shape): number {
  //@ ensures \result >= 10
  let n = 0;
  if (s.kind === "circle") { n = 1; }
  if (s.kind === "square") { n = 2; }
  return n + 10;
}
