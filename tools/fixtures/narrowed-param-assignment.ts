// A parameter assigned only inside a narrowed block still needs a mutable copy.

export function inOptionalBlock(p: number, o?: number): number {
  if (o !== undefined) { p = p + o; }
  return p;
}

export type Shape = { kind: "circle"; r: number } | { kind: "square"; s: number };

export function inUnionArm(p: number, sh: Shape): number {
  if (sh.kind === "circle") { p = p + sh.r; }
  return p;
}
