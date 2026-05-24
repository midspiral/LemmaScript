/**
 * `//@ declare-type` with a string-literal union.
 *
 * `declare-type` shadows a type so LemmaScript stops resolution at a small
 * surface — needed when the real type is unreachable across an unresolved
 * import. A string-literal-union RHS now becomes an enum `datatype` (the shape a
 * real string-union resolves to), so `switch` lowers to a Dafny `match` and
 * `=== "lit"` to a discriminant test (`x.lit?`). Previously the declare-type
 * path emitted an invalid `type Role = "user" | …`. See `parseDeclareType`.
 *
 * (The real TS `Role`/`Msg` below stand in for the imported types; `declare-type`
 * shadows them — `tsc` needs them present, LemmaScript uses the shadow.)
 */

//@ backend dafny

type Role = "user" | "assistant" | "toolResult";
interface Msg { role: Role }

//@ declare-type Role = "user" | "assistant" | "toolResult"

export function roleTag(m: Msg): string {
  //@ verify
  //@ ensures true
  const role = m.role;
  switch (role) {
    case "user": return "u";
    case "assistant": return "a";
    case "toolResult": return "t";
  }
}

export function isToolResult(m: Msg): boolean {
  //@ verify
  //@ ensures \result === (m.role === "toolResult")
  return m.role === "toolResult";
}
