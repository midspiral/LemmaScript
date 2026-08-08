import assert from "node:assert/strict";

import type { RawExpr } from "./src/rawir.js";
import { parseExpr } from "./src/specparser.js";

function shape(expr: RawExpr): string {
  switch (expr.kind) {
    case "var": return expr.name;
    case "num": return String(expr.value);
    case "str": return JSON.stringify(expr.value);
    case "binop": return `(${shape(expr.left)} ${expr.op} ${shape(expr.right)})`;
    case "conditional": return `(${shape(expr.cond)} ? ${shape(expr.then)} : ${shape(expr.else)})`;
    case "call": return `${shape(expr.fn)}(${expr.args.map(shape).join(", ")})`;
    case "index": return `${shape(expr.obj)}[${shape(expr.idx)}]`;
    case "forall": return `forall ${expr.var}:${expr.varType}. ${shape(expr.body)}`;
    default: return expr.kind;
  }
}

const cases: [string, string][] = [
  ["a && b ==> c || d", "((a && b) ==> (c || d))"],
  ["a || b ==> c || d", "((a || b) ==> (c || d))"],
  ["(a ==> b) || c", "((a ==> b) || c)"],
  ["a ==> b ==> c", "(a ==> (b ==> c))"],
  ["a ==> b <==> c", "((a ==> b) <==> c)"],
  ["a <==> b ==> c", "(a <==> (b ==> c))"],
  ["a ==> b ? c : d", "(a ==> (b ? c : d))"],
  ["a ? b ==> c : d", "(a ? (b ==> c) : d)"],
  ["a ? b : c ==> d", "(a ? b : (c ==> d))"],
  ["(a ? b : c) ==> d", "((a ? b : c) ==> d)"],
  ["forall((k: nat) => k < n ==> xs[k] > 0)", "forall k:nat. ((k < n) ==> (xs[k] > 0))"],
  ["s === \"==>\" ==> t === \"<==>\"", "((s === \"==>\") ==> (t === \"<==>\"))"],
  ["s === \"😀\" ==> t === \"ok\"", "((s === \"😀\") ==> (t === \"ok\"))"],
  ["f(a ==> b, c)", "f((a ==> b), c)"],
  ["0.6 <= x ==> x < 1.2", "((0.6 <= x) ==> (x < 1.2))"],
];

for (const [source, expected] of cases) {
  assert.equal(shape(parseExpr(source)), expected, source);
}
