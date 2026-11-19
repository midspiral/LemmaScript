/** Adapt JavaScript's indexed callback convention to the unary collection
 * operations shared by both backends. Binding and rest-pack simplification
 * have already happened in resolve; this pass only supplies actual values. */
import type { Expr, Stmt } from "./ir.js";
import { pCtor, usesNameInStmts } from "./ir.js";
import type { Ty } from "./typedir.js";
import type { BuiltinSpec } from "./builtins.js";
import { callbackBaseArity } from "./builtins.js";
import { freshName } from "./names.js";

const INT: Ty = { kind: "int" };
const INDICES: Ty = { kind: "array", elem: INT };
const variable = (name: string): Expr => ({ kind: "var", name });

export function lowerIndexedCallback(
  receiver: Expr, receiverTy: Ty, method: string, args: Expr[],
  shape: NonNullable<BuiltinSpec["hof"]>["shape"], monadic: boolean, id: number,
): Expr | null {
  const callback = args[0];
  if (receiverTy.kind !== "array" || callback?.kind !== "lambda" ||
      callback.params.length <= callbackBaseArity(shape)) return null;

  const sourceName = freshName(`_callbackSource${id}`);
  const indexName = freshName(`_callbackIndex${id}`);
  const accName = freshName(`_callbackAcc${id}`);
  const source = variable(sourceName), index = variable(indexName);
  const element: Expr = { kind: "index", arr: source, idx: { kind: "toNat", expr: index } };
  const values = shape === "reduce" ? [variable(accName), element, index, source] : [element, index, source];
  const elementPosition = shape === "reduce" ? 1 : 0;
  if (receiverTy.elem.kind === "nat" && callback.params[elementPosition].type.kind === "int") {
    values[elementPosition] = { kind: "toInt", expr: element };
  }
  const bindings: Stmt[] = callback.params.flatMap((p, i) =>
    usesNameInStmts(callback.body, p.name)
      ? [{ kind: "let" as const, name: p.name, type: p.type, mutable: false, value: values[i] }]
      : []);
  // Keep the body expression-shaped when possible, as required by Dafny's
  // collection operations. These bindings evaluate only already-bound values.
  let body = callback.body;
  if (body.length === 1 && body[0].kind === "return") {
    let value = body[0].value;
    for (const s of [...bindings].reverse()) {
      if (s.kind === "let") value = { kind: "let", name: s.name, type: s.type, value: s.value, body: value };
    }
    // Backend collection helpers take total callbacks. Extend the callback
    // outside its actual index domain without evaluating its body there.
    // map and some inline the body under membership/bounds instead.
    if (method !== "map" && method !== "some") {
      const valid: Expr = { kind: "binop", op: "∧",
        left: { kind: "binop", op: "≤", left: { kind: "num", value: 0 }, right: index },
        right: { kind: "binop", op: "<", left: index, right: { kind: "field", obj: source, field: "size" } } };
      value = { kind: "if", cond: valid, then: value,
        else: shape === "reduce" ? variable(accName) : { kind: "bool", value: false } };
    }
    body = [{ kind: "return", value }];
  } else body = [...bindings, ...body];
  const adapted: Expr = { kind: "lambda", body, typedParams: true, params: shape === "reduce"
    ? [{ name: accName, type: callback.params[0].type }, { name: indexName, type: INT }]
    : [{ name: indexName, type: INT }] };
  const positions: Expr = { kind: "arrayRange", length: { kind: "field", obj: source, field: "size" } };
  let result: Expr = { kind: "methodCall", obj: positions, objTy: INDICES,
    method, args: [adapted, ...args.slice(1)], monadic };

  // Selection methods return elements; their index-domain versions return
  // positions. Translate the result back without changing order or witnesses.
  if (method === "filter") {
    result = { kind: "methodCall", obj: result, objTy: INDICES, method: "map", monadic: false,
      args: [{ kind: "lambda", typedParams: true, params: [{ name: indexName, type: INT }], body: [{ kind: "return", value: element }] }] };
  } else if (method === "find" || method === "findLast") {
    result = { kind: "match", scrutinee: result, arms: [
      { pattern: pCtor("some", indexName), body: { kind: "constructor", name: "some", args: [element] } },
      { pattern: pCtor("none"), body: { kind: "constructor", name: "none", args: [] } },
    ] };
  }
  return { kind: "let", name: sourceName, type: receiverTy, value: receiver, body: result };
}
