/**
 * Builtin registry — the single classification table for builtin methods on
 * collection/string receivers (DESIGN_LS_IN_LS.md §3).
 *
 * One stable `BuiltinId` per supported operation, one entry per identity.
 * `resolve` recognizes `(receiver type kind, method name)` once — via
 * `recognizeBuiltin` — and stamps the typed call node (and optChain call
 * steps) with the id. Downstream, `narrow` reads `pure` and `transform`
 * reads `hof`/`intArgPositions` from the stamp; neither re-recognizes by
 * spelling. The emitters are deliberately NOT keyed on the stamp: they
 * dispatch on `(objTy, method)` over the backend IR, where transform
 * legitimately synthesizes method calls with no source-level identity.
 *
 * The registry holds classification only — no lowerings. Namespace builtins
 * (`Math.*`, `Array.isArray`) are recognized syntactically in resolve and
 * are not registry entries: they are not methods on receiver values.
 *
 * Classification values mirror the historical per-pass lists exactly
 * (byte-for-byte gauntlet compatibility), including their quirks — e.g.
 * `array.shift` returns the element type un-wrapped, `array.with` types as
 * `unknown`, and `pure` reproduces narrow's old PURE_BUILTIN_METHODS set
 * (so `startsWith` is not `pure` even though it lowers purely). Widen such
 * bits deliberately, with tests — not while migrating.
 */

import type { Ty, TExpr } from "./typedir.js";

export type RecvKind = "array" | "string" | "map" | "set";

export type BuiltinId =
  // array
  | "array.includes" | "array.indexOf" | "array.shift" | "array.pop"
  | "array.push" | "array.unshift" | "array.concat" | "array.sort"
  | "array.filter" | "array.every" | "array.some" | "array.reduce"
  | "array.find" | "array.findLast" | "array.findIndex" | "array.findLastIndex"
  | "array.flat" | "array.slice" | "array.join" | "array.map" | "array.with"
  // string
  | "string.trim" | "string.trimEnd" | "string.trimStart"
  | "string.toLowerCase" | "string.toUpperCase" | "string.slice"
  | "string.substring" | "string.split" | "string.includes"
  | "string.startsWith" | "string.endsWith"
  // map
  | "map.get" | "map.has" | "map.set" | "map.delete" | "map.keys" | "map.values"
  // set
  | "set.has" | "set.add" | "set.delete";

export interface BuiltinSpec {
  recv: RecvKind;                     // recognition key: receiver type kind
  method: string;                     // recognition key: surface method name
  /** Return-type rule. `inSpec` matters for `map.get` (raw value in specs,
   *  Option in code). */
  ret(objTy: Ty, args: TExpr[], c: { inSpec: boolean }): Ty;
  /** Lowers to a pure backend expression (`x in s`, `|s|`, `s.Keys`, …) —
   *  safe inside match arms even with `callKind: "method"`. */
  pure: boolean;
  /** Takes a lambda whose params are inferred from the receiver:
   *  unary (elem), comparator (elem, elem), reduce (acc, elem). */
  hof?: { shape: "unary" | "comparator" | "reduce" };
  /** Arg positions that must be nat in Lean (array index args). */
  intArgPositions?: number[];
  /** Arg 0 is a membership key/element of the receiver collection — drives
   *  quantifier-variable type inference (`forall k … m.has(k)`). */
  argIsKey?: boolean;
}

const UNKNOWN: Ty = { kind: "unknown" };
const BOOL = (): Ty => ({ kind: "bool" });
const INT = (): Ty => ({ kind: "int" });
const STRING = (): Ty => ({ kind: "string" });
const self = (objTy: Ty): Ty => objTy;
const elem = (objTy: Ty): Ty => objTy.kind === "array" ? objTy.elem : UNKNOWN;
const optElem = (objTy: Ty): Ty =>
  objTy.kind === "array" ? { kind: "optional", inner: objTy.elem } : UNKNOWN;

export const BUILTINS: Record<BuiltinId, BuiltinSpec> = {
  // ── array ─────────────────────────────────────────────────
  "array.includes": { recv: "array", method: "includes", ret: BOOL, pure: true,
    intArgPositions: [1], argIsKey: true },
  "array.indexOf": { recv: "array", method: "indexOf", ret: INT, pure: false,
    intArgPositions: [1] },
  "array.shift": { recv: "array", method: "shift", ret: elem, pure: false },
  "array.pop": { recv: "array", method: "pop", ret: optElem, pure: false },
  "array.push": { recv: "array", method: "push", ret: self, pure: false },
  "array.unshift": { recv: "array", method: "unshift", ret: self, pure: false },
  "array.concat": { recv: "array", method: "concat", ret: self, pure: false },
  "array.sort": { recv: "array", method: "sort", ret: self, pure: false,
    hof: { shape: "comparator" } },
  "array.filter": { recv: "array", method: "filter", ret: self, pure: false,
    hof: { shape: "unary" } },
  "array.every": { recv: "array", method: "every", ret: BOOL, pure: false,
    hof: { shape: "unary" } },
  "array.some": { recv: "array", method: "some", ret: BOOL, pure: false,
    hof: { shape: "unary" } },
  "array.reduce": { recv: "array", method: "reduce", pure: false,
    hof: { shape: "reduce" },
    ret: (_objTy, args) => args.length === 2 ? args[1].ty : UNKNOWN },
  "array.find": { recv: "array", method: "find", ret: optElem, pure: false,
    hof: { shape: "unary" } },
  "array.findLast": { recv: "array", method: "findLast", ret: optElem, pure: false,
    hof: { shape: "unary" } },
  "array.findIndex": { recv: "array", method: "findIndex", ret: INT, pure: false,
    hof: { shape: "unary" } },
  "array.findLastIndex": { recv: "array", method: "findLastIndex", ret: INT,
    pure: false, hof: { shape: "unary" } },
  "array.flat": { recv: "array", method: "flat", pure: false,
    ret: (objTy) => objTy.kind === "array" && objTy.elem.kind === "array"
      ? { kind: "array", elem: objTy.elem.elem } : UNKNOWN },
  "array.slice": { recv: "array", method: "slice", ret: self, pure: false },
  "array.join": { recv: "array", method: "join", pure: false,
    ret: (objTy) => objTy.kind === "array" && objTy.elem.kind === "string"
      ? STRING() : UNKNOWN },
  "array.map": { recv: "array", method: "map", pure: false,
    hof: { shape: "unary" },
    // Prefer the lambda's declared return type (handles multi-statement bodies
    // where body[0] is an `if`, not a `return`); fall back to the body's return.
    ret: (_objTy, args) => {
      if (args.length >= 1 && args[0].kind === "lambda") {
        const lam = args[0];
        const retTy: Ty = lam.ty.kind === "fn" ? lam.ty.result
          : lam.body.length > 0 && lam.body[0].kind === "return" ? lam.body[0].value.ty : UNKNOWN;
        return { kind: "array", elem: retTy };
      }
      return UNKNOWN;
    } },
  "array.with": { recv: "array", method: "with", ret: () => UNKNOWN, pure: false,
    intArgPositions: [0] },

  // ── string ────────────────────────────────────────────────
  "string.trim": { recv: "string", method: "trim", ret: STRING, pure: false },
  "string.trimEnd": { recv: "string", method: "trimEnd", ret: STRING, pure: false },
  "string.trimStart": { recv: "string", method: "trimStart", ret: STRING, pure: false },
  "string.toLowerCase": { recv: "string", method: "toLowerCase", ret: STRING, pure: false },
  "string.toUpperCase": { recv: "string", method: "toUpperCase", ret: STRING, pure: false },
  "string.slice": { recv: "string", method: "slice", ret: STRING, pure: false },
  "string.substring": { recv: "string", method: "substring", ret: STRING, pure: false },
  "string.split": { recv: "string", method: "split", pure: false,
    ret: () => ({ kind: "array", elem: { kind: "string" } }) },
  "string.includes": { recv: "string", method: "includes", ret: BOOL, pure: true },
  "string.startsWith": { recv: "string", method: "startsWith", ret: BOOL, pure: false },
  "string.endsWith": { recv: "string", method: "endsWith", ret: BOOL, pure: false },

  // ── map ───────────────────────────────────────────────────
  "map.get": { recv: "map", method: "get", pure: false, argIsKey: true,
    ret: (objTy, _args, c) => objTy.kind !== "map" ? UNKNOWN
      : c.inSpec ? objTy.value : { kind: "optional", inner: objTy.value } },
  "map.has": { recv: "map", method: "has", ret: BOOL, pure: true, argIsKey: true },
  "map.set": { recv: "map", method: "set", ret: self, pure: false },
  "map.delete": { recv: "map", method: "delete", ret: self, pure: false },
  "map.keys": { recv: "map", method: "keys", ret: () => UNKNOWN, pure: true },
  "map.values": { recv: "map", method: "values", ret: () => UNKNOWN, pure: true },

  // ── set ───────────────────────────────────────────────────
  "set.has": { recv: "set", method: "has", ret: BOOL, pure: true, argIsKey: true },
  "set.add": { recv: "set", method: "add", ret: self, pure: false },
  "set.delete": { recv: "set", method: "delete", ret: self, pure: false },
};

/** Recognition index, derived from the table: `(recv, method) → BuiltinId`. */
const INDEX = new Map<string, BuiltinId>();
for (const [id, spec] of Object.entries(BUILTINS) as [BuiltinId, BuiltinSpec][]) {
  INDEX.set(`${spec.recv}.${spec.method}`, id);
}

/** Recognize a builtin method call by receiver type kind + method name.
 *  Called by resolve (once per call node); everything downstream reads the
 *  stamped id. */
export function recognizeBuiltin(objTy: Ty, method: string): BuiltinId | null {
  const k = objTy.kind;
  if (k !== "array" && k !== "string" && k !== "map" && k !== "set") return null;
  return INDEX.get(`${k}.${method}`) ?? null;
}

export function builtinSpec(id: BuiltinId): BuiltinSpec {
  return BUILTINS[id];
}
