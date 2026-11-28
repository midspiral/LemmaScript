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
 */

import type { Ty, TExpr } from "./typedir.js";

export type RecvKind = "array" | "string" | "map" | "set";

export interface BuiltinSpec {
  /** Return-type rule. `inSpec` matters for `map.get` (raw value in specs,
   *  Option in code). */
  ret(objTy: Ty, args: TExpr[], c: { inSpec: boolean }): Ty;
  /** Lowers to a pure backend expression (`x in s`, `|s|`, `s.Keys`, …) —
   *  safe inside match arms even with `callKind: "method"`. */
  pure: boolean;
  /** JavaScript callback convention, including arguments omitted by unary
   *  backend collection operations. */
  hof?: { shape: "element" | "comparator" | "reduce" };
  /** Arg positions that must be nat in Lean (array index args). */
  intArgPositions?: number[];
  /** Arg 0 is a membership key/element of the receiver collection — drives
   *  quantifier-variable type inference (`forall k … m.has(k)`). */
  argIsKey?: boolean;
  /** Expected slot type for argument `index` (used by `resolve` to coerce
   *  narrowed/non-null/literal values to the collection's element/key/value type). */
  argSlot?(objTy: Ty, index: number): Ty | null;
}

const UNKNOWN: Ty = { kind: "unknown" };
const BOOL = (): Ty => ({ kind: "bool" });
const INT = (): Ty => ({ kind: "int" });
const STRING = (): Ty => ({ kind: "string" });
const self = (objTy: Ty): Ty => objTy;
const optElem = (objTy: Ty): Ty =>
  objTy.kind === "array" ? { kind: "optional", inner: objTy.elem } : UNKNOWN;
const arrElemAt0 = (objTy: Ty, i: number): Ty | null =>
  i === 0 && objTy.kind === "array" ? objTy.elem : null;
const arrElemAll = (objTy: Ty): Ty | null =>
  objTy.kind === "array" ? objTy.elem : null;
const arrElemAt1 = (objTy: Ty, i: number): Ty | null =>
  i === 1 && objTy.kind === "array" ? objTy.elem : null;
const mapKeyAt0 = (objTy: Ty, i: number): Ty | null =>
  i === 0 && objTy.kind === "map" ? objTy.key : null;
const mapKeyVal = (objTy: Ty, i: number): Ty | null =>
  objTy.kind === "map" ? (i === 0 ? objTy.key : i === 1 ? objTy.value : null) : null;
const setElemAt0 = (objTy: Ty, i: number): Ty | null =>
  i === 0 && objTy.kind === "set" ? objTy.elem : null;

/** The table is the single source: each key is `<RecvKind>.<method>`, which
 *  *is* the `BuiltinId`. */
export const BUILTINS = {
  // ── array ─────────────────────────────────────────────────
  "array.includes": { ret: BOOL, pure: true,
    intArgPositions: [1], argIsKey: true, argSlot: arrElemAt0 },
  "array.indexOf": { ret: INT, pure: true,
    intArgPositions: [1], argSlot: arrElemAt0 },
  "array.shift": { ret: optElem, pure: false },
  "array.pop": { ret: optElem, pure: false },
  "array.push": { ret: self, pure: false, argSlot: arrElemAll },
  "array.unshift": { ret: self, pure: false, argSlot: arrElemAll },
  "array.concat": { ret: self, pure: true },
  "array.sort": { ret: self, pure: false,
    hof: { shape: "comparator" } },
  "array.filter": { ret: self, pure: false,
    hof: { shape: "element" } },
  "array.every": { ret: BOOL, pure: false,
    hof: { shape: "element" } },
  "array.some": { ret: BOOL, pure: false,
    hof: { shape: "element" } },
  "array.reduce": { pure: false,
    hof: { shape: "reduce" },
    ret: (_objTy, args) => args.length === 2 ? args[1].ty : UNKNOWN },
  "array.find": { ret: optElem, pure: false,
    hof: { shape: "element" } },
  "array.findLast": { ret: optElem, pure: false,
    hof: { shape: "element" } },
  "array.findIndex": { ret: INT, pure: false,
    hof: { shape: "element" } },
  "array.findLastIndex": { ret: INT,
    pure: false, hof: { shape: "element" } },
  "array.flat": { pure: true,
    ret: (objTy) => objTy.kind === "array" && objTy.elem.kind === "array"
      ? { kind: "array", elem: objTy.elem.elem } : UNKNOWN },
  "array.slice": { ret: self, pure: true },
  "array.join": { pure: true,
    ret: (objTy) => objTy.kind === "array" && objTy.elem.kind === "string"
      ? STRING() : UNKNOWN },
  "array.map": { pure: false,
    hof: { shape: "element" },
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
  "array.with": { ret: (objTy) => objTy, pure: true,
    intArgPositions: [0], argSlot: arrElemAt1 },

  // ── string ────────────────────────────────────────────────
  "string.trim": { ret: STRING, pure: true },
  "string.trimEnd": { ret: STRING, pure: true },
  "string.trimStart": { ret: STRING, pure: true },
  "string.toLowerCase": { ret: STRING, pure: true },
  "string.toUpperCase": { ret: STRING, pure: true },
  "string.repeat": { ret: STRING, pure: true },
  "string.slice": { ret: STRING, pure: true },
  "string.substring": { ret: STRING, pure: true },
  "string.split": { pure: true,
    ret: () => ({ kind: "array", elem: { kind: "string" } }) },
  "string.includes": { ret: BOOL, pure: true },
  "string.startsWith": { ret: BOOL, pure: true },
  "string.endsWith": { ret: BOOL, pure: true },

  // ── map ───────────────────────────────────────────────────
  "map.get": { pure: true, argIsKey: true, argSlot: mapKeyAt0,
    ret: (objTy, _args, c) => objTy.kind !== "map" ? UNKNOWN
      : c.inSpec ? objTy.value : { kind: "optional", inner: objTy.value } },
  "map.has": { ret: BOOL, pure: true, argIsKey: true, argSlot: mapKeyAt0 },
  "map.set": { ret: self, pure: false, argSlot: mapKeyVal },
  "map.delete": { ret: self, pure: false, argSlot: mapKeyAt0 },
  "map.keys": { ret: () => UNKNOWN, pure: true },
  "map.values": { ret: () => UNKNOWN, pure: true },

  // ── set ───────────────────────────────────────────────────
  "set.has": { ret: BOOL, pure: true, argIsKey: true, argSlot: setElemAt0 },
  "set.add": { ret: self, pure: false, argSlot: setElemAt0 },
  "set.delete": { ret: self, pure: false, argSlot: setElemAt0 },
} satisfies Record<`${RecvKind}.${string}`, BuiltinSpec>;

/** One id per table entry. */
export type BuiltinId = keyof typeof BUILTINS;

/** Recognize a builtin method call by receiver type kind + method name.
 *  Called by resolve (once per call node); everything downstream reads the
 *  stamped id. `hasOwn`, not `in`: `method` comes from user source, and `in`
 *  would match inherited names (`constructor`, `toString`). */
export function recognizeBuiltin(objTy: Ty, method: string): BuiltinId | null {
  const k = objTy.kind;
  if (k !== "array" && k !== "string" && k !== "map" && k !== "set") return null;
  const id = `${k}.${method}`;
  return Object.hasOwn(BUILTINS, id) ? id as BuiltinId : null;
}

export function builtinSpec(id: BuiltinId): BuiltinSpec {
  return BUILTINS[id];
}

/** The actual arguments passed by JavaScript, independently of which ones a
 * callback declares or observes. Array indices are JS numbers (modeled ints). */
export function callbackArgumentTypes(spec: BuiltinSpec, receiver: Ty, initial?: Ty): Ty[] | undefined {
  if (!spec.hof || receiver.kind !== "array") return undefined;
  switch (spec.hof.shape) {
    case "element": return [receiver.elem, { kind: "int" }, receiver];
    case "comparator": return [receiver.elem, receiver.elem];
    case "reduce": return initial ? [initial, receiver.elem, { kind: "int" }, receiver] : undefined;
  }
}

export function callbackBaseArity(shape: NonNullable<BuiltinSpec["hof"]>["shape"]): number {
  return shape === "element" ? 1 : 2;
}
