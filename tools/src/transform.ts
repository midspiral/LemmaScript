/**
 * Transform — Typed IR → Backend IR.
 *
 * Consumes resolved types and classifications.
 * No type lookups, no string parsing, no re-inference.
 */

import type { TExpr, TStmt, TModule, Ty } from "./typedir.js";
import { isBigInt, tyEqual } from "./typedir.js";
import type { Expr, Stmt, Decl, Module, FnDef, FnDefByMethod, FnMethod, MatchArm, ConstDecl, MatchPattern } from "./ir.js";
import { anyExpr, anyExprInStmts, pWild, pCtor, pLiteral, patternBinders, patternBinds, patternCtor } from "./ir.js";
import type { TypeDeclInfo, VariantInfo } from "./types.js";
import { parseTsType } from "./types.js";
import { freshName } from "./names.js";
import { builtinSpec } from "./builtins.js";
import { lowerIndexedCallback } from "./callback-lowering.js";
import { isFalsyCapableTy, applyChain } from "./condition-facts.js";
import { UNDEFINED, NULL } from "./nullish.js";
import { declOf, declOfKind, declOfTy, unionDeclOfTy, declWithVariant, tyBaseName } from "./typedecls.js";

// ── Generic IR walkers ──────────────────────────────────────

/**
 * Map over all sub-expressions in an Expr. `f` is called on each node;
 * if it returns non-null, that replaces the node (and recursion stops).
 * If it returns null, the walker recurses into children.
 */
function mapExpr(e: Expr, f: (e: Expr) => Expr | null): Expr {
  const hit = f(e);
  if (hit) return hit;
  const r = (x: Expr) => mapExpr(x, f);
  switch (e.kind) {
    case "var": case "num": case "bigint": case "bool": case "str": case "emptyMap": case "emptySet": case "havoc": case "default": return e;
    case "mapLiteral": return { ...e, entries: e.entries.map(en => ({ key: r(en.key), value: r(en.value) })) };
    case "constructor": return e.args ? { ...e, args: e.args.map(r) } : e;
    case "binop": return { ...e, left: r(e.left), right: r(e.right) };
    case "unop": return { ...e, expr: r(e.expr) };
    case "implies": return { ...e, premises: e.premises.map(r), conclusion: r(e.conclusion) };
    case "app": return { ...e, args: e.args.map(r) };
    case "field": return { ...e, obj: r(e.obj) };
    case "toNat": return { ...e, expr: r(e.expr) };
    case "toInt": return { ...e, expr: r(e.expr) };
    case "toReal": return { ...e, expr: r(e.expr) };
    case "nullishTest": return { ...e, expr: r(e.expr) };
    case "nullishCoerce": return { ...e, expr: r(e.expr) };
    case "index": return { ...e, arr: r(e.arr), idx: r(e.idx) };
    case "stringIndex": return { ...e, str: r(e.str), idx: r(e.idx) };
    case "tupleLiteral": return { ...e, elems: e.elems.map(r) };
    case "tupleProj": return { ...e, obj: r(e.obj) };
    case "record": return { ...e, spread: e.spread ? r(e.spread) : null, fields: e.fields.map(fi => ({ ...fi, value: r(fi.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(r) };
    case "arrayRange": return { ...e, length: r(e.length) };
    case "if": return { ...e, cond: r(e.cond), then: r(e.then), else: r(e.else) };
    case "match": {
      const scr = r(e.scrutinee);
      return { ...e, scrutinee: scr, arms: e.arms.map(a => ({ ...a, body: r(a.body) })) };
    }
    case "forall": return { ...e, body: r(e.body) };
    case "exists": return { ...e, body: r(e.body) };
    case "let": return { ...e, value: r(e.value), body: r(e.body) };
    case "methodCall": return { ...e, obj: r(e.obj), args: e.args.map(r) };
    case "lambda": return e;
  }
}

/** Map over all expressions in a statement tree. */
function mapStmt(s: Stmt, f: (e: Expr) => Expr | null): Stmt {
  const r = (e: Expr) => mapExpr(e, f);
  switch (s.kind) {
    case "let": return { ...s, value: r(s.value) };
    case "assign": return { ...s, value: r(s.value) };
    case "bind": return { ...s, value: r(s.value) };
    case "let-bind": return { ...s, value: r(s.value) };
    case "return": return { ...s, value: r(s.value) };
    case "break": case "continue": return s;
    case "if": return { ...s, cond: r(s.cond), then: s.then.map(t => mapStmt(t, f)), else: s.else.map(t => mapStmt(t, f)) };
    case "match": {
      const scr = r(s.scrutinee);
      return { ...s, scrutinee: scr, arms: s.arms.map(a => ({ ...a, body: a.body.map(t => mapStmt(t, f)) })) };
    }
    case "while": return { ...s, cond: r(s.cond), invariants: s.invariants.map(r), body: s.body.map(t => mapStmt(t, f)) };
    case "forin": return { ...s, bound: r(s.bound), invariants: s.invariants.map(r), body: s.body.map(t => mapStmt(t, f)) };
    case "ghostLet": return { ...s, value: r(s.value) };
    case "ghostAssign": return { ...s, value: r(s.value) };
    case "assert": return { ...s, expr: r(s.expr) };
  }
}

/** Rename free occurrences of `from` to `to`, stopping at every construct that
 *  rebinds `from` — lambda params, `let`/`let-bind`/`ghostLet` (shadows the
 *  rest of the block), `match` arm patterns, `forall`/`exists`, and `for-in`
 *  indices. Capture-avoiding: a nested scope that reintroduces `from` keeps its
 *  own binding untouched. `mapExpr` doesn't descend into lambda bodies, so this
 *  walks them by hand — statement binders are tracked only at that body's top
 *  level, which is enough for the sole caller (dafny-emit's
 *  `comprehensionBinder`). TODO: generalize if more callers need this. */
const varE = (name: string): Expr => ({ kind: "var", name });
export function renameFreeVar(e: Expr, from: string, to: string): Expr {
  const f = (x: Expr): Expr | null => {
    if (x.kind === "var") return x.name === from ? { ...x, name: to } : x;
    // let-expression: `value` is in the outer scope (rename), `body` sees the
    // rebound `from` (leave it), so handle the recursion here to stop descent.
    if (x.kind === "let" && x.name === from) return { ...x, value: mapExpr(x.value, f) };
    if ((x.kind === "forall" || x.kind === "exists") && x.var === from) return x;
    if (x.kind === "match") {
      return { ...x, scrutinee: mapExpr(x.scrutinee, f), arms: x.arms.map(a =>
        patternBinds(a.pattern, from) ? a : { ...a, body: mapExpr(a.body, f) }) };
    }
    if (x.kind === "lambda") {
      if (x.params.some(p => p.name === from)) return x;   // param shadows `from`
      const body: Stmt[] = [];
      let shadowed = false;
      for (const s of x.body) {
        if (shadowed) { body.push(s); continue; }
        body.push(s.kind === "forin" && s.idx === from
          ? { ...s, bound: mapExpr(s.bound, f) }            // idx shadows in the loop body
          : mapStmt(s, f));
        if ((s.kind === "let" || s.kind === "let-bind" || s.kind === "ghostLet") && s.name === from) shadowed = true;
      }
      return { ...x, body };
    }
    return null;
  };
  return mapExpr(e, f);
}



/** Map over all sub-expressions in a TExpr (typed IR). */
function mapTExpr(e: TExpr, f: (e: TExpr) => TExpr | null): TExpr {
  const hit = f(e);
  if (hit) return hit;
  const r = (x: TExpr) => mapTExpr(x, f);
  switch (e.kind) {
    case "var": case "num": case "bigint": case "str": case "bool": case "havoc": return e;
    case "binop": return { ...e, left: r(e.left), right: r(e.right) };
    case "unop": case "coerce": return { ...e, expr: r(e.expr) };
    case "call": return { ...e, fn: r(e.fn), args: e.args.map(r) };
    case "index": return { ...e, obj: r(e.obj), idx: r(e.idx) };
    case "field": return { ...e, obj: r(e.obj) };
    case "record": return { ...e, spread: e.spread ? r(e.spread) : null, fields: e.fields.map(fi => ({ ...fi, value: r(fi.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(r) };
    case "conditional": return { ...e, cond: r(e.cond), then: r(e.then), else: r(e.else) };
    case "optChain": return { ...e, obj: r(e.obj),
      chain: e.chain.map(s => s.kind === "call" ? { ...s, args: s.args.map(r) }
        : s.kind === "index" ? { ...s, idx: r(s.idx) }
        : s) };
    case "nullish": return { ...e, left: r(e.left), right: r(e.right) };
    case "tagMatch": return { ...e, scrutinee: r(e.scrutinee),
      cases: e.cases.map(c => ({ ...c, body: r(c.body) })),
      fallthrough: e.fallthrough ? r(e.fallthrough) : null };
    case "forall": return { ...e, body: r(e.body) };
    case "exists": return { ...e, body: r(e.body) };
    case "lambda": return e;
  }
}

/** Map over all expressions in a TStmt tree (typed IR). */
function mapTStmt(s: TStmt, f: (e: TExpr) => TExpr | null): TStmt {
  const r = (e: TExpr) => mapTExpr(e, f);
  switch (s.kind) {
    case "let": return { ...s, init: r(s.init) };
    case "assign": return { ...s, value: r(s.value) };
    case "return": return { ...s, value: r(s.value) };
    case "break": case "continue": case "throw": return s;
    case "expr": return { ...s, expr: r(s.expr) };
    case "if": return { ...s, cond: r(s.cond), then: s.then.map(t => mapTStmt(t, f)), else: s.else.map(t => mapTStmt(t, f)) };
    case "while": return { ...s, cond: r(s.cond), invariants: s.invariants.map(r), body: s.body.map(t => mapTStmt(t, f)) };
    case "switch": return { ...s, expr: r(s.expr), cases: s.cases.map(c => ({ ...c, body: c.body.map(t => mapTStmt(t, f)) })), defaultBody: s.defaultBody.map(t => mapTStmt(t, f)) };
    case "forof": return { ...s, iterable: r(s.iterable), invariants: s.invariants.map(r), body: s.body.map(t => mapTStmt(t, f)) };
    case "ghostLet": return { ...s, init: r(s.init) };
    case "ghostAssign": return { ...s, value: r(s.value) };
    case "assert": return { ...s, expr: r(s.expr) };
    case "tagMatch": return { ...s, scrutinee: r(s.scrutinee),
      cases: s.cases.map(c => ({ ...c, body: c.body.map(t => mapTStmt(t, f)) })),
      fallthrough: s.fallthrough.map(t => mapTStmt(t, f)) };
  }
}

// ── Backend configuration ───────────────────────────────────

export type Backend = "lean" | "dafny";

export interface TransformOptions {
  backend: Backend;
  monadic: boolean;
}

export const LEAN_OPTIONS: TransformOptions = {
  backend: "lean",
  monadic: true,
};

export const DAFNY_OPTIONS: TransformOptions = {
  backend: "dafny",
  monadic: false,
};

/** Active options — set before each transform call. */
let _opts: TransformOptions = DAFNY_OPTIONS;

/** Type declarations — set once per module transform for discriminated union handling. */
let _typeDecls: TypeDeclInfo[] = [];

/** Names of functions that get a `Pure.` mirror (Lean). A bare reference to one
 *  in a higher-order position resolves to the monadic method, so it must be
 *  redirected to the pure mirror. Set once per module transform. */
let _pureDefNames: Set<string> = new Set();

/** Discriminated unions whose tag is read as a *value* (`x.kind` compared
 *  to another union's tag, passed as an argument, …). Each gets a generated
 *  `<Union>_<disc>` discriminator function beside its datatype, returning
 *  the source tag strings. Narrowing consumes discriminant *checks*, so this
 *  fires only for surviving reads. Populated during body transforms; drained
 *  into the types file. */
let _neededKindHelpers = new Map<string, TypeDeclInfo>();

function kindHelperName(decl: TypeDeclInfo): string {
  return freshName(`${decl.name}_${decl.discriminant}`);
}

function kindHelperDecl(decl: TypeDeclInfo): Decl {
  return {
    kind: "def",
    name: kindHelperName(decl),
    typeParams: [],
    params: [{ name: "t", type: { kind: "user", name: decl.name } }],
    returnType: { kind: "string" },
    requires: [], ensures: [], decreases: null,
    body: {
      kind: "match", scrutinee: varE("t"),
      arms: decl.variants!.map(v => ({
        pattern: { kind: "ctor" as const, ctor: v.name, binders: v.fields.map((_, i) => `_${i}`) },
        body: { kind: "str" as const, value: v.name },
      })),
    },
  };
}

/** Prefix match-bound field names to avoid capturing user variables.
 *  When prefix is given (the scrutinee name), include it to avoid
 *  collisions in nested matches on different variables. `freshName` closes
 *  the residual gap: a user variable literally named `_value`/`_x_field` in an
 *  arm body would still be captured, so prime on any module-wide collision.
 *  Deterministic, so the pattern binder and its body substitutions agree. */
function matchBinder(fieldName: string, prefix?: string): string {
  const safePrefix = prefix === "\\result"
    ? "result"
    : prefix?.replace(/[^A-Za-z0-9_]/g, "_");
  return freshName(safePrefix ? `_${safePrefix}_${fieldName}` : `_${fieldName}`);
}

/** Build a match arm pattern like `.VariantName _v_field1 _v_field2` from variant info. */
function buildMatchPattern(variantName: string, fields: { name: string }[], scopePrefix?: string): MatchPattern {
  return pCtor(variantName, ...fields.map(f => matchBinder(f.name, scopePrefix)));
}

const _forofCounters = new Map<string, number>();
function isNat(ty: Ty): boolean { return ty.kind === "nat"; }
function isIntegral(ty: Ty): boolean { return ty.kind === "int" || ty.kind === "nat"; }
function isArray(ty: Ty): boolean { return ty.kind === "array"; }
function isRecordType(ty: Ty): boolean {
  return declOfTy(_typeDecls, ty)?.kind === "record";
}

/** Truthiness test for a *lowered* value of source type `ty`, used by `||`
 *  falsiness lowering. Which types need one is `isFalsyCapableTy` (shared with
 *  condition-facts' falsy gate); this adds the per-type test. Returns null for
 *  the always-truthy types so callers can unwrap directly instead of emitting
 *  a redundant guard. */
function valueTruthyCond(value: Expr, ty: Ty): Expr | null {
  if (!isFalsyCapableTy(ty)) return null;
  switch (ty.kind) {
    case "int": case "nat":
      return { kind: "binop", op: "≠", left: value, right: { kind: "num", value: 0 } };
    case "string":
      return { kind: "binop", op: ">", left: { kind: "field", obj: value, field: "length" }, right: { kind: "num", value: 0 } };
    case "bool":
      return value;
    default:
      return null;
  }
}

/** Check if transformed lambda body contains monadic binds. */
function isMonadicBody(stmts: Stmt[]): boolean {
  for (const s of stmts) {
    if (s.kind === "let-bind" || s.kind === "bind") return true;
    if (s.kind === "if" && (isMonadicBody(s.then) || isMonadicBody(s.else))) return true;
    if (s.kind === "while" && isMonadicBody(s.body)) return true;
    if (s.kind === "forin" && isMonadicBody(s.body)) return true;
    if (s.kind === "match") {
      for (const arm of s.arms) if (isMonadicBody(arm.body)) return true;
    }
  }
  return false;
}


// ── Transform expressions ────────────────────────────────────

/** Prop-valued operators (for specs/invariants). */
const OP_MAP: Record<string, string> = {
  "===": "=", "!==": "≠", ">=": "≥", "<=": "≤", ">": ">", "<": "<",
  "&&": "∧", "||": "∨", "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
  "==": "=", "!=": "≠", "<==>": "↔",
};

/** Arithmetic + comparison ops eligible for int→real operand coercion. */
const NUMERIC_OPS = new Set(["+", "-", "*", "/", "===", "!==", ">=", "<=", ">", "<"]);

function transformExpr(e: TExpr): Expr { return lowerExpr(e, null); }

/** Reduce an if/let/return-shaped statement body to a single expression, for
 *  expression-only lambda bodies. Returns null for shapes that can't be a pure
 *  expression (loops, assignments, bare side effects), so callers leave the
 *  body as statements. A `return` is terminal — statements after it are
 *  unreachable and dropped.
 *    [return e]                          → e
 *    [let x = e, …rest]                  → Expr.let(x, e, flatten(rest))
 *    [if (c) thenStmts elseStmts, …rest] → Expr.if(c, …) where each branch
 *        absorbs `rest` if it doesn't already terminate with a return. */
function flattenLambdaBody(stmts: Stmt[]): Expr | null {
  if (stmts.length === 0) return null;
  const first = stmts[0]!;
  const rest = stmts.slice(1);
  if (first.kind === "return") return first.value;
  if (first.kind === "let" && !first.mutable) {
    const body = flattenLambdaBody(rest);
    return body === null ? null : { kind: "let", name: first.name, value: first.value, body };
  }
  if (first.kind === "if") {
    const thenTerminates = flattenLambdaBody(first.then);
    if (thenTerminates !== null) {
      // then-branch yields a value (ends in return) → `rest` is the else path.
      const elseExpr = flattenLambdaBody(first.else.length > 0 ? [...first.else, ...rest] : rest);
      return elseExpr === null ? null : { kind: "if", cond: first.cond, then: thenTerminates, else: elseExpr };
    }
    // then-branch falls through → both branches continue into `rest`.
    const thenExpr = flattenLambdaBody([...first.then, ...rest]);
    const elseExpr = flattenLambdaBody(first.else.length > 0 ? [...first.else, ...rest] : rest);
    return thenExpr === null || elseExpr === null ? null : { kind: "if", cond: first.cond, then: thenExpr, else: elseExpr };
  }
  // A `switch` lowered to a match-statement: reduce each arm's body to an
  // expression (an arm that doesn't return falls through into `rest`), giving a
  // match-expression — same reduction the `if` case does, one level wider.
  if (first.kind === "match") {
    const arms: MatchArm[] = [];
    for (const arm of first.arms) {
      const armExpr = flattenLambdaBody([...arm.body, ...rest]);
      if (armExpr === null) return null;
      arms.push({ pattern: arm.pattern, body: armExpr });
    }
    return { kind: "match", scrutinee: first.scrutinee, arms };
  }
  return null;
}

/**
 * Lower a typed expression to Backend IR.
 *
 * When `binds` is non-null, embedded method calls are extracted into
 * `let ← ` binds (monadic lifting / selective ANF).  Lifting propagates
 * through binop, unop, and call arguments — the expression kinds where
 * a method call can appear inline in TS.  It does NOT propagate into
 * field, index, record, forall, or exists sub-expressions.
 */

/** JS truthiness coercion for `if`/`while`/`?:` conditions.
 *  Dafny requires bool; coerce number→`!== 0`, string→non-empty, array→`true`
 *  (every array, even `[]`, is truthy in JS).
 *
 *  Rewrites the typed tree, before lowering, and distributes over `&&`/`||`:
 *  each operand of a logical connective is itself in condition position, and the
 *  operands need not share a type — `i >= 0 && carry`, with `carry` an int, is a
 *  bool conjoined with a number. A conjunction takes its type from its right
 *  operand (resolve), so coercing the whole expression by its type would emit
 *  `((i >= 0) && carry) != 0`, which is not well-typed.
 *
 *  Optional conds never arrive here — narrow.ts rewrites them to someMatch. */
function asCondition(e: TExpr): TExpr {
  const bool: Ty = { kind: "bool" };
  if (e.ty.kind === "bool") return e;
  if (e.ty.kind === "nullish") return { kind: "bool", value: false, ty: bool };
  if (e.kind === "binop" && (e.op === "&&" || e.op === "||"))
    return { ...e, left: asCondition(e.left), right: asCondition(e.right), ty: bool };
  if (e.ty.kind === "int" || e.ty.kind === "nat" || e.ty.kind === "real")
    return { kind: "binop", op: "!==", left: e, right: { kind: "num", value: 0, ty: e.ty }, ty: bool };
  if (e.ty.kind === "string")
    return { kind: "binop", op: ">",
      left: { kind: "field", obj: e, field: "length", ty: { kind: "nat" } },
      right: { kind: "num", value: 0, ty: { kind: "nat" } }, ty: bool };
  if (e.ty.kind === "optional") {
    const present: TExpr = {
      kind: "binop", op: "!=", left: e,
      right: { kind: "var", name: "null", ty: NULL },
      ty: bool,
    };
    if (!isFalsyCapableTy(e.ty.inner)) return present;
    const inner: TExpr = { kind: "coerce", expr: e, ty: e.ty.inner };
    return { kind: "binop", op: "&&", left: present, right: asCondition(inner), ty: bool };
  }
  // Arrays, objects, maps, sets, tuples are always truthy in JS (even `[]`/`{}`).
  if (["array", "user", "map", "set", "tuple"].includes(e.ty.kind))
    return { kind: "bool", value: true, ty: bool };
  return e;
}

/** Wrap a value into an optional/nullish container (total upcast). */
function wrapForOptional(expr: Expr, fromTy: Ty, targetTy: Ty & { kind: "optional" }): Expr {
  if (fromTy.kind === "nullish") {
    if (targetTy.nullish === "both") {
      return { kind: "constructor", name: fromTy.nullish === "null" ? "Null" : "Undefined", type: "LemmaScript.Nullish", args: [] };
    }
    return { kind: "constructor", name: "none", type: "Option", args: [] };
  }
  if (fromTy.kind === "optional") {
    if (fromTy.nullish === targetTy.nullish) return expr;
    if (targetTy.nullish === "both") {
      return { kind: "nullishCoerce", expr, op: fromTy.nullish === "null" ? "optNullToNullish" : "optUndefToNullish" };
    }
    return expr;
  }
  if (targetTy.nullish === "both") {
    return { kind: "constructor", name: "Value", type: "LemmaScript.Nullish", args: [expr] };
  }
  return { kind: "constructor", name: "some", type: "Option", args: [expr] };
}

/** Lower a representation coercion (`fromTy` → `toTy`). */
function lowerCoerce(expr: Expr, fromTy: Ty, toTy: Ty, binds: Stmt[] | null): Expr {
  if (tyEqual(fromTy, toTy)) return expr;
  if (toTy.kind === "optional") {
    if (fromTy.kind === "optional" && fromTy.nullish === "both" && toTy.nullish !== "both") {
      const op = toTy.nullish === "null" ? "nullishExcludeUndefined" : "nullishExcludeNull";
      if (_opts.backend === "lean" && binds !== null) {
        const name = freshName(`_v${_liftCounter++}`);
        binds.push({ kind: "let-bind", name, value: { kind: "app", fn: `LemmaScript.${op}`, args: [expr] } });
        return { kind: "var", name };
      }
      return { kind: "nullishCoerce", expr, op };
    }
    return wrapForOptional(expr, fromTy, toTy);
  }
  if (fromTy.kind === "optional") {
    const isNullish = fromTy.nullish === "both";
    if (_opts.backend === "lean" && binds !== null) {
      const name = freshName(`_v${_liftCounter++}`);
      const fn = isNullish ? "LemmaScript.nullishValue" : "LemmaScript.optionValue";
      binds.push({ kind: "let-bind", name, value: { kind: "app", fn, args: [expr] } });
      return { kind: "var", name };
    }
    return { kind: "nullishCoerce", expr, op: isNullish ? "nullishGet" : "optionGet" };
  }
  return expr;
}

/** Legacy helper kept for tagMatch optional branches. */
function wrapOptionalBranch(expr: Expr, raw: TExpr, targetTy?: Ty): Expr {
  if (targetTy?.kind === "optional") return wrapForOptional(expr, raw.ty, targetTy);
  if (raw.kind === "var" && (raw.name === "undefined" || raw.name === "null")) {
    return { kind: "constructor", name: "none", type: "Option", args: [] };
  }
  if (raw.ty.kind === "optional") return expr;
  return { kind: "constructor", name: "some", type: "Option", args: [expr] };
}

/** Lean needs `let mut` for any local that is later reassigned. A const local
 *  whose collection field is mutated (`b.items.push(v)` → `b := b.(items := …)`)
 *  becomes an assign in the lowered body, so scan for assign targets and flip
 *  matching lets to mutable. Harmless on Dafny (method locals are `var`); and an
 *  assigned let already forces a method, so purity is unaffected. */
function promoteAssignedLets(stmts: Stmt[]): Stmt[] {
  const assigned = new Set<string>();
  const collect = (ss: Stmt[]) => {
    for (const s of ss) {
      if (s.kind === "assign") assigned.add(s.target);
      else if (s.kind === "if") { collect(s.then); collect(s.else); }
      else if (s.kind === "while" || s.kind === "forin") collect(s.body);
      else if (s.kind === "match") s.arms.forEach(a => collect(a.body));
    }
  };
  collect(stmts);
  if (assigned.size === 0) return stmts;
  const fix = (ss: Stmt[]): Stmt[] => ss.map(s => {
    const s2: Stmt = s.kind === "let" && !s.mutable && assigned.has(s.name) ? { ...s, mutable: true } : s;
    if (s2.kind === "if") return { ...s2, then: fix(s2.then), else: fix(s2.else) };
    if (s2.kind === "while" || s2.kind === "forin") return { ...s2, body: fix(s2.body) };
    if (s2.kind === "match") return { ...s2, arms: s2.arms.map(a => ({ ...a, body: fix(a.body) })) };
    return s2;
  });
  return fix(stmts);
}

/** Build a nested record-update assigning `newVal` to a field-path receiver
 *  rooted at a var: `b.a.items` → `b := b.(a := b.a.(items := newVal))`.
 *  Returns null if the path isn't a chain of field accesses ending at a var. */
/** Build a storage-preserving update back to the root variable through any
 *  combination of record fields and optional/nullish coercions:
 *    - `a.push(99)` (a: Option<T[]>) → `a := Some(a.value + [99])`
 *    - `b.items.push(99)` (b: Option<Bag>) → `b := Some(b.value.(items := ...))` */
function buildNestedUpdate(recv: TExpr, newVal: Expr, binds: Stmt[] | null): { root: string; value: Expr } | null {
  if (recv.kind === "var") return { root: recv.name, value: newVal };
  if (recv.kind === "coerce" && recv.expr.ty.kind === "optional") {
    const wrapped = wrapForOptional(newVal, recv.ty, recv.expr.ty);
    return buildNestedUpdate(recv.expr, wrapped, binds);
  }
  if (recv.kind === "field") {
    const upd: Expr = { kind: "record", spread: lowerExpr(recv.obj, binds), fields: [{ name: recv.field, value: newVal }] };
    return buildNestedUpdate(recv.obj, upd, binds);
  }
  return null;
}

/** Root variable name of a mutable receiver chain (through `field` and `coerce`). */
function mutableReceiverRoot(e: TExpr): string | null {
  if (e.kind === "var") return e.name;
  if (e.kind === "coerce") return mutableReceiverRoot(e.expr);
  if (e.kind === "field") return mutableReceiverRoot(e.obj);
  return null;
}

/** Promote every spread segment before concatenation, preserving evaluation
 *  order. A seq<int> needs elementwise conversion; it cannot be cast to real. */
function lowerMinMaxSequence(e: TExpr, real: boolean, binds: Stmt[] | null): Expr {
  if (e.kind === "binop" && e.op === "arrayConcat") {
    return { kind: "binop", op: "arrayConcat",
      left: lowerMinMaxSequence(e.left, real, binds),
      right: lowerMinMaxSequence(e.right, real, binds) };
  }
  if (e.kind === "arrayLiteral") {
    return { kind: "arrayLiteral", elems: e.elems.map(el => {
      const value = lowerExpr(el, binds);
      if (real && isIntegral(el.ty)) return { kind: "toReal", expr: value };
      return _opts.backend === "lean" && isNat(el.ty) ? { kind: "toInt", expr: value } : value;
    }) };
  }
  const value = lowerExpr(e, binds);
  if (_opts.backend === "lean" && e.ty.kind === "array" && isNat(e.ty.elem)) {
    return { kind: "app", fn: "Array.map", args: [{ kind: "var", name: "Int.ofNat" }, value] };
  }
  return real && e.ty.kind === "array" && isIntegral(e.ty.elem)
    ? { kind: "app", fn: "SeqIntToReal", args: [value] } : value;
}

function lowerExpr(e: TExpr, binds: Stmt[] | null): Expr {
  // Lean spreads are checked Option operations. Lift even a syntactically pure
  // call so total correctness requires the combined array to be nonempty.
  if (_opts.backend === "lean" && e.kind === "call" && e.fn.kind === "var" &&
      (e.fn.name === "MaxOfSeq" || e.fn.name === "MinOfSeq") && e.args.length === 1) {
    const name = binds ? freshName(`_t${_liftCounter++}`) : null;
    const value: Expr = { kind: "app",
      fn: e.fn.name === "MaxOfSeq" ? "LemmaScript.maxOfArray" : "LemmaScript.minOfArray",
      args: [lowerMinMaxSequence(e.args[0], e.ty.kind === "real", binds)] };
    if (binds && name) {
      binds.push({ kind: "let-bind", name, value });
      return { kind: "var", name };
    }
    return value;
  }
  // Monadic lifting: extract embedded method calls to let-binds.
  // `callKind: "method"` means a global var-fn call (classifyCall returns
  // "method" only for `fn.kind === "var"`). Receiver method calls have
  // callKind "unknown" and fall through to the regular case below where
  // they become `methodCall`.
  if (binds && e.kind === "call" && e.callKind === "method" && e.fn.kind === "var") {
    const name = freshName(`_t${_liftCounter++}`);
    const args = e.args.map(a => lowerExpr(a, binds));
    binds.push({ kind: "let-bind", name, value: { kind: "app", fn: e.fn.name, args } });
    return { kind: "var", name };
  }

  switch (e.kind) {
    case "var": return { kind: "var", name: e.name };
    case "num": {
      const literal: Expr = { kind: "num", value: e.value };
      return e.ty.kind === "real" && Number.isInteger(e.value)
        ? { kind: "toReal", expr: literal } : literal;
    }
    case "bigint": return { kind: "bigint", value: e.value };
    case "bool": return { kind: "bool", value: e.value };

    case "str":
      if (e.ty.kind === "user") return { kind: "constructor", name: e.value, type: e.ty.name, args: [] };
      return { kind: "str", value: e.value };

    case "coerce": {
      const inner = lowerExpr(e.expr, binds);
      return lowerCoerce(inner, e.expr.ty, e.ty, binds);
    }

    case "unop":
      // Only `num` folds. A `bigint` payload is a string, so negating it here
      // would coerce through `Number` and round: `-9007199254740993n` stays a
      // structural `unop("-", bigint(...))` and is negated by the emitter.
      if (e.op === "-" && e.expr.kind === "num")
        return lowerExpr({ ...e.expr, value: -e.expr.value, ty: e.ty }, binds);
      // String truthiness: !str → str == ""
      if (e.op === "!" && e.expr.ty.kind === "string")
        return { kind: "binop", op: "=", left: lowerExpr(e.expr, binds), right: { kind: "str", value: "" } };
      // Optional / nullish truthiness: `!e` → `¬asCondition(e)`
      if (e.op === "!" && (e.expr.ty.kind === "optional" || e.expr.ty.kind === "nullish")) {
        if (e.expr.ty.kind === "nullish") {
          lowerExpr(e.expr, binds);
          return { kind: "bool", value: true };
        }
        return { kind: "unop", op: "¬", expr: lowerExpr(asCondition(e.expr), binds) };
      }
      // Number truthiness: !n → n == 0
      if (e.op === "!" && (e.expr.ty.kind === "int" || e.expr.ty.kind === "nat" || e.expr.ty.kind === "real"))
        return { kind: "binop", op: "=", left: lowerExpr(e.expr, binds), right: { kind: "num", value: 0 } };
      // Object truthiness: arrays, objects, maps, and sets are always truthy in JS.
      if (e.op === "!" && ["array", "user", "map", "set", "tuple"].includes(e.expr.ty.kind)) {
        lowerExpr(e.expr, binds);
        return { kind: "bool", value: false };
      }
      return { kind: "unop", op: e.op === "!" ? "¬" : e.op, expr: lowerExpr(e.expr, binds) };

    case "binop": {
      // Implication: flatten (A && B) ==> C → implies [A, B] C
      if (e.op === "==>") {
        const { premises, conclusion } = flattenImpl(e);
        return { kind: "implies", premises: premises.map(p => transformExpr(asCondition(p))), conclusion: transformExpr(conclusion) };
      }
      // Boolean connectives evaluate the RHS only if the left operand selects
      // it. Keep lifted calls in that branch instead of hoisting them eagerly.
      if ((e.op === "&&" || e.op === "||") && e.left.ty.kind === "bool" && e.right.ty.kind === "bool") {
        const left = lowerExpr(e.left, binds);
        const rightBinds: Stmt[] | null = binds ? [] : null;
        const right = lowerExpr(e.right, rightBinds);
        if (binds && rightBinds?.length) {
          const name = freshName(`_branch${_branchCounter++}`);
          const value: Expr = { kind: "var", name };
          binds.push({ kind: "let", name, type: { kind: "bool" }, mutable: true, value: left });
          binds.push({ kind: "if", cond: e.op === "&&" ? value : { kind: "unop", op: "¬", expr: value },
            then: [...rightBinds, { kind: "assign", target: name, value: right }], else: [] });
          return value;
        }
        return { kind: "binop", op: OP_MAP[e.op], left, right };
      }
      // Null / undefined sentinel equality checks (`===`, `!==`, `==`, `!=`):
      if ((e.op === "===" || e.op === "!==" || e.op === "==" || e.op === "!=") &&
          (e.left.ty.kind === "nullish" || e.right.ty.kind === "nullish")) {
        const neg = e.op === "!==" || e.op === "!=";
        const loose = e.op === "==" || e.op === "!=";
        if (e.left.ty.kind === "nullish" && e.right.ty.kind === "nullish") {
          const eq = loose ? true : e.left.ty.nullish === e.right.ty.nullish;
          return { kind: "bool", value: neg ? !eq : eq };
        }
        const [sentinelSide, rawExprSide] = e.left.ty.kind === "nullish" ? [e.left, e.right] : [e.right, e.left];
        // When testing `x === null` after `x !== undefined` already narrowed `Nullish<T>` to `Option<T>`,
        // test the underlying storage `x` directly (`x.Null?` / `x.isNull`) instead of coercing first!
        const exprSide = rawExprSide.kind === "coerce" && rawExprSide.expr.ty.kind === "optional"
          ? rawExprSide.expr
          : rawExprSide;
        const sentinel = (sentinelSide.ty as { kind: "nullish"; nullish: "null" | "undefined" | "both" }).nullish;
        const tested = loose ? "both" : sentinel;
        const expr = lowerExpr(exprSide, binds);
        if (exprSide.ty.kind !== "optional") {
          return { kind: "bool", value: neg };
        }
        if (exprSide.ty.nullish !== "both") {
          if (tested === "both" || tested === exprSide.ty.nullish) {
            const isSome: Expr = { kind: "nullishTest", expr, test: "isSome" };
            return neg ? isSome : { kind: "unop", op: "¬", expr: isSome };
          }
          return { kind: "bool", value: neg };
        }
        // Three-case Nullish<T>
        if (tested === "undefined") {
          const t: Expr = { kind: "nullishTest", expr, test: "isUndefined" };
          return neg ? { kind: "unop", op: "¬", expr: t } : t;
        }
        if (tested === "null") {
          const t: Expr = { kind: "nullishTest", expr, test: "isNull" };
          return neg ? { kind: "unop", op: "¬", expr: t } : t;
        }
        const isVal: Expr = { kind: "nullishTest", expr, test: "isValue" };
        return neg ? isVal : { kind: "unop", op: "¬", expr: isVal };
      }
      // Discriminant check: x.discriminant === "foo" → x = .foo
      if ((e.op === "===" || e.op === "!==" || e.op === "==" || e.op === "!=") &&
          e.left.kind === "field" && e.left.isDiscriminant && e.right.kind === "str") {
        const objTy = e.left.obj.ty.kind === "user" ? e.left.obj.ty.name : undefined;
        return {
          kind: "binop",
          op: (e.op === "===" || e.op === "==") ? "=" : "≠",
          left: lowerExpr(e.left.obj, binds),
          right: { kind: "constructor", name: e.right.value, type: objTy, args: [] },
        };
      }
      // String literal comparison — constructor if user type, string literal if string.
      if ((e.op === "===" || e.op === "!==" || e.op === "==" || e.op === "!=") &&
          e.right.kind === "str" && e.left.ty.kind !== "optional") {
        const left = lowerExpr(e.left, binds);
        const leftTy = e.left.ty.kind === "user" ? e.left.ty.name : undefined;
        const isStrUnion = leftTy !== undefined && declOfKind(_typeDecls, tyBaseName(leftTy), "string-union") !== undefined;
        const right: Expr = isStrUnion
          ? { kind: "constructor", name: e.right.value, type: leftTy, args: [] }
          : { kind: "str", value: e.right.value };
        return { kind: "binop", op: (e.op === "===" || e.op === "==") ? "=" : "≠", left, right };
      }
      // Dafny extensionality for `opt === val` / `opt !== val` when `val` is a
      // sequence/set/map (including `string`): `Option.Some(a) == Option.Some(b)`
      // hides the collection equality from Dafny's extensionality axioms, whereas
      // `opt.Some? && opt.value == val` exposes it directly. Both sides are lowered
      // in left-to-right source order so call obligations and side effects stay intact.
      if (_opts.backend === "dafny" && (e.op === "===" || e.op === "!==" || e.op === "==" || e.op === "!=") &&
          e.left.ty.kind === "optional" && e.right.ty.kind === "optional") {
        const isCollectionUpcast = (x: TExpr): x is Extract<TExpr, { kind: "coerce" }> =>
          x.kind === "coerce" && (x.expr.ty.kind === "string" || x.expr.ty.kind === "array" || x.expr.ty.kind === "set" || x.expr.ty.kind === "map");
        const leftUp = isCollectionUpcast(e.left) ? e.left : null;
        const rightUp = isCollectionUpcast(e.right) ? e.right : null;
        if (Boolean(leftUp) !== Boolean(rightUp)) {
          const leftL = leftUp ? lowerExpr(leftUp.expr, binds) : lowerExpr(e.left, binds);
          const rightL = rightUp ? lowerExpr(rightUp.expr, binds) : lowerExpr(e.right, binds);
          const optL = leftUp ? rightL : leftL;
          const valL = leftUp ? leftL : rightL;
          const optTy = leftUp ? e.right.ty : e.left.ty;
          const isNullish = optTy.kind === "optional" && optTy.nullish === "both";
          const test: "isValue" | "isSome" = isNullish ? "isValue" : "isSome";
          const getOp: "nullishGet" | "optionGet" = isNullish ? "nullishGet" : "optionGet";
          const simpleOpt = optL.kind === "var" || optL.kind === "field" || optL.kind === "app";
          const ref: Expr = simpleOpt ? optL : { kind: "var", name: freshName(`_eq${_liftCounter++}`) };
          const isEq = e.op === "===" || e.op === "==";
          const present: Expr = { kind: "nullishTest", expr: ref, test };
          const payload: Expr = { kind: "nullishCoerce", expr: ref, op: getOp };
          const cmp: Expr = { kind: "binop", op: isEq ? "=" : "≠", left: leftUp ? valL : payload, right: leftUp ? payload : valL };
          const body: Expr = isEq
            ? { kind: "binop", op: "∧", left: present, right: cmp }
            : { kind: "binop", op: "∨", left: { kind: "unop", op: "¬", expr: present }, right: cmp };
          return simpleOpt ? body : { kind: "let", name: (ref as { kind: "var"; name: string }).name, value: optL, body };
        }
      }
      // `||` on optional (JS falsiness fallback: `opt || default`):
      if (e.op === "||" && e.left.ty.kind === "optional") {
        const optExpr = lowerExpr(e.left, binds);
        const isNullish = e.left.ty.nullish === "both";
        const test: "isValue" | "isSome" = isNullish ? "isValue" : "isSome";
        const getOp: "nullishGet" | "optionGet" = isNullish ? "nullishGet" : "optionGet";
        const useVar = e.left.kind === "var" ? optExpr : { kind: "var" as const, name: freshName(`_or${_liftCounter++}`) };
        const presentTest: Expr = { kind: "nullishTest", expr: useVar, test };
        const unwrapped: Expr = { kind: "nullishCoerce", expr: useVar, op: getOp };
        const innerTruthy = valueTruthyCond(unwrapped, e.left.ty.inner);
        const cond: Expr = innerTruthy ? { kind: "binop", op: "∧", left: presentTest, right: innerTruthy } : presentTest;
        const thenVal = e.ty.kind === "optional" ? lowerCoerce(unwrapped, e.left.ty.inner, e.ty, null) : unwrapped;
        const elseVal = lowerExpr(e.right, binds);
        const ite: Expr = { kind: "if", cond, then: thenVal, else: elseVal };
        return e.left.kind === "var" ? ite : { kind: "let", name: (useVar as { kind: "var"; name: string }).name, value: optExpr, body: ite };
      }
      // || on map index → if key in map then map[key] else default. The stored
      // value is still subject to JS falsiness (`counts.get(k) || 1` returns 1 when
      // the stored value is 0), so for falsy-capable value types the present branch
      // re-tests the value too. Always-truthy value types unwrap directly.
      if (e.op === "||" && e.left.kind === "index" && e.left.obj.ty.kind === "map") {
        const map = lowerExpr(e.left.obj, binds);
        const key = lowerExpr(e.left.idx, binds);
        const right = lowerExpr(e.right, binds);
        const got: Expr = { kind: "index", arr: map, idx: key };
        const truthy = valueTruthyCond(got, e.left.obj.ty.value);
        return {
          kind: "if",
          cond: { kind: "binop", op: "in", left: key, right: map },
          then: truthy ? { kind: "if", cond: truthy, then: got, else: right } : got,
          else: right,
        };
      }
      // || on non-optional array → `xs` itself: every array (even `[]`) is truthy
      // in JS, so `xs || ys` short-circuits to `xs` and `ys` is never evaluated.
      // resolve types the whole `||` as the array, so any optional context (e.g.
      // `xs || undefined`) gets its single Some-wrap from the standard coercion at
      // the use site — this rule must not add one. Mirrors the `!array` rule above.
      if (e.op === "||" && e.left.ty.kind === "array") {
        return lowerExpr(e.left, binds);
      }
      // || on non-optional string/user → if non-empty then x else default
      if (e.op === "||" && (e.left.ty.kind === "string" ||
          (e.left.ty.kind === "user" && e.right.ty.kind === "string"))) {
        const left = lowerExpr(e.left, binds);
        const right = lowerExpr(e.right, binds);
        // `s || undefined` produces `Option<string>` — wrap the truthy branch in Some.
        const rightIsUndef = e.right.kind === "var" && e.right.name === "undefined";
        return {
          kind: "if",
          // strings carry the `length` marker — it renders to `|x|` in Dafny and
          // `.length` in Lean (whose String has no `.size` field).
          cond: { kind: "binop", op: ">", left: { kind: "field", obj: left, field: e.left.ty.kind === "string" ? "length" : "size" }, right: { kind: "num", value: 0 } },
          then: rightIsUndef ? { kind: "app", fn: "Some", args: [left] } : left,
          else: right,
        };
      }
      // `bool || undefined` → `if bool then Some(bool) else None`. Used in
      // optional-field initialization where the source assigns a truthy/false
      // bool to a `T?` field. Without this, emit produces `bool || None`,
      // which Dafny rejects (bool || Option<?> is ill-typed).
      if (e.op === "||" && e.left.ty.kind === "bool" &&
          e.right.kind === "var" && e.right.name === "undefined") {
        const left = lowerExpr(e.left, binds);
        return {
          kind: "if",
          cond: left,
          then: { kind: "app", fn: "Some", args: [left] },
          else: { kind: "var", name: "undefined" },
        };
      }
      // || on a number → `if x != 0 then x else default` (0 the only falsy int).
      if (e.op === "||" && (e.left.ty.kind === "int" || e.left.ty.kind === "nat")) {
        const left = lowerExpr(e.left, binds);
        const right = lowerExpr(e.right, binds);
        const truthy = valueTruthyCond(left, e.left.ty)!;
        return { kind: "if", cond: truthy, then: left, else: right };
      }
      // String concatenation: `+` with a string operand. Stringify int/nat
      // operands (Dafny NatToString, Lean toString) and join with arrayConcat
      // (rendered `+` in Dafny, `++` in Lean).
      if (e.op === "+" && (e.left.ty.kind === "string" || e.right.ty.kind === "string")) {
        const strify = (o: TExpr): Expr => {
          if (o.ty.kind !== "int" && o.ty.kind !== "nat") return lowerExpr(o, binds);
          // Lean `toString` handles any Int; Dafny needs IntToString for signed
          // ints (NatToString is nat-only).
          const fn = _opts.backend !== "dafny" ? "ToString" : o.ty.kind === "nat" ? "NatToString" : "IntToString";
          return { kind: "app", fn, args: [lowerExpr(o, binds)] };
        };
        return { kind: "binop", op: "arrayConcat", left: strify(e.left), right: strify(e.right) };
      }
      // JS `%` is truncated (sign of the dividend); a signed `int` differs from the
      // Euclidean `%` of Dafny/Lean, so route it through JSRem (Lean: `Int.tmod`).
      if (e.op === "%" && e.left.ty.kind === "int") {
        return { kind: "app", fn: "JSRem", args: [lowerExpr(e.left, binds), lowerExpr(e.right, binds)] };
      }
      // JS bigint `/` truncates toward zero (`-3n / 2n === -1n`); it differs from the
      // floored `/` of Dafny/Lean, so route it through JSTruncDiv (Lean: `Int.tdiv`).
      if (e.op === "/" && e.ty.kind === "int") {
        return { kind: "app", fn: "JSTruncDiv", args: [lowerExpr(e.left, binds), lowerExpr(e.right, binds)] };
      }
      // JS string ordering is lexicographic vs Dafny's seq prefix order, so route
      // through JSStringLt. Dafny-only: Lean's native `<` is already lexicographic.
      if (_opts.backend === "dafny" && ["<", "<=", ">", ">="].includes(e.op) && e.left.ty.kind === "string") {
        const l = lowerExpr(e.left, binds), r = lowerExpr(e.right, binds);
        const lt = (x: Expr, y: Expr): Expr => ({ kind: "app", fn: "JSStringLt", args: [x, y] });
        const not = (x: Expr): Expr => ({ kind: "unop", op: "¬", expr: x });
        if (e.op === "<") return lt(l, r);
        if (e.op === ">") return lt(r, l);
        if (e.op === "<=") return not(lt(r, l));
        return not(lt(l, r));  // >=
      }
      // Numeric int→real coercion. After resolve, `/` is always real, and any
      // arithmetic/comparison mixing real and integral operands is real-valued.
      // Lift each integral operand to `real` so the backend sees homogeneous
      // real operations (Dafny `as real`, Lean Int→Float).
      if (NUMERIC_OPS.has(e.op)) {
        const realCtx = e.ty.kind === "real" || e.left.ty.kind === "real" || e.right.ty.kind === "real";
        if (realCtx) {
          const lift = (operand: TExpr): Expr => {
            const lowered = lowerExpr(operand, binds);
            return isIntegral(operand.ty) ? { kind: "toReal", expr: lowered } : lowered;
          };
          return { kind: "binop", op: OP_MAP[e.op] ?? e.op, left: lift(e.left), right: lift(e.right) };
        }
      }
      return {
        kind: "binop",
        op: OP_MAP[e.op] ?? e.op,
        left: lowerExpr(e.left, binds),
        right: lowerExpr(e.right, binds),
      };
    }

    case "field": {
      const obj = lowerExpr(e.obj, binds);
      if (e.field === "length" && isArray(e.obj.ty))
        return { kind: "field", obj, field: "size" };
      if (e.field === "length" && e.obj.ty.kind === "string")
        return { kind: "field", obj, field: "length" };
      if (e.field === "size" && (e.obj.ty.kind === "map" || e.obj.ty.kind === "set"))
        return { kind: "field", obj, field: "collectionSize" };
      if (e.isDiscriminant && e.obj.ty.kind === "user") {
        const decl = unionDeclOfTy(_typeDecls, e.obj.ty);
        if (decl?.variants?.some(v => v.name === "true")) {
          return { kind: "field", obj, field: "true_?" };
        }
        if (decl?.variants && decl.discriminant && decl.discriminant !== "__isArray__") {
          _neededKindHelpers.set(decl.name, decl);
          return { kind: "app", fn: kindHelperName(decl), args: [obj] };
        }
      }
      if (e.obj.ty.kind === "user") {
        const baseName = tyBaseName(e.obj.ty.name);
        const decl = declOfKind(_typeDecls, baseName, "discriminated-union");
        const owners = decl?.variants?.filter(v => v.fields.some(f => f.name === e.field)) ?? [];
        if (owners.length > 0) {
          const ownerTy = (v: VariantInfo) => v.fields.find(f => f.name === e.field)?.type;
          const differ = owners.some(v => {
            const a = ownerTy(v), b = ownerTy(owners[0]);
            return a && b && !tyEqual(a, b);
          });
          const matching = differ ? owners.filter(v => { const t = ownerTy(v); return t && tyEqual(t, e.ty); }) : [];
          const ctor = e.ofVariant ?? (matching.length === 1 ? matching[0].name : undefined);
          return { kind: "field", obj, field: e.field, fromUnion: baseName, ctor, datatypeField: true };
        }
      }
      return { kind: "field", obj, field: e.field, datatypeField: isRecordType(e.obj.ty) };
    }

    case "index": {
      const obj = lowerExpr(e.obj, binds);
      const idx = lowerExpr(e.idx, binds);
      if (e.obj.ty.kind === "string") {
        return { kind: "stringIndex", str: obj, idx };
      }
      if (e.obj.ty.kind === "tuple") {
        return { kind: "tupleProj", obj, index: (e.idx as { value: number }).value, arity: e.obj.ty.elems.length };
      }
      if (e.obj.ty.kind === "map") {
        const method = e.ty.kind !== "optional" ? "getDirect" : "get";
        return { kind: "methodCall", obj, objTy: e.obj.ty, method, args: [idx], monadic: false };
      }
      const wrappedIdx = isArray(e.obj.ty) && !isNat(e.idx.ty) ? { kind: "toNat" as const, expr: idx } : idx;
      return { kind: "index", arr: obj, idx: wrappedIdx };
    }

    case "call": {
      if (_opts.backend === "dafny" && e.fn.kind === "var" &&
          (e.fn.name === "MaxOfSeq" || e.fn.name === "MinOfSeq") && e.args.length === 1) {
        const real = e.ty.kind === "real";
        return { kind: "app", fn: real ? `${e.fn.name}Real` : e.fn.name,
          args: [lowerMinMaxSequence(e.args[0], real, binds)] };
      }
      // Array.isArray(x) on a synth array-union (discriminant "__isArray__")
      // → constructor predicate `x.ArrayBranch?`. Used in spec ensures and
      // anywhere `Array.isArray` escapes the narrowing rule (narrow rewrites
      // top-level if-cond Array.isArray uses; this catches the rest).
      if (e.fn.kind === "field" && e.fn.obj.kind === "var" && e.fn.obj.name === "Array" &&
          e.fn.field === "isArray" && e.args.length === 1) {
        const arg = e.args[0];
        if (arg.ty.kind === "user") {
          const decl = declOfTy(_typeDecls, arg.ty);
          if (decl?.kind === "discriminated-union" && decl.discriminant === "__isArray__") {
            return {
              kind: "binop", op: "=",
              left: lowerExpr(arg, binds),
              right: { kind: "constructor", name: "ArrayBranch", type: arg.ty.name, args: [] },
            };
          }
        }
      }
      // String.fromCharCode(n) → preamble function (inverse of charCodeAt,
      // which lowers to `(s[i] as int)`).
      if (e.fn.kind === "field" && e.fn.obj.kind === "var" && e.fn.obj.name === "String" &&
          e.fn.field === "fromCharCode" && e.args.length === 1) {
        return { kind: "app", fn: "StringFromCharCode", args: [lowerExpr(e.args[0], binds)] };
      }
      // Number.isSafeInteger(n) on an integer: a bigint is never a safe integer
      // in JS, so the result is false. A `number` is an unbounded integer in the
      // model, so the JS bound -(2^53 - 1) <= n <= 2^53 - 1 must be stated.
      if (e.fn.kind === "field" && e.fn.obj.kind === "var" && e.fn.obj.name === "Number" &&
          e.fn.field === "isSafeInteger" && e.args.length === 1 && isIntegral(e.args[0].ty)) {
        if (isBigInt(e.args[0].ty)) {
          // The result is false, but JS still evaluates the argument. Keep
          // lifted method calls and pure expressions' proof obligations.
          const value = lowerExpr(e.args[0], binds);
          const result: Expr = { kind: "bool", value: false };
          if (value.kind === "var" || value.kind === "bigint") return result;
          const name = freshName("_safeIntegerArg");
          if (binds) {
            binds.push({ kind: "let", name, type: e.args[0].ty, mutable: false, value });
            return result;
          }
          return { kind: "let", name, type: e.args[0].ty, value, body: result };
        }
        const n = lowerExpr(e.args[0], binds);
        const max = 9007199254740991;
        return {
          kind: "binop", op: "∧",
          left: { kind: "binop", op: "≤", left: { kind: "num", value: -max }, right: n },
          right: { kind: "binop", op: "≤", left: n, right: { kind: "num", value: max } },
        };
      }
      // Number.isSafeInteger(x) on a real: check integrality and safe range via
      // a preamble predicate.
      if (e.fn.kind === "field" && e.fn.obj.kind === "var" && e.fn.obj.name === "Number" &&
          e.fn.field === "isSafeInteger" && e.args.length === 1 && e.args[0].ty.kind === "real") {
        return { kind: "app", fn: "IsSafeIntegerReal", args: [lowerExpr(e.args[0], binds)] };
      }
      // Math.abs/min/max preserve the resolved numeric type. Mixed operands
      // need explicit int/nat→real coercions, just like real binary operations.
      if (e.fn.kind === "field" && e.fn.obj.kind === "var" && e.fn.obj.name === "Math") {
        const minMax = (e.fn.field === "min" || e.fn.field === "max") && e.args.length >= 1;
        const fn = e.fn.field === "abs" && e.args.length === 1 ? "MathAbs"
          : minMax ? (e.fn.field === "min" ? "MathMin" : "MathMax") : null;
        if (fn) {
          const real = e.ty.kind === "real";
          const args = e.args.map((arg): Expr => {
            const lowered = lowerExpr(arg, binds);
            if (real && isIntegral(arg.ty)) return { kind: "toReal", expr: lowered };
            return _opts.backend === "lean" && minMax && e.ty.kind === "int" && isNat(arg.ty)
              ? { kind: "toInt", expr: lowered } : lowered;
          });
          const helper = real ? `${fn}Real` : _opts.backend === "lean" && minMax
            ? `${e.fn.field === "min" ? "Min" : "Max"}.${e.fn.field}` : fn;
          // Unary min/max is identity. Fold positional arguments through the
          // binary helpers so scalar bounds need no sequence/index proofs.
          return minMax
            ? args.slice(1).reduce<Expr>((acc, arg) => ({ kind: "app", fn: helper, args: [acc, arg] }), args[0])
            : { kind: "app", fn: helper, args };
        }
      }
      // Math.ceil(x): CeilReal on real args, identity on int
      if (e.fn.kind === "field" && e.fn.field === "ceil" && e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1) {
        const arg = e.args[0];
        if (arg.ty.kind === "real")
          return { kind: "app", fn: "CeilReal", args: [lowerExpr(arg, binds)] };
        return lowerExpr(arg, binds);
      }
      // Math.floor(x):
      //   - a / b on integral operands → integer floor division, kept in
      //     integer arithmetic (JSFloorDiv on Dafny; native Int/Nat `/` floors
      //     on Lean). Checked first: after resolve, `a / b` is typed `real`, so
      //     the real branch below would otherwise drag it into real arithmetic.
      //   - real arg → FloorReal (Dafny's .Floor)
      //   - int arg → identity
      if (e.fn.kind === "field" && e.fn.field === "floor" && e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1) {
        const arg = e.args[0];
        if (arg.kind === "binop" && arg.op === "/" && isIntegral(arg.left.ty) && isIntegral(arg.right.ty)) {
          const l = lowerExpr(arg.left, binds), r = lowerExpr(arg.right, binds);
          return _opts.backend === "dafny"
            ? { kind: "app", fn: "JSFloorDiv", args: [l, r] }
            : { kind: "binop", op: "/", left: l, right: r };
        }
        if (arg.ty.kind === "real")
          return { kind: "app", fn: "FloorReal", args: [lowerExpr(arg, binds)] };
        return lowerExpr(arg, binds);
      }
      // Math.trunc(x) / Math.round(x):
      //   - trunc(a / b) on integral operands → JSTruncDiv (Lean: Int.tdiv),
      //     checked first for the same reason as the floor case above
      //   - integral arg → identity
      //   - real arg (Dafny only) → TruncReal(x) / FloorReal(x + 0.5); JS
      //     rounds halfway ties toward +Infinity
      // A bigint argument (a JS TypeError) would otherwise lower to the
      // identity, and a Lean real argument has no lowering, so both are
      // rejected. Other calls fall through to the unsupported-call error.
      if (e.fn.kind === "field" && (e.fn.field === "trunc" || e.fn.field === "round") &&
          e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1 &&
          (isIntegral(e.args[0].ty) || e.args[0].ty.kind === "real")) {
        const name = `Math.${e.fn.field}`;
        const arg = e.args[0];
        if (isBigInt(arg.ty))
          throw new Error(`${name} does not accept a bigint argument (JavaScript throws TypeError)`);
        if (e.fn.field === "trunc" && arg.kind === "binop" && arg.op === "/" &&
            isIntegral(arg.left.ty) && isIntegral(arg.right.ty)) {
          return { kind: "app", fn: "JSTruncDiv", args: [lowerExpr(arg.left, binds), lowerExpr(arg.right, binds)] };
        }
        if (isIntegral(arg.ty)) return lowerExpr(arg, binds);
        if (_opts.backend !== "dafny")
          throw new Error("real arithmetic is not supported by the Lean backend (needs noncomputable ℝ / Mathlib).");
        const x = lowerExpr(arg, binds);
        if (e.fn.field === "trunc") return { kind: "app", fn: "TruncReal", args: [x] };
        return {
          kind: "app", fn: "FloorReal",
          args: [{ kind: "binop", op: "+", left: x, right: { kind: "num", value: 0.5 } }],
        };
      }
      // Method call: receiver.method(args) → methodCall node
      if (e.fn.kind === "field") {
        const recv = lowerExpr(e.fn.obj, binds);
        let method = e.fn.field;
        const spec = e.builtinId !== undefined ? builtinSpec(e.builtinId) : null;
        // Lambda-taking array builtins (registry `hof`, comparator excluded —
        // mirrors the historical HOF_METHODS set).
        const isHOF = spec?.hof !== undefined && spec.hof.shape !== "comparator";
        const args = e.args.map((a, i) => {
          const lowered = lowerExpr(a, binds);
          // Lean: a pure fn passed to a HOF by name resolves to the monadic
          // method; redirect to its pure `Pure.` mirror.
          if (_opts.backend === "lean" && isHOF &&
              lowered.kind === "var" && _pureDefNames.has(lowered.name)) {
            return { kind: "var" as const, name: `Pure.${lowered.name}` };
          }
          // Array index args must be nat in Lean: `with`'s index (0), includes/indexOf `from` (1)
          // — registry `intArgPositions`.
          const isArrIdxArg = spec?.intArgPositions !== undefined && spec.intArgPositions.includes(i);
          if (isArrIdxArg && !isNat(a.ty)) return { kind: "toNat" as const, expr: lowered };
          return lowered;
        });
        // arr.concat(...args): each array arg is spread, each value arg appended.
        if (method === "concat" && e.fn.obj.ty.kind === "array") {
          let acc = recv;
          for (let k = 0; k < args.length; k++) {
            const piece: Expr = e.args[k].ty.kind === "array" ? args[k] : { kind: "arrayLiteral", elems: [args[k]] };
            acc = { kind: "binop", op: "arrayConcat", left: acc, right: piece };
          }
          return acc;
        }
        // Spec-context map get: result type is non-optional → direct access
        if (method === "get" && e.fn.obj.ty.kind === "map" && e.ty.kind !== "optional") {
          method = "getDirect";
        }
        // map.set(k, v): if v is an Optional-wrapped map get, unwrap to getDirect
        // (the desugared spread { ...m, [k]: m2[k] } becomes m.set(k, m2.get(k)),
        // but the value should be direct access, not Optional)
        if (method === "set" && e.fn.obj.ty.kind === "map" && args.length === 2) {
          const val = args[1];
          if (val.kind === "methodCall" && val.method === "get" && val.objTy.kind === "map") {
            args[1] = { ...val, method: "getDirect" };
          }
        }
        // Check if any lambda arg has monadic body
        const needsMonadic = _opts.monadic && args.some(a => a.kind === "lambda" && isMonadicBody(a.body));
        const indexed = spec?.hof ? lowerIndexedCallback(recv, e.fn.obj.ty, method, args,
          spec.hof.shape, needsMonadic, _callbackCounter++) : null;
        const result: Expr = indexed ?? { kind: "methodCall", obj: recv, objTy: e.fn.obj.ty, method, args, monadic: needsMonadic };
        // Monadic HOF call is itself monadic — lift via binds like a method call
        if (_opts.monadic && needsMonadic && binds) {
          const name = freshName(`_t${_liftCounter++}`);
          binds.push({ kind: "let-bind", name, value: result });
          return { kind: "var", name };
        }
        return result;
      }
      if (e.fn.kind === "coerce") {
        const fnExpr = lowerExpr(e.fn, binds);
        const args = e.args.map(a => lowerExpr(a, binds));
        if (fnExpr.kind === "var") return { kind: "app", fn: fnExpr.name, args };
        const name = freshName(`_fn${_liftCounter++}`);
        if (binds) {
          binds.push({ kind: "let", name, type: e.fn.ty, mutable: false, value: fnExpr });
          return { kind: "app", fn: name, args };
        }
        return { kind: "let", name, value: fnExpr, body: { kind: "app", fn: name, args } };
      }
      if (e.fn.kind !== "var")
        throw new Error(`Unsupported call expression: ${e.fn.kind}`);
      const prefix = e.callKind === "spec-pure" && _opts.backend === "lean" ? "Pure." : "";
      return { kind: "app", fn: prefix + e.fn.name, args: e.args.map(a => lowerExpr(a, binds)) };
    }

    case "record": {
      // Discriminated union: { kind: 'NoOp' } → constructor NoOp
      if (e.ty.kind === "user" && !e.spread) {
        const tyName = e.ty.name;
        // Match base type name (strip generic args: "Result<Model, Err>" → "Result")
        const baseName = tyBaseName(tyName);
        const decl = declOfKind(_typeDecls, baseName, "discriminated-union", "string-union");
        if (decl && decl.discriminant) {
          const discField = e.fields.find(f => f.name === decl.discriminant);
          if (discField && (discField.value.kind === "str" || discField.value.kind === "bool")) {
            const variantName = String(discField.value.kind === "str" ? discField.value.value : discField.value.value);
            const variant = decl.variants?.find(v => v.name === variantName);
            if (variant) {
              const nonDiscFields = e.fields.filter(f => f.name !== decl.discriminant);
              // Bare-constructor shortcut only when the variant truly has no
              // fields — a variant with only optional fields still needs its
              // None-filled argument list (`int_(None)`, not `int_`).
              if (variant.fields.length === 0) {
                return { kind: "constructor", name: variantName, type: tyName, args: [] };
              }
              // Constructor with args: match variant field order. Emit a bare `app`
              // (Dafny renders `variantName(args)`, a valid unqualified constructor
              // call — unchanged output) tagged with `ctorOf` so the Lean emitter,
              // which CANNOT take a bare constructor name, qualifies it as
              // `BaseType.variantName args`. Use the BASE type name (no generic args):
              // `Result.true_` is valid in Lean; `Result<Model,Err>.true_` is not.
              const args = variant.fields.map(vf => {
                const ef = nonDiscFields.find(f => f.name === vf.name);
                return ef ? lowerExpr(ef.value, binds) : { kind: "var" as const, name: "None" };
              });
              return { kind: "app", fn: variantName, args, ctorOf: baseName };
            }
          }
        }
      }
      // For spread records, propagate declared field types and wrap optionals
      if (e.spread) {
        const spreadTy = e.spread.ty.kind === "optional" ? e.spread.ty.inner : e.spread.ty;
        const structName = spreadTy.kind === "user" ? spreadTy.name : undefined;
        const structDecl = structName ? declOfKind(_typeDecls, structName, "record") : undefined;
        // Also check discriminated-union variants for field types
        const unionDecl = structName ? declOfKind(_typeDecls, structName, "discriminated-union") : undefined;
        const loweredFields = e.fields.map(f => {
          // Propagate declared field type onto value if it has unknown type
          let fieldValue = f.value;
          const fieldDecl = structDecl?.fields?.find(sf => sf.name === f.name);
          let declaredTy: Ty | undefined;
          if (fieldDecl) {
            declaredTy = fieldDecl.type;
          } else if (unionDecl?.variants) {
            for (const v of unionDecl.variants) {
              const vf = v.fields.find(vf => vf.name === f.name);
              if (vf) { declaredTy = vf.type; break; }
            }
          }
          if (declaredTy && fieldValue.ty.kind === "unknown") {
            fieldValue = { ...fieldValue, ty: declaredTy } as TExpr;
          }
          let value = lowerExpr(fieldValue, binds);
          // Wrap non-optional values in Some for optional fields
          if (declaredTy?.kind === "optional") {
            const isUndef = f.value.kind === "var" && f.value.name === "undefined";
            if (f.value.ty.kind !== "optional" && !isUndef) {
              value = { kind: "app", fn: "Some", args: [value] };
            }
          }
          return { name: f.name, value };
        });
        return { kind: "record", spread: lowerExpr(e.spread, binds), fields: loweredFields };
      }
      // Empty record with map type → empty map
      if (e.fields.length === 0 && !e.spread && e.ty.kind === "map") {
        return { kind: "emptyMap" };
      }
      // Non-empty record literal with map type — emit as a flat Dafny map
      // literal `map[k1 := v1, k2 := v2, ...]`. (A chain of `m["k" := v]`
      // works for a handful of entries but Dafny's type resolver stack-
      // overflows on hundreds; the flat form is fine at any size.)
      if (e.fields.length > 0 && !e.spread && e.ty.kind === "map") {
        return {
          kind: "mapLiteral",
          entries: e.fields.map(f => ({
            key: { kind: "str" as const, value: f.name },
            value: lowerExpr(f.value, binds),
          })),
        };
      }
      // Carry the resolved record type so the emitter can pick the right
      // constructor when two datatypes share a field-name set (Event vs
      // SparseEvent) — structural matching alone would take the first-declared.
      const recName = e.ty.kind === "user" ? tyBaseName(e.ty.name) : undefined;
      const ctor = recName && declOfKind(_typeDecls, recName, "record") ? recName : undefined;
      return { kind: "record", spread: null, ctor, fields: e.fields.map(f => ({ name: f.name, value: lowerExpr(f.value, binds) })) };
    }

    case "arrayLiteral":
      if (e.ty.kind === "map" && e.elems.length === 0) return { kind: "emptyMap" };
      if (e.ty.kind === "set" && e.elems.length === 0) return { kind: "emptySet" };
      // Set with initial elements: new Set([a, b]) → {a, b}
      if (e.ty.kind === "set") return { kind: "app", fn: "SetLiteral", args: e.elems.map(el => lowerExpr(el, binds)) };
      if (e.ty.kind === "tuple") return { kind: "tupleLiteral", elems: e.elems.map(el => lowerExpr(el, binds)) };
      return { kind: "arrayLiteral", elems: e.elems.map(el => lowerExpr(el, binds)) };

    case "lambda": {
      if (e.params.some(p => p.rest || p.defaultValue)) {
        throw new Error("lambda rest/default bindings require a known callback argument list");
      }
      // Pass the module typeDecls (not []), so type lookups inside the lambda
      // body — e.g. a `switch`'s variant fields — resolve. A bare `[]` left a
      // discriminated-union switch in a lambda with binderless patterns.
      const body = transformStmts(e.body, _typeDecls);
      // Flatten an if/let/return-shaped multi-statement body into a single
      // `return <expr>` so both backends' single-return-lambda fast path emits
      // it (Dafny lambdas are expression-only; Lean prefers the expression form
      // over a `do` block). Bodies with shapes we can't reduce (loops, bare
      // side effects) are left as-is.
      const flat = flattenLambdaBody(body);
      return {
        kind: "lambda",
        params: e.params.map(p => ({ name: p.name, type: p.ty })),
        body: flat === null ? body : [{ kind: "return", value: flat }],
      };
    }

    case "forall":
      return { kind: "forall", var: e.var, type: e.varTy, body: transformExpr(e.body) };

    case "exists":
      return { kind: "exists", var: e.var, type: e.varTy, body: transformExpr(e.body) };

    case "conditional": {
      const cond = lowerExpr(asCondition(e.cond), binds);
      const thenBinds: Stmt[] | null = binds ? [] : null;
      const elseBinds: Stmt[] | null = binds ? [] : null;
      let thenExpr = lowerExpr(e.then, thenBinds);
      let elseExpr = lowerExpr(e.else, elseBinds);
      if (e.ty.kind === "optional") {
        thenExpr = wrapForOptional(thenExpr, e.then.ty, e.ty);
        elseExpr = wrapForOptional(elseExpr, e.else.ty, e.ty);
      }
      if (binds && (thenBinds?.length || elseBinds?.length)) {
        const name = freshName(`_branch${_branchCounter++}`);
        binds.push({ kind: "let", name, type: e.ty, mutable: true,
          value: { kind: _opts.backend === "dafny" ? "havoc" : "default", type: e.ty } });
        binds.push({ kind: "if", cond,
          then: [...(thenBinds ?? []), { kind: "assign", target: name, value: thenExpr }],
          else: [...(elseBinds ?? []), { kind: "assign", target: name, value: elseExpr }] });
        return { kind: "var", name };
      }
      return { kind: "if", cond, then: thenExpr, else: elseExpr };
    }

    case "optChain": {
      // Single-evaluation optional chain: evaluate `obj` once, then apply `chain`
      // only when `obj` is present (Some / Value).
      if (e.obj.ty.kind !== "optional") {
        const applied = applyChain(e.obj, e.chain);
        const lowered = lowerExpr(applied, binds);
        return e.ty.kind === "optional" ? wrapForOptional(lowered, applied.ty, e.ty) : lowered;
      }
      const isNullish = e.obj.ty.nullish === "both";
      const innerTy = e.obj.ty.inner;
      const objExpr = lowerExpr(e.obj, binds);
      const isSimpleVar = e.obj.kind === "var";
      const tmpName = e.obj.kind === "var" ? e.obj.name : freshName(`_oc${_liftCounter++}`);
      const scrTExpr: TExpr = isSimpleVar ? e.obj : { kind: "var", name: tmpName, ty: e.obj.ty };
      const scrExpr: Expr = isSimpleVar ? objExpr : { kind: "var", name: tmpName };
      const cond: Expr = { kind: "nullishTest", expr: scrExpr, test: isNullish ? "isValue" : "isSome" };
      const appliedTExpr = applyChain({ kind: "coerce", expr: scrTExpr, ty: innerTy }, e.chain);
      const someBinds: Stmt[] | null = binds ? [] : null;
      let someExpr = lowerExpr(appliedTExpr, someBinds);
      if (e.ty.kind === "optional") {
        someExpr = wrapForOptional(someExpr, appliedTExpr.ty, e.ty);
      }
      const noneExpr: Expr = e.ty.kind === "optional"
        ? wrapForOptional({ kind: "var", name: "undefined" }, UNDEFINED, e.ty)
        : { kind: "constructor", name: "none", type: "Option", args: [] };
      if (binds && someBinds?.length) {
        if (!isSimpleVar) {
          binds.push({ kind: "let", name: tmpName, type: e.obj.ty, mutable: false, value: objExpr });
        }
        const resName = freshName(`_branch${_branchCounter++}`);
        binds.push({ kind: "let", name: resName, type: e.ty, mutable: true, value: noneExpr });
        binds.push({ kind: "if", cond, then: [...someBinds, { kind: "assign", target: resName, value: someExpr }], else: [] });
        return { kind: "var", name: resName };
      }
      const ite: Expr = { kind: "if", cond, then: someExpr, else: noneExpr };
      return isSimpleVar ? ite : { kind: "let", name: tmpName, value: objExpr, body: ite };
    }

    case "nullish": {
      // Single-evaluation nullish coalescing: evaluate `left` once, evaluate `right`
      // only when `left` is absent (None / Null / Undefined).
      if (e.left.ty.kind !== "optional") {
        const left = lowerExpr(e.left, binds);
        return lowerCoerce(left, e.left.ty, e.ty, binds);
      }
      const isNullish = e.left.ty.nullish === "both";
      const innerTy = e.left.ty.inner;
      const leftExpr = lowerExpr(e.left, binds);
      const isSimpleVar = e.left.kind === "var";
      const tmpName = e.left.kind === "var" ? e.left.name : freshName(`_nc${_liftCounter++}`);
      const scrExpr: Expr = isSimpleVar ? leftExpr : { kind: "var", name: tmpName };
      const cond: Expr = { kind: "nullishTest", expr: scrExpr, test: isNullish ? "isValue" : "isSome" };
      const someBinds: Stmt[] | null = binds ? [] : null;
      const noneBinds: Stmt[] | null = binds ? [] : null;
      let someExpr = lowerCoerce(scrExpr, e.left.ty, innerTy, someBinds);
      if (e.ty.kind === "optional") {
        someExpr = wrapForOptional(someExpr, innerTy, e.ty);
      }
      let noneExpr = lowerExpr(e.right, noneBinds);
      if (e.ty.kind === "optional") {
        noneExpr = wrapForOptional(noneExpr, e.right.ty, e.ty);
      }
      if (binds && (someBinds?.length || noneBinds?.length)) {
        if (!isSimpleVar) {
          binds.push({ kind: "let", name: tmpName, type: e.left.ty, mutable: false, value: leftExpr });
        }
        const resName = freshName(`_branch${_branchCounter++}`);
        binds.push({ kind: "let", name: resName, type: e.ty, mutable: true,
          value: { kind: _opts.backend === "dafny" ? "havoc" : "default", type: e.ty } });
        binds.push({ kind: "if", cond,
          then: [...(someBinds ?? []), { kind: "assign", target: resName, value: someExpr }],
          else: [...(noneBinds ?? []), { kind: "assign", target: resName, value: noneExpr }] });
        return { kind: "var", name: resName };
      }
      const ite: Expr = { kind: "if", cond, then: someExpr, else: noneExpr };
      return isSimpleVar ? ite : { kind: "let", name: tmpName, value: leftExpr, body: ite };
    }

    case "havoc":
      // Dafny's * only works in var/assign positions — lift to own declaration
      if (binds) {
        const name = freshName(`_t${_liftCounter++}`);
        binds.push({ kind: "let", name, type: e.ty, mutable: false, value: { kind: "havoc", type: e.ty } });
        return { kind: "var", name };
      }
      return { kind: "havoc", type: e.ty };

    case "tagMatch": {
      // Expression-form tagMatch — emitted by `ruleImplArrayIsArray` for spec
      // implications like `Array.isArray(x) ==> B` and by
      // `ruleConditionalArrayIsArray` for ternary narrowing. Substitutes
      // scrutinee field accesses and (for synth array-unions) scrutinee
      // path occurrences inside each arm with the variant's payload binder.
      // Path scrutinees (e.g. `m.content`) get a synthesized hint derived
      // from the last field/var name so the binder reads naturally.
      const scrutinee = lowerExpr(e.scrutinee, binds);
      const decl = declOf(_typeDecls, e.typeName);
      const isSynthArrayUnion = decl?.discriminant === "__isArray__";
      const varName = e.scrutinee.kind === "var" ? e.scrutinee.name : undefined;
      const pathHint = varName ?? scrutineeHint(e.scrutinee);
      const wrapOpt = e.ty.kind === "optional";
      const arms: MatchArm[] = e.cases.map(c => {
        const variant = decl?.variants?.find(v => v.name === c.variant);
        const fields = variant?.fields ?? [];
        let body = lowerExpr(c.body, binds);
        if (varName && fields.length > 0) {
          body = replaceFieldAccess(body, varName, fields, c.variant, tyBaseName(e.typeName));
          if (isSynthArrayUnion && fields.length === 1) {
            body = replaceVarInExpr(body, varName, matchBinder(fields[0].name, varName));
          }
        } else if (!varName && isSynthArrayUnion && fields.length === 1) {
          // Path scrutinee (e.g. `m.content`): replace structural occurrences
          // with the binder var ref.
          const binderName = matchBinder(fields[0].name, pathHint);
          body = replaceExprInExpr(body, scrutinee, { kind: "var", name: binderName });
        }
        if (wrapOpt) body = wrapOptionalBranch(body, c.body);
        return { pattern: buildMatchPattern(c.variant, fields, pathHint), body };
      });
      if (e.fallthrough) {
        let body = lowerExpr(e.fallthrough, binds);
        if (wrapOpt) body = wrapOptionalBranch(body, e.fallthrough);
        arms.push({ pattern: pWild(), body });
      }
      return { kind: "match", scrutinee: varName !== undefined ? varE(varName) : scrutinee, arms };
    }
  }
}

function flattenImpl(e: TExpr): { premises: TExpr[]; conclusion: TExpr } {
  if (e.kind === "binop" && e.op === "==>") {
    const lhs = splitConj(e.left);
    const rest = flattenImpl(e.right);
    return { premises: [...lhs, ...rest.premises], conclusion: rest.conclusion };
  }
  return { premises: [], conclusion: e };
}

function splitConj(e: TExpr): TExpr[] {
  if (e.kind === "binop" && e.op === "&&") return [...splitConj(e.left), ...splitConj(e.right)];
  return [e];
}

// ── Ensures-to-match for discriminated unions ────────────────

function ensuresToMatch(e: TExpr, typeDecls: TypeDeclInfo[]): Expr | null {
  if (e.kind !== "binop" || e.op !== "==>") return null;
  if (e.left.kind !== "binop" || e.left.op !== "===") return null;
  if (e.left.left.kind !== "field" || !e.left.left.isDiscriminant || e.left.right.kind !== "str") return null;

  const obj = e.left.left.obj;
  if (obj.kind !== "var" || obj.ty.kind !== "user") return null;
  const typeName = obj.ty.name;
  const decl = declOfKind(typeDecls, typeName, "discriminated-union");
  if (!decl) return null;

  const variantName = e.left.right.value;
  const variant = decl.variants?.find(v => v.name === variantName);
  if (!variant) return null;

  const fields = variant.fields;
  const pattern = buildMatchPattern(variantName, fields, obj.name);

  let rhs = transformExpr(e.right);
  rhs = replaceFieldAccess(rhs, obj.name, fields);

  return { kind: "match", scrutinee: varE(obj.name), arms: [{ pattern, body: rhs }, { pattern: pWild(), body: { kind: "bool", value: true } }] };
}

function replaceFieldAccess(e: Expr, varName: string, fields: { name: string; tsType: string }[], ctorName?: string, ctorOf?: string): Expr {
  return mapExpr(e, x => {
    if (x.kind === "field" && x.obj.kind === "var" && x.obj.name === varName) {
      const f = fields.find(f => f.name === x.field);
      if (f) return { kind: "var", name: matchBinder(f.name, varName) };
    }
    // Datatype update of the scrutinee (`{ ...vn, f: v }`): the arm knows the
    // variant, so stamp it — emitters need it for per-constructor destructor
    // names. Recurse manually (returning a node stops mapExpr's own descent).
    if (ctorName && x.kind === "record" && !x.ctor && x.spread &&
        x.spread.kind === "var" && x.spread.name === varName) {
      return { ...x, ctor: ctorName, ctorOf,
        fields: x.fields.map(f => ({ ...f, value: replaceFieldAccess(f.value, varName, fields, ctorName, ctorOf) })) };
    }
    // If this let shadows the matched variable, stop replacing in the body
    if (x.kind === "let" && x.name === varName) return { ...x, value: replaceFieldAccess(x.value, varName, fields, ctorName, ctorOf) };
    return null;
  });
}

/** Replace bare `var(oldName)` references → `var(newName)` in lowered IR.
 *  Used inside synth array-union match arms: the user code refers to the
 *  scrutinee by its bare name (`content`), but in the arm body that name
 *  must refer to the variant's sole payload binder (`i_content_arr`). */
function replaceVarInExpr(e: Expr, oldName: string, newName: string): Expr {
  return mapExpr(e, x => {
    if (x.kind === "var" && x.name === oldName) return { kind: "var", name: newName };
    // If a binding shadows the name, stop substituting inside its body.
    if (x.kind === "let" && x.name === oldName) return { ...x, value: replaceVarInExpr(x.value, oldName, newName) };
    return null;
  });
}

/** Structural equality on Expr access-paths (var / field chain). Enough to
 *  match the scrutinee `m.content` against later occurrences in a match arm. */
function exprPathEqual(a: Expr, b: Expr): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "var" && b.kind === "var") return a.name === b.name;
  if (a.kind === "field" && b.kind === "field") return a.field === b.field && exprPathEqual(a.obj, b.obj);
  return false;
}

/** Substitute every occurrence of `target` (an access-path Expr) with `repl`
 *  inside `e`. Mirror of `replaceVarInExpr` but keyed on a sub-path rather
 *  than a bare name — needed when the narrowing scrutinee is `m.content`
 *  (field access) rather than a bare `content` (var). */
function replaceExprInExpr(e: Expr, target: Expr, repl: Expr): Expr {
  return mapExpr(e, x => {
    if (exprPathEqual(x, target)) return repl;
    return null;
  });
}

/** Extract a short reader-friendly hint for a TExpr access-path: the last
 *  field name in a field chain, or the var name. Used to derive a stable
 *  binder prefix when the scrutinee isn't a bare var. */
function scrutineeHint(e: TExpr): string {
  if (e.kind === "var") return e.name;
  if (e.kind === "field") return e.field;
  return "x";
}

// ── Transform statements ─────────────────────────────────────

// `if (X) continue; rest` → `if (!X) { rest }` at the top of a loop body.
// Dafny's lowered while-loops have the index increment at the bottom, so a
// `continue` would skip it and loop forever; rewriting to if/else lets the
// loop fall through normally. The operand is already-lowered IR, where
// negation is spelled `¬` (lowerExpr rewrites `!`).
function negateExpr(e: Expr): Expr {
  if (e.kind === "unop" && e.op === "¬") return e.expr;
  return { kind: "unop", op: "¬", expr: e };
}

/** Build the two pieces of an `arr.pop()` lowering on a named array variable:
 *  - `optValue` is `(if |arr|>0 then Some(arr[|arr|-1]) else None)` (the popped element)
 *  - `guardedTrunc` is `(if |arr|>0 then arr[..|arr|-1] else arr)` (the array minus its last element)
 *  Callers wrap these in let/assign statements appropriate to their context. */
function buildPopLowering(arrExpr: Expr, arrTy: Ty): { optValue: Expr; guardedTrunc: Expr } {
  const arrLen: Expr = { kind: "field", obj: arrExpr, field: "size" };
  const lastIdx: Expr = { kind: "binop", op: "-", left: arrLen, right: { kind: "num", value: 1 } };
  const lastElem: Expr = { kind: "index", arr: arrExpr, idx: lastIdx };
  const isNonEmpty: Expr = { kind: "binop", op: ">", left: arrLen, right: { kind: "num", value: 0 } };
  const optValue: Expr = { kind: "if", cond: isNonEmpty,
    then: { kind: "constructor", name: "some", type: "Option", args: [lastElem] },
    else: { kind: "constructor", name: "none", type: "Option", args: [] } };
  const truncated: Expr = { kind: "methodCall", obj: arrExpr, objTy: arrTy, method: "slice",
    args: [{ kind: "num", value: 0 }, lastIdx], monadic: false };
  const guardedTrunc: Expr = { kind: "if", cond: isNonEmpty, then: truncated, else: arrExpr };
  return { optValue, guardedTrunc };
}
/**
 * Velvet (Lean backend) rejects `return` inside a loop. For a function shaped as
 * `…; while (…) { … early returns … }; return fallthrough`, hoist a mutable
 * result variable: each in-loop `return e` becomes `_loopRet := e; break`, then
 * `return _loopRet` after the loop. The trailing fallthrough return seeds
 * `_loopRet`, so a normal loop exit returns it unchanged. Dafny is untouched —
 * it keeps the native early returns.
 */
function stmtsContainReturn(stmts: Stmt[]): boolean {
  for (const s of stmts) {
    if (s.kind === "return") return true;
    if (s.kind === "if" && (stmtsContainReturn(s.then) || stmtsContainReturn(s.else))) return true;
    if (s.kind === "match" && s.arms.some(a => stmtsContainReturn(a.body))) return true;
    // Don't descend into a nested while — its returns would target that loop.
  }
  return false;
}

function replaceReturnsWithBreak(stmts: Stmt[], retVar: string): Stmt[] {
  return stmts.flatMap((s): Stmt[] => {
    if (s.kind === "return") return [{ kind: "assign", target: retVar, value: s.value }, { kind: "break" }];
    if (s.kind === "if") return [{ ...s, then: replaceReturnsWithBreak(s.then, retVar), else: replaceReturnsWithBreak(s.else, retVar) }];
    if (s.kind === "match") return [{ ...s, arms: s.arms.map(a => ({ ...a, body: replaceReturnsWithBreak(a.body, retVar) })) }];
    return [s];
  });
}

// Seed value for `_loopRet` when a return-in-loop function has no trailing
// fallthrough return. Readable literals for the primitives; everything else
// (user types, arrays, maps, optionals) gets a typed `default : T` rather than a
// type-incorrect `0` — these types derive `Inhabited`, so the default exists.
function defaultExprForTy(ty: Ty): Expr {
  switch (ty.kind) {
    case "bool": return { kind: "bool", value: false };
    case "string": return { kind: "str", value: "" };
    case "nat": case "int": case "real": return { kind: "num", value: 0 };
    default: return { kind: "default", type: ty };
  }
}

function eliminateReturnInLoops(stmts: Stmt[], retTy: Ty, resultInvariants: Expr[]): Stmt[] {
  const out: Stmt[] = [];
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    if (s.kind === "while" && stmtsContainReturn(s.body)) {
      const retVar = "_loopRet";
      const next = stmts[i + 1];
      const init: Expr = next && next.kind === "return" ? next.value : defaultExprForTy(retTy);
      out.push({ kind: "let", name: retVar, type: retTy, mutable: true, value: init });
      // The result variable carries the postcondition (the function's `ensures`
      // with `\result` → `_loopRet`) as a loop invariant: it holds initially (the
      // fallthrough seed) and after each `_loopRet := e; break`, so the
      // postcondition is re-established from the invariant when the loop exits.
      // Where Dafny discharged the postcondition at each `return` site, the
      // break-rewrite discharges it once, after the loop.
      out.push({ ...s, invariants: [...s.invariants, ...resultInvariants], body: replaceReturnsWithBreak(s.body, retVar) });
      out.push({ kind: "return", value: { kind: "var", name: retVar } });
      if (next && next.kind === "return") i++; // consume the seeded fallthrough return
    } else {
      out.push(s);
    }
  }
  return out;
}

/** True if `name` is referenced as a variable anywhere in `stmts`. Conservative:
 *  counts every occurrence and ignores shadowing — a spurious hit only costs an
 *  unused `let`, whereas a miss would leave a binder unbound. */
function stmtsUseVar(stmts: Stmt[], name: string): boolean {
  return anyExprInStmts(stmts, e => e.kind === "var" && e.name === name);
}

/**
 * Velvet (Lean backend) cannot synthesize a `WPGen` for a monadic statement
 * `match` on a user inductive in a method body (loom's matcher-WPGen drops a
 * `sorry`). loom *can* handle method-body `if`s (cf. examples/arrayEquals), so
 * lower such matches to discriminator `if`-chains: `match x with | .C f.. => B`
 * becomes `if x.C? then (let f := x.f-destructor; B) else …`. Constructor field
 * binders become `let`s bound to the (already-supported) union destructor. Option
 * matches and other non-user matches are left alone (loom handles those). Dafny
 * is untouched — it keeps the native match.
 */
function matchToIfChains(stmts: Stmt[]): Stmt[] {
  return stmts.flatMap((s): Stmt[] => {
    if (s.kind === "if") return [{ ...s, then: matchToIfChains(s.then), else: matchToIfChains(s.else) }];
    if (s.kind === "while") return [{ ...s, body: matchToIfChains(s.body) }];
    if (s.kind === "forin") return [{ ...s, body: matchToIfChains(s.body) }];
    if (s.kind !== "match") return [s];

    const arms = s.arms.map(a => ({ ...a, body: matchToIfChains(a.body) }));
    // Literal-value matches are not user-inductive matches and need no
    // discriminator rewrite. In particular, don't let a later ctor arm make us
    // accidentally drop an earlier literal arm from a malformed mixed match.
    if (arms.some(a => a.pattern.kind === "literal")) return [{ ...s, arms }];
    const ctorArms = arms.filter(a => a.pattern.kind === "ctor");
    const firstCtor = ctorArms[0] ? patternCtor(ctorArms[0].pattern) : undefined;
    const decl = firstCtor ? declWithVariant(_typeDecls, firstCtor) : undefined;
    if (!decl) return [{ ...s, arms }]; // not a user union (e.g. Option) — leave as match

    const scrutExpr: Expr = s.scrutinee;
    const defaultArm = arms.find(a => a.pattern.kind === "wild");
    const declaredCtors = decl.kind === "discriminated-union"
      ? decl.variants?.map(v => v.name)
      : decl.kind === "string-union" ? decl.values : undefined;
    const coveredCtors = new Set(ctorArms.map(a => patternCtor(a.pattern)).filter((c): c is string => !!c));
    const exhaustiveWithoutDefault = !defaultArm && !!declaredCtors && declaredCtors.every(c => coveredCtors.has(c));
    let elseBranch: Stmt[] = defaultArm ? defaultArm.body : [];
    for (let k = ctorArms.length - 1; k >= 0; k--) {
      const armBody = ctorArms[k].body;
      if (armBody.length === 0) continue; // empty arm (no-op) — let it fall through to `else`
      const ctor = patternCtor(ctorArms[k].pattern) ?? "";
      const binders = patternBinders(ctorArms[k].pattern);
      const variant = decl.variants?.find(v => v.name === ctor);
      // Discriminator condition. A nullary discriminated-union constructor would
      // need `DecidableEq` for `x = .Ctor` (which such unions don't derive), so
      // use a match-bool instead. Multi-field ctors already lower to a match-bool;
      // string-unions derive DecidableEq, so `=` is fine there.
      const cond: Expr = decl.kind === "discriminated-union" && binders.length === 0
        ? { kind: "match", scrutinee: scrutExpr, arms: [
            { pattern: pCtor(ctor), body: { kind: "bool", value: true } },
            { pattern: pWild(), body: { kind: "bool", value: false } }] }
        : { kind: "binop", op: "=", left: scrutExpr, right: { kind: "constructor", name: ctor, type: decl.name, args: [] } };
      // Bind only the constructor-field binders the body actually uses, pinning the
      // owning ctor so the destructor doesn't guess (variants share field names).
      const lets: Stmt[] = [];
      binders.forEach((b, i) => {
        const f = variant?.fields[i];
        if (b !== "_" && f && stmtsUseVar(armBody, b)) lets.push({
          kind: "let", name: b, type: f.type ?? { kind: "unknown" }, mutable: false,
          value: { kind: "field", obj: scrutExpr, field: f.name, fromUnion: decl.name, ctor },
        });
      });
      // An exhaustive source match has no fallthrough. Use its final arm as
      // the unconditional else branch; emitting `else pure ()` would force a
      // Unit result even when every arm returns the method's result type.
      if (exhaustiveWithoutDefault && k === ctorArms.length - 1) {
        elseBranch = [...lets, ...armBody];
        continue;
      }
      elseBranch = [{ kind: "if", cond, then: [...lets, ...armBody], else: elseBranch }];
    }
    return elseBranch;
  });
}

/** True if `stmts` contain a `break` not nested inside another while. */
function stmtsContainBreak(stmts: Stmt[]): boolean {
  for (const s of stmts) {
    if (s.kind === "break") return true;
    if (s.kind === "if" && (stmtsContainBreak(s.then) || stmtsContainBreak(s.else))) return true;
    if (s.kind === "match" && s.arms.some(a => stmtsContainBreak(a.body))) return true;
  }
  return false;
}

/**
 * loom's default loop-exit fact is `¬guard`, which does not hold for a loop that
 * `break`s (a break exits with the guard still true). Such loops need an explicit
 * `//@ done_with` in the TS source (`//@ done_with true` when the loop invariant
 * alone carries the exit facts). Rather than silently supplying one, reject —
 * the exit fact is part of the spec and belongs beside the invariants.
 * Lean-only; Dafny derives loop-exit facts from the break sites themselves.
 */
function requireDoneWithForBreaks(stmts: Stmt[], fnName: string): void {
  for (const s of stmts) {
    if (s.kind === "if") { requireDoneWithForBreaks(s.then, fnName); requireDoneWithForBreaks(s.else, fnName); }
    if (s.kind === "match") for (const a of s.arms) requireDoneWithForBreaks(a.body, fnName);
    if (s.kind === "while") {
      if (!s.doneWith && stmtsContainBreak(s.body)) {
        throw new Error(
          `${fnName}: loop with break needs //@ done_with on the Lean backend ` +
          `(an early return in a loop also lowers to a break). ` +
          `Use //@ done_with true when the loop invariants carry the exit facts.`);
      }
      requireDoneWithForBreaks(s.body, fnName);
    }
  }
}

/** The forin emission places the index increment at the loop-body end, so a
 *  surviving `continue` would skip it. Insert the increment immediately
 *  before every same-scope continue (nested loops own their continues),
 *  mirroring the C-style-for desugar's discipline. */
function insertIncrementBeforeContinue(stmts: Stmt[], idxName: string): Stmt[] {
  const incr: Stmt = { kind: "assign", target: idxName,
    value: { kind: "binop", op: "+", left: { kind: "var", name: idxName }, right: { kind: "num", value: 1 } } };
  const walk = (ss: Stmt[]): Stmt[] => {
    const out: Stmt[] = [];
    for (const s of ss) {
      if (s.kind === "continue") { out.push(incr, s); continue; }
      if (s.kind === "if") { out.push({ ...s, then: walk(s.then), else: walk(s.else) }); continue; }
      if (s.kind === "match") { out.push({ ...s, arms: s.arms.map(a => ({ ...a, body: walk(a.body) })) }); continue; }
      out.push(s);
    }
    return out;
  };
  return walk(stmts);
}

function eliminateTopLevelContinue(stmts: Stmt[]): Stmt[] {
  const out: Stmt[] = [];
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    // `if (X) {...A, continue}; rest` (empty else, trailing continue in then)
    // — if A is empty, rewrite to `if (!X) { rest }`; otherwise rewrite to
    // `if (X) { ...A } else { rest }`. Either form lets the loop fall through
    // naturally past the bottom of the body.
    if (s.kind === "if" && s.else.length === 0 &&
        s.then.length >= 1 && s.then[s.then.length - 1].kind === "continue") {
      const rest = eliminateTopLevelContinue(stmts.slice(i + 1));
      const thenWithoutContinue = s.then.slice(0, -1);
      if (thenWithoutContinue.length === 0) {
        out.push({ kind: "if", cond: negateExpr(s.cond), then: rest, else: [] });
      } else {
        out.push({ kind: "if", cond: s.cond, then: thenWithoutContinue, else: rest });
      }
      return out;
    }
    // narrow.ts's ruleEarlyReturnConsume rewrites `if (!x) continue; rest`
    // (when x is Optional) to a someMatch which transform.ts then emits as a
    // `match`. A trailing `continue` inside a match arm is a no-op when the
    // match is the last statement in the loop body — drop it.
    if (s.kind === "match" && i === stmts.length - 1) {
      const arms = s.arms.map(arm => {
        const b = arm.body;
        if (b.length > 0 && b[b.length - 1].kind === "continue") {
          return { ...arm, body: b.slice(0, -1) };
        }
        return arm;
      });
      out.push({ ...s, arms });
      continue;
    }
    out.push(s);
  }
  return out;
}

function transformStmts(stmts: TStmt[], typeDecls: TypeDeclInfo[]): Stmt[] {
  const result: Stmt[] = [];
  let i = 0;
  while (i < stmts.length) {
    const s = stmts[i];
    // Transform for-of → for-in over range
    if (s.kind === "forof") {
      const headName = s.names[0];
      const headTy = s.nameTypes[0] ?? { kind: "unknown" as const };
      const { binds: iterBinds, expr: iterExpr } = liftMethodCalls(s.iterable);
      result.push(...iterBinds);

      // All for-of shapes lower to the same range loop `for idx in 0..seq.size`;
      // they differ only in (a) which indexable `seq` is iterated and (b) the
      // per-iteration `let`s that bind the loop names. Compute the shared loop-
      // variable naming once, then let each shape fill in `seq` + `perIter`.
      const count = _forofCounters.get(headName) ?? 0;
      _forofCounters.set(headName, count + 1);
      const suffix = count === 0 ? "" : `${count + 1}`;
      const idxName = freshName(`_${headName}_idx${suffix}`);
      const idxVar: Expr = { kind: "var", name: idxName };

      let seq: Expr;
      let perIter: Stmt[];

      if (s.iterable.ty.kind === "map") {
        // for (const k of map) / for (const [k, v] of map): materialize the keys
        // as a seq and index into it; a value name looks up via getDirect.
        const keyTy = s.nameTypes[0] ?? s.iterable.ty.key ?? { kind: "unknown" as const };
        const keysSeqName = freshName(`_${headName}_keys${suffix}`);
        result.push({ kind: "let", name: keysSeqName, type: { kind: "array", elem: keyTy }, mutable: false,
          value: { kind: "app", fn: "SetToSeq", args: [{ kind: "field", obj: iterExpr, field: "keys" }] } });
        seq = { kind: "var", name: keysSeqName };
        const letKey: Stmt = { kind: "let", name: headName, type: keyTy, mutable: false, value: { kind: "index", arr: seq, idx: idxVar } };
        if (s.names.length >= 2) {
          const valueTy = s.nameTypes[1] ?? { kind: "unknown" as const };
          const letVal: Stmt = { kind: "let", name: s.names[1], type: valueTy, mutable: false,
            value: { kind: "methodCall", obj: iterExpr, objTy: s.iterable.ty, method: "getDirect", args: [{ kind: "var", name: headName }], monadic: false } };
          perIter = [letKey, letVal];
        } else {
          perIter = [letKey];
        }
      } else if (s.names.length >= 2 && s.iterable.ty.kind === "array" && s.iterable.ty.elem.kind === "tuple") {
        // for (const [a, b] of tupleArr): bind the element once, then destructure
        // it into each name via a tuple projection.
        const tupleTy = s.iterable.ty.elem;
        seq = iterExpr;
        const elemName = freshName(`_${headName}_elem${suffix}`);
        const letElem: Stmt = { kind: "let", name: elemName, type: tupleTy, mutable: false, value: { kind: "index", arr: seq, idx: idxVar } };
        perIter = [letElem, ...s.names.map((n, k): Stmt => ({
          kind: "let", name: n, type: tupleTy.elems[k] ?? { kind: "unknown" }, mutable: false,
          value: { kind: "tupleProj", obj: { kind: "var", name: elemName }, index: k, arity: tupleTy.elems.length },
        }))];
      } else {
        // Single element by index. Sets aren't indexable, so materialize first.
        if (s.iterable.ty.kind === "set") {
          const seqName = freshName(`_${headName}_seq${suffix}`);
          const elemTy: Ty = headTy.kind !== "unknown" ? headTy : { kind: "string" };
          result.push({ kind: "let", name: seqName, type: { kind: "array", elem: elemTy }, mutable: false,
            value: { kind: "app", fn: "SetToSeq", args: [iterExpr] } });
          seq = { kind: "var", name: seqName };
        } else {
          seq = iterExpr;
        }
        perIter = [{ kind: "let", name: headName, type: headTy, mutable: false, value: { kind: "index", arr: seq, idx: idxVar } }];
      }

      const arrSize: Expr = { kind: "field", obj: seq, field: "size" };
      // Auto-add bound invariant: idx ≤ bound (always true for range loops)
      const boundInv: Expr = { kind: "binop", op: "≤", left: idxVar, right: arrSize };
      const bodyStmts = insertIncrementBeforeContinue(
        eliminateTopLevelContinue(transformStmts(s.body, typeDecls)), idxName);
      result.push({
        kind: "forin", idx: idxName, bound: arrSize,
        invariants: [boundInv, ...s.invariants.map(transformExpr)],
        body: [...perIter, ...bodyStmts],
      });
      i++;
      continue;
    }
    result.push(...transformStmt(s, typeDecls));
    i++;
  }
  return result;
}

let _liftCounter = 0;
let _callbackCounter = 0;
// Branch results must not renumber the existing lifted-call temporaries.
let _branchCounter = 0;

function liftMethodCalls(e: TExpr): { binds: Stmt[]; expr: Expr } {
  const binds: Stmt[] = [];
  return { binds, expr: lowerExpr(e, binds) };
}

// ── Transform statements ─────────────────────────────────────

function transformStmt(s: TStmt, typeDecls: TypeDeclInfo[]): Stmt[] {
  switch (s.kind) {
    case "let": {
      // Whole-init havoc: emit directly, no lifting
      if (s.init.kind === "havoc") {
        return [{ kind: "let", name: s.name, type: s.ty, mutable: s.mutable, value: { kind: "havoc", type: s.init.ty } }];
      }
      // arr.shift()! → let x = arr[0]; arr = arr[1..]
      const init = s.init.kind === "call" ? s.init : undefined;
      if (init && init.fn.kind === "field" && init.fn.field === "shift" && init.fn.obj.ty.kind === "array") {
        const arrName = init.fn.obj.kind === "var" ? init.fn.obj.name : undefined;
        if (arrName) {
          const arrVar: Expr = { kind: "var", name: arrName };
          const letHead: Stmt = { kind: "let", name: s.name, type: s.ty, mutable: s.mutable,
            value: { kind: "index", arr: arrVar, idx: { kind: "num", value: 0 } } };
          const sliceTail: Stmt = { kind: "assign", target: arrName,
            value: { kind: "methodCall", obj: arrVar, objTy: init.fn.obj.ty, method: "slice", args: [{ kind: "num", value: 1 }], monadic: false } };
          return [letHead, sliceTail];
        }
      }
      // let x = arr.pop() → let x: T? = (Option-expr); arr := (truncated-or-self)
      if (init && init.fn.kind === "field" && init.fn.field === "pop" && init.fn.obj.ty.kind === "array") {
        const recv = init.fn.obj;
        if (mutableReceiverRoot(recv)) {
          const binds: Stmt[] = [];
          const arrExpr = lowerExpr(recv, binds);
          const { optValue, guardedTrunc } = buildPopLowering(arrExpr, recv.ty);
          const upd = buildNestedUpdate(recv, guardedTrunc, binds);
          if (upd) {
            return [
              ...binds,
              { kind: "let", name: s.name, type: s.ty, mutable: s.mutable, value: optValue },
              { kind: "assign", target: upd.root, value: upd.value },
            ];
          }
        }
      }
      // new Map(arr.map(n => [n.field, n])) → let m = map[]; for (n of arr) m[n.field] := n
      if (init && init.fn.kind === "var" && init.fn.name === "__mapFromArray" &&
          init.args.length === 1 && init.args[0].kind === "call" &&
          init.args[0].fn.kind === "field" && init.args[0].fn.field === "map" &&
          init.args[0].args.length === 1 && init.args[0].args[0].kind === "lambda") {
        const arrExpr = init.args[0].fn.obj;
        const lam = init.args[0].args[0];
        const param = lam.params[0]?.name ?? "_";
        const lamBody = Array.isArray(lam.body) ? lam.body : [{ kind: "return" as const, value: lam.body }];
        const retStmt = lamBody.find(b => b.kind === "return") as { kind: "return"; value: TExpr } | undefined;
        if (retStmt && retStmt.value.kind === "arrayLiteral" && retStmt.value.elems.length === 2) {
          const keyExpr = retStmt.value.elems[0];
          const valExpr = retStmt.value.elems[1];
          const arrIR = transformExpr(arrExpr);
          const arrTy = arrExpr.ty;
          const elemTy = arrTy.kind === "array" ? arrTy.elem : { kind: "unknown" as const };
          const idxName = freshName(`_${param}_idx`);
          const idx: Expr = { kind: "var", name: idxName };
          const arrSize: Expr = { kind: "field", obj: arrIR, field: "size" };
          const keyIR = transformExpr(keyExpr);
          const valIR = transformExpr(valExpr);
          const mapSet: Expr = { kind: "methodCall", obj: { kind: "var", name: s.name }, objTy: s.ty, method: "set", args: [keyIR, valIR], monadic: false };
          // Auto-invariant: all processed elements' keys are in the map. The
          // quantifier wraps user expressions, so its binder must be fresh.
          const kiName = freshName("ki");
          const kVar: Expr = { kind: "var", name: kiName };
          const mapHasKey: Expr = {
            kind: "implies",
            premises: [
              { kind: "binop", op: "≥", left: kVar, right: { kind: "num", value: 0 } },
              { kind: "binop", op: "<", left: kVar, right: idx },
            ],
            conclusion: { kind: "methodCall", obj: { kind: "var", name: s.name }, objTy: s.ty, method: "has", args: [keyIR.kind === "field" ? { kind: "field", obj: { kind: "index", arr: arrIR, idx: kVar }, field: (keyIR as any).field } : keyIR], monadic: false },
          };
          const autoInv: Expr = { kind: "forall", var: kiName, type: { kind: "int" }, body: mapHasKey };
          const stmts: Stmt[] = [
            { kind: "let", name: s.name, type: s.ty, mutable: true, value: { kind: "emptyMap" } },
            { kind: "forin", idx: idxName, bound: arrSize,
              invariants: [{ kind: "binop", op: "≤", left: idx, right: arrSize }, autoInv],
              body: [
                { kind: "let", name: param, type: elemTy, mutable: false, value: { kind: "index", arr: arrIR, idx } },
                { kind: "assign", target: s.name, value: mapSet },
              ] },
          ];
          return stmts;
        }
      }
      const { binds, expr } = liftMethodCalls(s.init);
      return [...binds, { kind: "let", name: s.name, type: s.ty, mutable: s.mutable, value: expr }];
    }

    case "assign": {
      // x = arr.pop() → x := (Option-expr); arr := (truncated-or-self)
      if (s.value.kind === "call" && s.value.fn.kind === "field" &&
          s.value.fn.field === "pop" && s.value.fn.obj.ty.kind === "array") {
        const recv = s.value.fn.obj;
        if (mutableReceiverRoot(recv)) {
          const binds: Stmt[] = [];
          const arrExpr = lowerExpr(recv, binds);
          const { optValue, guardedTrunc } = buildPopLowering(arrExpr, recv.ty);
          const upd = buildNestedUpdate(recv, guardedTrunc, binds);
          if (upd) {
            return [
              ...binds,
              { kind: "assign", target: s.target, value: optValue },
              { kind: "assign", target: upd.root, value: upd.value },
            ];
          }
        }
      }
      // Top-level method call → direct monadic bind, no lifting needed
      if (s.value.kind === "call" && s.value.callKind === "method")
        return [{ kind: "bind", target: s.target, value: transformExpr(s.value) }];
      const { binds, expr } = liftMethodCalls(s.value);
      return [...binds, { kind: "assign", target: s.target, value: expr }];
    }

    case "return": {
      const { binds, expr } = liftMethodCalls(s.value);
      return [...binds, { kind: "return", value: expr }];
    }
    case "break": return [{ kind: "break" }];
    case "continue": return [{ kind: "continue" }];
    case "expr": {
      // Guard idiom: `cond && effect;` → `if (cond) { effect; }`
      if (s.expr.kind === "binop" && s.expr.op === "&&") {
        return transformStmt({
          kind: "if",
          cond: s.expr.left,
          then: [{ kind: "expr", expr: s.expr.right }],
          else: [],
        }, typeDecls);
      }
      // Standalone `arr.pop();`
      if (s.expr.kind === "call" && s.expr.fn.kind === "field" &&
          s.expr.fn.field === "pop" && s.expr.fn.obj.ty.kind === "array") {
        const recv = s.expr.fn.obj;
        if (mutableReceiverRoot(recv)) {
          const binds: Stmt[] = [];
          const arrExpr = lowerExpr(recv, binds);
          const { guardedTrunc } = buildPopLowering(arrExpr, recv.ty);
          const upd = buildNestedUpdate(recv, guardedTrunc, binds);
          if (upd) return [...binds, { kind: "assign", target: upd.root, value: upd.value }];
        }
      }
      // Mutating collection call: m.set(k, v), s.add(v), arr.push(v), including
      // through narrowed optional/nullish receivers (`a.push(99)`, `b.items.push(99)`).
      if (s.expr.kind === "call" && s.expr.fn.kind === "field") {
        const recv = s.expr.fn.obj;
        const f = s.expr.fn.field;
        const isMutating =
          ((recv.ty.kind === "map" || recv.ty.kind === "set") && (f === "set" || f === "add" || f === "delete")) ||
          (recv.ty.kind === "array" && (f === "push" || f === "unshift" || f === "sort"));
        if (isMutating && mutableReceiverRoot(recv)) {
          const binds: Stmt[] = [];
          const expr = lowerExpr(s.expr, binds);
          const upd = buildNestedUpdate(recv, expr, binds);
          if (upd) return [...binds, { kind: "assign", target: upd.root, value: upd.value }];
        }
      }
      // Optional chaining on map.get at statement level: `m.get(k)?.push(v)`
      // → `if k in m { m := m[k := m[k] + [v]] }`
      if (s.expr.kind === "optChain" &&
          s.expr.obj.kind === "call" && s.expr.obj.fn.kind === "field" &&
          s.expr.obj.fn.field === "get" && s.expr.obj.fn.obj.ty.kind === "map" &&
          s.expr.chain.length === 2 &&
          s.expr.chain[0].kind === "field" && s.expr.chain[0].name === "push" &&
          s.expr.chain[1].kind === "call" && s.expr.chain[1].args.length === 1) {
        const mapExpr = s.expr.obj.fn.obj;
        const mapName = mapExpr.kind === "var" ? mapExpr.name : undefined;
        const keyExpr = lowerExpr(s.expr.obj.args[0], null);
        const pushArg = lowerExpr(s.expr.chain[1].args[0], null);
        if (mapName) {
          const mapVar: Expr = { kind: "var", name: mapName };
          const directGet: Expr = { kind: "methodCall", obj: mapVar, objTy: mapExpr.ty, method: "getDirect", args: [keyExpr], monadic: false };
          const pushed: Expr = { kind: "methodCall", obj: directGet, objTy: (mapExpr.ty as any).value, method: "push", args: [pushArg], monadic: false };
          const updated: Expr = { kind: "methodCall", obj: mapVar, objTy: mapExpr.ty, method: "set", args: [keyExpr, pushed], monadic: false };
          const hasCond: Expr = { kind: "methodCall", obj: mapVar, objTy: mapExpr.ty, method: "has", args: [keyExpr], monadic: false };
          return [{ kind: "if", cond: hasCond, then: [{ kind: "assign", target: mapName, value: updated }], else: [] }];
        }
      }
      const { binds, expr } = liftMethodCalls(s.expr);
      return [...binds, { kind: "assign", target: "_", value: expr }];
    }

    case "if": {
      // Keep pure `if` conditions unlifted when there are no method calls, so
      // Lean `dite` exposes the full condition (`o.isSome && o.get _ ≥ 0`) directly
      // to nested `while` guards/invariants/decreases!
      const condT = asCondition(s.cond);
      let hasMethod = false;
      mapTExpr(condT, x => {
        if (x.kind === "call" && x.callKind === "method" && !(x.builtinId !== undefined && builtinSpec(x.builtinId).pure)) {
          hasMethod = true;
        }
        return null;
      });
      const { binds, expr: cond } = hasMethod
        ? liftMethodCalls(condT)
        : { binds: [] as Stmt[], expr: transformExpr(condT) };
      return [...binds, { kind: "if", cond, then: transformStmts(s.then, typeDecls), else: transformStmts(s.else, typeDecls) }];
    }

    case "while":
      return [{
        kind: "while",
        cond: transformExpr(asCondition(s.cond)),
        invariants: s.invariants.map(transformExpr),
        decreasing: s.decreases ? transformExpr(s.decreases) : null,
        doneWith: s.doneWith ? transformExpr(s.doneWith) : null,
        body: eliminateTopLevelContinue(transformStmts(s.body, typeDecls)),
      }];

    case "throw":
      return [{ kind: "assert", expr: { kind: "bool", value: false } }];

    case "forof":
      throw new Error("forof should be transformed to forin (range loop) in transformStmts");

    case "switch":
      return [emitSwitchStmt(s, typeDecls)];

    case "ghostLet":
      return [{ kind: "ghostLet", name: s.name, type: s.ty, value: transformExpr(s.init) }];

    case "ghostAssign":
      return [{ kind: "ghostAssign", target: s.target, value: transformExpr(s.value) }];

    case "assert":
      return [{ kind: "assert", expr: transformExpr(s.expr), assumed: s.assumed }];

    case "tagMatch":
      return [emitMatchStmt(s.scrutinee, s.typeName, s.cases, s.fallthrough, typeDecls)];
  }
}

// ── Discriminant if-chain detection ──────────────────────────

interface Chain {
  varName: string;
  typeName: string;
  cases: { variant: string; body: TStmt[] }[];
  fallthrough: TStmt[];
}

/** Build match arms from variant cases — shared by imperative and pure paths.
 *  Looks up variant fields from typeDecls, builds patterns via buildMatchPattern,
 *  and delegates body transformation to the caller-provided function.
 *  Returns null if any body transformation returns null (pure path abort). */
function buildMatchArms<T>(
  cases: { name: string; body: TStmt[] }[],
  varName: string | undefined, typeName: string, typeDecls: TypeDeclInfo[],
  transformBody: (body: TStmt[], varName: string | undefined, fields: { name: string; tsType: string }[], ctorName?: string) => T | null
): { pattern: MatchPattern; body: T }[] | null {
  const decl = declOf(typeDecls, typeName);
  if (!decl || (decl.kind !== "string-union" && decl.kind !== "discriminated-union")) {
    throw new Error(`match type ${typeName} is not a declared union`);
  }
  const arms: { pattern: MatchPattern; body: T }[] = [];
  for (const c of cases) {
    const variant = decl?.variants?.find(v => v.name === c.name);
    const declared = decl.kind === "string-union"
      ? decl.values?.includes(c.name)
      : !!variant;
    if (!declared) throw new Error(`case ${JSON.stringify(c.name)} is not a variant of ${typeName}`);
    const fields = variant?.fields ?? [];
    const pattern = buildMatchPattern(c.name, fields, varName);
    const body = transformBody(c.body, varName, fields, c.name);
    if (body === null) return null;
    arms.push({ pattern, body });
  }
  return arms;
}

/** Build value-pattern arms for a switch on a plain string. Case labels have
 *  already been validated and decoded by extraction; unlike datatype cases,
 *  these are literal values and introduce no constructor-field binders. */
function buildLiteralMatchArms<T>(
  cases: { name: string; body: TStmt[] }[],
  transformBody: (body: TStmt[]) => T | null,
): { pattern: MatchPattern; body: T }[] | null {
  const arms: { pattern: MatchPattern; body: T }[] = [];
  for (const c of cases) {
    const body = transformBody(c.body);
    if (body === null) return null;
    arms.push({ pattern: pLiteral(c.name), body });
  }
  return arms;
}

function emitMatchStmt(
  scrutinee: TExpr,
  typeName: string,
  cases: { variant: string; body: TStmt[] }[],
  fallthrough: TStmt[],
  typeDecls: TypeDeclInfo[],
): Stmt {
  const decl = declOf(typeDecls, typeName);
  // Synth array-unions (discriminant "__isArray__") have single-field variants
  // ArrayBranch(arr) / NonArrayBranch(val). The matched arm refers to the
  // scrutinee by its bare name/path (`content`, `m.content`), not `.arr`, so
  // we substitute that whole reference with the variant's sole field binder.
  const isSynthArrayUnion = decl?.discriminant === "__isArray__";
  // The scrutinee is a bare var (`current`) or a field-access path
  // (`current.content`). `prefix` names the binder scope — the var name, or a
  // safe id derived from the path (`current.content` → `current_content`) —
  // and is used for both pattern binders and arm-body substitution so they
  // always agree. A var scrutinee has empty `fields`, so `prefix` is just its
  // name and the emitted code is unchanged from before this generalization.
  const path = asTAccessPath(scrutinee);
  const isPath = !!path && path.fields.length > 0;
  const prefix = path ? [path.rootVar, ...path.fields].join("_") : "?";
  function transformArmBody(body: TStmt[], fields: { name: string; tsType: string; type?: Ty }[]): Stmt[] {
    let stmts: TStmt[];
    if (isPath && path) {
      // Path scrutinee: the matched value is referred to by the bare path, so
      // substitute the whole path (only the synth single-field shape arises
      // here — discriminant chains require a var scrutinee).
      stmts = isSynthArrayUnion && fields.length === 1
        ? replacePathInTStmts(body, path, matchBinder(fields[0].name, prefix), fields[0].type ?? parseTsType(fields[0].tsType))
        : body;
    } else {
      stmts = replaceFieldAccessInTStmts(body, prefix, fields);
      if (isSynthArrayUnion && fields.length === 1) {
        const f = fields[0];
        stmts = replaceVarInTStmts(stmts, prefix, matchBinder(f.name, prefix), f.type ?? parseTsType(f.tsType));
      }
    }
    return transformStmts(stmts, typeDecls);
  }
  const armCases = cases.map(c => ({ name: c.variant, body: c.body }));
  const arms = buildMatchArms(armCases, prefix, typeName, typeDecls,
    (body, _vn, fields) => transformArmBody(body, fields))!;
  // Add the fallthrough arm whenever the listed cases don't cover every
  // variant — needed for exhaustiveness even when there's no `else`
  // (`fallthrough` empty), e.g. `if (Array.isArray(x)) {...}` with no else
  // becomes `match x { case ArrayBranch(..) => ... case NonArrayBranch(..) => }`.
  const allCovered = !!decl?.variants && cases.length >= decl.variants.length;
  if (!allCovered) {
    const remaining = remainingVariant(typeName, cases, typeDecls);
    if (remaining) {
      // Exactly one variant left — destructure so the fallthrough body can
      // access variant-specific fields (Lean requires this; Dafny tolerates `_`).
      const pattern = buildMatchPattern(remaining.name, remaining.fields, prefix);
      const body = transformArmBody(fallthrough, remaining.fields);
      arms.push({ pattern, body });
    } else {
      arms.push({ pattern: pWild(), body: transformStmts(fallthrough, typeDecls) });
    }
  }
  return { kind: "match", scrutinee: isPath ? transformExpr(scrutinee) : varE(prefix), arms };
}

/** Replace bare `var(oldName)` references → `var(newName)` with the given type.
 *  Used by emitMatchStmt for synth array-unions where the variant has a single
 *  payload field and the user code refers to the scrutinee by its bare name. */
function replaceVarInTStmts(stmts: TStmt[], oldName: string, newName: string, newTy: Ty): TStmt[] {
  return stmts.map(s => mapTStmt(s, e => {
    if (e.kind === "var" && e.name === oldName) {
      return { kind: "var", name: newName, ty: newTy } as TExpr;
    }
    return null;
  }));
}

/** If the chain has matched all variants but one, return that remaining variant. */
function remainingVariant(typeName: string, cases: { variant: string }[], typeDecls: TypeDeclInfo[]): { name: string; fields: { name: string; tsType: string; type?: Ty }[] } | null {
  const decl = declOf(typeDecls, typeName);
  if (!decl?.variants) return null;
  const matched = new Set(cases.map(c => c.variant));
  const remaining = decl.variants.filter(v => !matched.has(v.name));
  if (remaining.length !== 1) return null;
  return remaining[0];
}

/** `switch(obj.field)` is stripped at extraction to scrutinee `obj` + discriminant
 *  `field`, assuming `obj` is a discriminated union with `field` as its
 *  discriminant. When that's NOT so — e.g. `obj` is a plain record with an
 *  enum- or string-typed `field` — the switch is really on the field VALUE. This
 *  returns the scrutinee `obj.field` (+ its resolved type) to match directly; null
 *  for a genuine discriminant switch or `switch(localVar)`, which callers handle
 *  their usual way. Shared by emitSwitchStmt and transformPureSwitch. */
function enumFieldSwitch(s: TStmt & { kind: "switch" }, typeDecls: TypeDeclInfo[]): { scrutinee: Expr; fieldTy: Ty | undefined } | null {
  if (!s.discriminant) return null;
  const objDecl = declOfTy(typeDecls, s.expr.ty);
  if (objDecl?.kind === "discriminated-union" && objDecl.discriminant === s.discriminant) return null;
  const fieldTy = objDecl?.kind === "record" ? objDecl.fields?.find(f => f.name === s.discriminant)?.type : undefined;
  return {
    scrutinee: { kind: "field", obj: transformExpr(s.expr), field: s.discriminant },
    fieldTy,
  };
}

/** Declared datatype matched by a switch, excluding records/aliases/opaque
 *  types. A plain `string` intentionally has no declaration and uses literal
 *  patterns instead. */
function switchCtorDecl(typeDecls: TypeDeclInfo[], ty: Ty | undefined): TypeDeclInfo | undefined {
  if (!ty) return undefined;
  const decl = declOfTy(typeDecls, ty);
  return decl?.kind === "string-union" || decl?.kind === "discriminated-union" ? decl : undefined;
}

/** Stamp variant ctor info onto datatype updates of the match scrutinee in
 *  lowered arm bodies (`{ ...vn, f: v }`) — the statement-path twin of
 *  `replaceFieldAccess`'s stamping. Emitters need the pin to use
 *  per-constructor destructor names for collision-renamed fields. */
function stampScrutineeUpdates(body: Stmt[], varName: string, ctorName: string, ctorOf: string): Stmt[] {
  const stamp = (x: Expr): Expr | null => {
    if (x.kind === "record" && !x.ctor && x.spread &&
        x.spread.kind === "var" && x.spread.name === varName) {
      return { ...x, ctor: ctorName, ctorOf,
        fields: x.fields.map(f => ({ ...f, value: mapExpr(f.value, stamp) })) };
    }
    return null;
  };
  return body.map(st => mapStmt(st, stamp));
}

function emitSwitchStmt(s: TStmt & { kind: "switch" }, typeDecls: TypeDeclInfo[]): Stmt {
  const cases = s.cases.map(c => ({ name: c.label, body: c.body }));
  const ef = enumFieldSwitch(s, typeDecls);
  const matchTy = ef ? ef.fieldTy : s.expr.ty;
  const literalCases = matchTy?.kind === "string";
  const ctorDecl = switchCtorDecl(typeDecls, matchTy);
  if (!literalCases && !ctorDecl) {
    const typeName = !matchTy ? "unknown" : matchTy.kind === "user" ? matchTy.name : matchTy.kind;
    throw new Error(`switch scrutinee must be string-typed or a declared union, got ${typeName}`);
  }
  const baseName = s.expr.ty.kind === "user" ? tyBaseName(s.expr.ty.name) : undefined;
  const arms = literalCases
    ? buildLiteralMatchArms(cases, (body) => transformStmts(body, typeDecls))!
    : ef
      ? buildMatchArms(cases, undefined, ctorDecl!.name, typeDecls, (body) => transformStmts(body, typeDecls))!
      : buildMatchArms(cases, s.expr.kind === "var" ? s.expr.name : "?", ctorDecl!.name, typeDecls,
        (body, vn, fields, ctorName) => {
          let out = transformStmts(replaceFieldAccessInTStmts(body, vn!, fields), typeDecls);
          if (ctorName && vn && baseName) out = stampScrutineeUpdates(out, vn, ctorName, baseName);
          return out;
        })!;
  if (s.defaultBody.length > 0) arms.push({ pattern: pWild(), body: transformStmts(s.defaultBody, typeDecls) });
  return { kind: "match", scrutinee: ef ? ef.scrutinee : varE(s.expr.kind === "var" ? s.expr.name : "?"), arms };
}

/** Replace obj.field → replacement var in typed IR.
 *  Uses the TExpr's resolved type when available, falling back to `fallbackTy`. */
function replaceFieldsInTStmts(
  stmts: TStmt[], objName: string,
  replacements: { fieldName: string; newName: string; fallbackTy: Ty }[]
): TStmt[] {
  if (replacements.length === 0) return stmts;
  return stmts.map(s => mapTStmt(s, e => {
    if (e.kind === "field" && e.obj.kind === "var" && e.obj.name === objName) {
      const r = replacements.find(r => r.fieldName === e.field);
      if (r) {
        const ty = e.ty.kind !== "unknown" ? e.ty : r.fallbackTy;
        return { kind: "var", name: r.newName, ty } as TExpr;
      }
    }
    return null;
  }));
}

/** Replace all variant fields of obj → match binder vars in typed IR.
 *  Before replacing field reads, realize TypeScript's structural argument
 *  conversion for calls such as `helper(outcome)` inside a narrowed union arm.
 *  The source value is still the enclosing union in typed IR, while Dafny and
 *  Lean expect the helper's nominal record. Rebuild that record solely from
 *  the fields bound by this arm's match pattern. */
function replaceFieldAccessInTStmts(stmts: TStmt[], varName: string, fields: { name: string; tsType: string; type?: Ty }[]): TStmt[] {
  const projected = projectStructuralCallArgsInTStmts(stmts, varName, fields);
  return replaceFieldsInTStmts(projected, varName, fields.map(f => ({
    fieldName: f.name,
    newName: matchBinder(f.name, varName),
    fallbackTy: f.type ?? parseTsType(f.tsType),
  })));
}

/** Project a narrowed union scrutinee into a named structural record expected
 *  by a same-module/extern call. Resolution stamps named calls with paramTys;
 *  this pass fires only when every target record field has an identically typed
 *  match-bound source field. That deliberately avoids inventing a broad cast:
 *  it is the nominal-backend witness for the structural call TS already accepts. */
function projectStructuralCallArgsInTStmts(
  stmts: TStmt[], varName: string,
  fields: { name: string; tsType: string; type?: Ty }[],
): TStmt[] {
  const sourceFields = fields.map(f => ({
    ...f,
    resolvedTy: f.type ?? parseTsType(f.tsType),
  }));

  return stmts.map(s => mapTStmt(s, e => {
    if (e.kind !== "call" || !e.paramTys) return null;
    const paramTys = e.paramTys;
    let changed = false;
    const args = e.args.map((arg, i) => {
      if (arg.kind !== "var" || arg.name !== varName || i >= paramTys.length) return arg;
      const targetTy = paramTys[i];
      const targetDecl = declOfTy(_typeDecls, targetTy);
      if (targetTy.kind !== "user" || targetDecl?.kind !== "record" || !targetDecl.fields) return arg;

      const matched: { targetField: typeof targetDecl.fields[number]; sourceField: typeof sourceFields[number] }[] = [];
      for (const targetField of targetDecl.fields) {
        const sourceField = sourceFields.find(f => f.name === targetField.name);
        const targetFieldTy = targetField.type ?? parseTsType(targetField.tsType);
        if (!sourceField || !tyEqual(sourceField.resolvedTy, targetFieldTy)) return arg;
        matched.push({ targetField, sourceField });
      }

      changed = true;
      return {
        kind: "record" as const,
        spread: null,
        fields: matched.map(m => ({
          name: m.targetField.name,
          value: {
            kind: "var" as const,
            name: matchBinder(m.sourceField.name, varName),
            ty: m.sourceField.resolvedTy,
          },
        })),
        ty: targetTy,
      };
    });
    return changed ? { ...e, args } : null;
  }));
}

/** A pure access path — chain of field accesses rooted at a var. */
interface AccessPath { rootVar: string; fields: string[] }

function asTAccessPath(e: TExpr): AccessPath | null {
  if (e.kind === "coerce") return asTAccessPath(e.expr);
  if (e.kind === "var") return { rootVar: e.name, fields: [] };
  if (e.kind === "field") {
    const inner = asTAccessPath(e.obj);
    if (!inner) return null;
    return { rootVar: inner.rootVar, fields: [...inner.fields, e.field] };
  }
  return null;
}

/** Does TExpr `e` match the given access path exactly? */
function matchesAccessPath(e: TExpr, path: AccessPath): boolean {
  const candidate = asTAccessPath(e);
  return candidate !== null && candidate.rootVar === path.rootVar &&
    candidate.fields.length === path.fields.length &&
    candidate.fields.every((f, i) => f === path.fields[i]);
}

function replacePathInTStmts(stmts: TStmt[], path: AccessPath, binder: string, binderTy: Ty): TStmt[] {
  return stmts.map(s => mapTStmt(s, e =>
    matchesAccessPath(e, path)
      ? { kind: "var", name: binder, ty: binderTy } as TExpr : null
  ));
}


// ── Pure function generation ─────────────────────────────────

function transformPureBody(stmts: TStmt[], typeDecls: TypeDeclInfo[]): Expr | null {
  // tagMatch (from narrow's discriminant detection) is the leading stmt and consumes the rest.
  if (stmts.length > 0 && stmts[0].kind === "tagMatch") {
    const t = stmts[0];
    const varName = t.scrutinee.kind === "var" ? t.scrutinee.name : "?";
    const chain: Chain = { varName, typeName: t.typeName, cases: t.cases, fallthrough: t.fallthrough };
    return transformPureMatch(chain, typeDecls);
  }

  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    const rest = stmts.slice(i + 1);
    switch (s.kind) {
      case "return": return transformExpr(s.value);
      case "let": {
        const restExpr = transformPureBody(rest, typeDecls);
        if (!restExpr) return null;
        return { kind: "let", name: s.name, value: transformExpr(s.init), body: restExpr };
      }
      case "if": {
        // Append rest to both branches so nested ifs that fall through
        // can reach the continuation (e.g. early return inside then-branch).
        const thenExpr = transformPureBody([...s.then, ...rest], typeDecls);
        if (!thenExpr) return null;
        const elseStmts = s.else.length > 0 ? [...s.else, ...rest] : rest;
        const elseExpr = transformPureBody(elseStmts, typeDecls);
        if (!elseExpr) return null;
        return { kind: "if", cond: transformExpr(asCondition(s.cond)), then: thenExpr, else: elseExpr };
      }
      case "switch": return transformPureSwitch(s, typeDecls);
      default: return null;
    }
  }
  return null;
}

function transformPureSwitch(s: TStmt & { kind: "switch" }, typeDecls: TypeDeclInfo[]): Expr | null {
  const ef = enumFieldSwitch(s, typeDecls);
  if (ef) {
    const cases = s.cases.map(c => ({ name: c.label, body: c.body }));
    const literalCases = ef.fieldTy?.kind === "string";
    const ctorDecl = switchCtorDecl(typeDecls, ef.fieldTy);
    if (!literalCases && !ctorDecl) return null;
    const arms = literalCases
      ? buildLiteralMatchArms(cases, (body) => transformPureBody(body, typeDecls))
      : buildMatchArms(cases, undefined, ctorDecl!.name, typeDecls, (body) => transformPureBody(body, typeDecls));
    if (!arms) return null;
    if (s.defaultBody.length > 0) {
      const body = transformPureBody(s.defaultBody, typeDecls);
      if (!body) return null;
      arms.push({ pattern: pWild(), body });
    }
    return { kind: "match", scrutinee: ef.scrutinee, arms };
  }
  const ctorDecl = switchCtorDecl(typeDecls, s.expr.ty);
  if (!ctorDecl) return null;
  const typeName = ctorDecl.name;
  const varName = s.expr.kind === "var" ? s.expr.name : undefined;
  const cases = s.cases.map(c => ({ name: c.label, body: c.body }));
  const arms = buildMatchArms(cases, varName, typeName, typeDecls,
    (body, vn, fields, ctorName) => {
      const projected = vn ? projectStructuralCallArgsInTStmts(body, vn, fields) : body;
      let result = transformPureBody(projected, typeDecls);
      if (!result) return null;
      if (fields.length > 0 && vn) result = replaceFieldAccess(result, vn, fields, ctorName, tyBaseName(typeName));
      return result;
    });
  if (!arms) return null;
  if (s.defaultBody.length > 0) {
    const body = transformPureBody(s.defaultBody, typeDecls);
    if (!body) return null;
    arms.push({ pattern: pWild(), body });
  }
  if (s.expr.kind !== "var") return null;
  return { kind: "match", scrutinee: varE(s.expr.name), arms };
}

function transformPureMatch(chain: Chain, typeDecls: TypeDeclInfo[]): Expr | null {
  const cases = chain.cases.map(c => ({ name: c.variant, body: c.body }));
  const decl = declOf(typeDecls, chain.typeName);
  // Synth array-unions have single-field variants and user code refers to the
  // scrutinee by its bare name, not field-accessed. See emitMatchStmt for
  // the statement-level counterpart of this substitution.
  const isSynthArrayUnion = decl?.discriminant === "__isArray__";
  const arms = buildMatchArms(cases, chain.varName, chain.typeName, typeDecls,
    (body, vn, fields, ctorName) => {
      const projected = vn ? projectStructuralCallArgsInTStmts(body, vn, fields) : body;
      let result = transformPureBody(projected, typeDecls);
      if (!result) return null;
      if (fields.length > 0 && vn) result = replaceFieldAccess(result, vn, fields, ctorName, tyBaseName(chain.typeName));
      if (isSynthArrayUnion && fields.length === 1 && vn) {
        result = replaceVarInExpr(result, vn, matchBinder(fields[0].name, vn));
      }
      return result;
    });
  if (!arms) return null;
  // Idiomatic TS often has an unreachable fallthrough after exhaustive if-chains on
  // discriminated unions. Skip the catch-all arm when all variants are matched,
  // since Lean errors on redundant match arms.
  const allCovered = decl?.variants && chain.cases.length >= decl.variants.length;
  if (chain.fallthrough.length > 0 && !allCovered) {
    const remaining = remainingVariant(chain.typeName, chain.cases, typeDecls);
    if (remaining) {
      // Exactly one variant left — destructure for variant-specific field access.
      const projected = projectStructuralCallArgsInTStmts(chain.fallthrough, chain.varName, remaining.fields);
      let body = transformPureBody(projected, typeDecls);
      if (!body) return null;
      if (remaining.fields.length > 0) body = replaceFieldAccess(body, chain.varName, remaining.fields, remaining.name, tyBaseName(chain.typeName));
      if (isSynthArrayUnion && remaining.fields.length === 1) {
        body = replaceVarInExpr(body, chain.varName, matchBinder(remaining.fields[0].name, chain.varName));
      }
      arms.push({ pattern: buildMatchPattern(remaining.name, remaining.fields, chain.varName), body });
    } else {
      const body = transformPureBody(chain.fallthrough, typeDecls);
      if (!body) return null;
      arms.push({ pattern: pWild(), body });
    }
  }
  return { kind: "match", scrutinee: varE(chain.varName), arms };
}

// ── Generate type declarations ───────────────────────────────

function transformTypeDecl(d: TypeDeclInfo): Decl {
  if (d.kind === "string-union") {
    return {
      kind: "inductive", name: d.name,
      constructors: d.values!.map(v => ({ name: v, fields: [] })),
      deriving: ["Repr", "Inhabited", "DecidableEq"],
    };
  } else if (d.kind === "discriminated-union") {
    return {
      kind: "inductive", name: d.name,
      typeParams: d.typeParams,
      constructors: d.variants!.map(v => ({
        name: v.name,
        fields: v.fields.map(f => ({ name: f.name, type: f.type! })),
      })),
      deriving: ["Repr", "Inhabited"],
    };
  } else if (d.kind === "alias") {
    return {
      kind: "type-alias", name: d.name,
      target: d.aliasOfTy!,
    };
  } else if (d.kind === "opaque") {
    return { kind: "opaque-type", name: d.name };
  } else {
    return {
      kind: "structure", name: d.name,
      typeParams: d.typeParams,
      fields: d.fields!.map(f => ({ name: f.name, type: f.type! })),
      deriving: ["Repr", "Inhabited", "DecidableEq"],
    };
  }
}

// ── Helpers ──────────────────────────────────────────────────

/** Find parameter names that are reassigned anywhere in the body. */
function findReassignedNames(stmts: TStmt[], names: Set<string>): Set<string> {
  const found = new Set<string>();
  function checkCall(e: TExpr) {
    if (e.kind === "call" && e.fn.kind === "field" &&
        ["add", "set", "delete", "push", "unshift", "sort", "pop", "shift"].includes(e.fn.field)) {
      const root = mutableReceiverRoot(e.fn.obj);
      if (root && names.has(root)) found.add(root);
    }
    if (e.kind === "binop" && e.op === "&&") checkCall(e.right);
  }
  function scan(stmts: TStmt[]) {
    for (const s of stmts) {
      if (s.kind === "assign" && names.has(s.target)) found.add(s.target);
      if (s.kind === "ghostAssign" && names.has(s.target)) found.add(s.target);
      if (s.kind === "let") checkCall(s.init);
      if (s.kind === "assign") checkCall(s.value);
      if (s.kind === "expr") checkCall(s.expr);
      if (s.kind === "if") { scan(s.then); scan(s.else); }
      if (s.kind === "while") scan(s.body);
      if (s.kind === "forof") scan(s.body);
      if (s.kind === "switch") { for (const c of s.cases) scan(c.body); scan(s.defaultBody); }
      if (s.kind === "tagMatch") { for (const c of s.cases) scan(c.body); scan(s.fallthrough); }
    }
  }
  scan(stmts);
  return found;
}

/** Replace all occurrences of a variable name with a new expression. */
/**
 * Replace all occurrences of variable `name` with `replacement`.
 * If `narrowing` is true, the replacement is an unwrapped Optional value
 * (e.g., replacing `x: Option<T>` with `x_val: T`). In that case, when the
 * variable appears directly as a record spread field value, it's wrapped in
 * Some() to preserve the field's Optional type.
 */
function replaceVar(e: Expr, name: string, replacement: Expr, narrowing?: boolean): Expr {
  const rec = (expr: Expr) => replaceVar(expr, name, replacement, narrowing);
  return mapExpr(e, x => {
    if (x.kind === "var" && x.name === name) return replacement;
    // Record spread: wrap direct variable uses in field values with Some when narrowing
    if (narrowing && x.kind === "record" && x.spread) {
      return {
        ...x,
        spread: rec(x.spread),
        fields: x.fields.map(f => {
          if (f.value.kind === "var" && f.value.name === name) {
            return { ...f, value: { kind: "app" as const, fn: "Some", args: [replacement] } };
          }
          return { ...f, value: rec(f.value) };
        }),
      };
    }
    // Don't descend past bindings that shadow the name
    if (x.kind === "forall" && x.var === name) return x;
    if (x.kind === "exists" && x.var === name) return x;
    if (x.kind === "let" && x.name === name) return { ...x, value: replaceVar(x.value, name, replacement, narrowing) };
    return null;
  });
}

// ── Top-level transform ──────────────────────────────────────

/** Transform for Lean backend — same logic, Lean options. */
export function transformModuleLean(mod: TModule, specImport?: string, moduleBase?: string): { typesFile: Module | null; defFile: Module } {
  const prev = _opts;
  _opts = LEAN_OPTIONS;
  try {
    return transformModule(mod, specImport, moduleBase);
  } finally {
    _opts = prev;
  }
}

/** Transform for Dafny backend — same logic, Dafny options. */
export function transformModuleDafny(mod: TModule): { typesFile: Module | null; defFile: Module } {
  const prev = _opts;
  _opts = DAFNY_OPTIONS;
  try {
    return transformModule(mod);
  } finally {
    _opts = prev;
  }
}

export function transformModule(mod: TModule, specImport?: string, moduleBaseOverride?: string): { typesFile: Module | null; defFile: Module } {
  _forofCounters.clear();
  _liftCounter = 0;
  _callbackCounter = 0;
  _branchCounter = 0;
  _typeDecls = mod.typeDecls;
  _neededKindHelpers = new Map();
  _pureDefNames = new Set(mod.functions.filter(f => f.isPure).map(f => f.name));
  const typeDecls = mod.typeDecls.map(transformTypeDecl);

  // Module-level constants
  const constDecls: ConstDecl[] = (mod.constants ?? []).map(c => ({
    kind: "const" as const,
    name: c.name,
    type: c.ty,
    value: transformExpr(c.value),
  }));

  // Pure function mirrors
  const pureDefs: FnDef[] = [];
  const defByMethods: FnDefByMethod[] = [];
  for (const fn of mod.functions) {
    if (!fn.isPure) continue;
    const body = transformPureBody(fn.body, mod.typeDecls);
    if (body) {
      // For pure-function lemmas, replace \result with the function call.
      const fnCall: Expr = { kind: "app", fn: fn.name, args: fn.params.map(p => ({ kind: "var" as const, name: p.name })) };
      const ensures = fn.ensures.map(e => replaceVar(transformExpr(e), "\\result", fnCall));
      pureDefs.push({
        kind: "def",
        name: fn.name,
        typeParams: fn.typeParams,
        params: fn.params.map(p => ({ name: p.name, type: p.ty })),
        returnType: fn.returnTy,
        requires: fn.requires.map(transformExpr),
        ensures,
        decreases: fn.decreases ? transformExpr(fn.decreases) : null,
        body,
      });
    } else if (fn.forcePure) {
      // //@ pure but body can't be auto-converted — emit function by method
      _forofCounters.clear();
      const methodBody = promoteAssignedLets(transformStmts(fn.body, mod.typeDecls));
      defByMethods.push({
        kind: "def-by-method",
        name: fn.name,
        typeParams: fn.typeParams,
        params: fn.params.map(p => ({ name: p.name, type: p.ty })),
        returnType: fn.returnTy,
        requires: fn.requires.map(transformExpr),
        ensures: fn.ensures.map(transformExpr),
        decreases: fn.decreases ? transformExpr(fn.decreases) : null,
        methodBody,
      });
    }
  }

  if (_opts.backend === "lean") {
    // A pure mirror would erase failure on an empty spread or an unguarded `!`
    // assertion that relies on `requires`. Keep these functions and their
    // transitive callers as methods, where Velvet WP checks them.
    const checked = new Set([
      "LemmaScript.maxOfArray", "LemmaScript.minOfArray",
      "LemmaScript.optionValue", "LemmaScript.nullishValue",
      "LemmaScript.nullishExcludeUndefined", "LemmaScript.nullishExcludeNull",
    ]);
    const hasExplicitCheckedCoerce = (stmts: TStmt[]): boolean => {
      let found = false;
      for (const s of stmts) mapTStmt(s, e => { if (e.kind === "coerce" && e.checked) found = true; return null; });
      return found;
    };
    for (const fn of mod.functions) {
      if (fn.isPure && hasExplicitCheckedCoerce(fn.body)) checked.add(fn.name);
    }
    let changed = true;
    while (changed) {
      changed = false;
      for (const def of pureDefs) {
        if (!checked.has(def.name) && anyExpr(def.body, e => {
          const name = e.kind === "app" ? e.fn : e.kind === "var" ? e.name : "";
          return checked.has(name.replace(/^Pure\./, ""));
        })) {
          checked.add(def.name);
          changed = true;
        }
      }
    }
    for (let i = pureDefs.length - 1; i >= 0; i--) {
      if (checked.has(pureDefs[i].name)) {
        _pureDefNames.delete(pureDefs[i].name);
        pureDefs.splice(i, 1);
      }
    }
  }

  const base = mod.file.split("/").pop()?.replace(/\.ts$/, "") ?? "module";
  // Lean module base — overridable via `//@ lean-module` (see lsc.ts). Only the
  // def→types import below reads it; Dafny never passes an override.
  const moduleBase = moduleBaseOverride ?? base;

  // Externs: effectively pure declarations become uninterpreted functions;
  // impure declarations become body-less methods with independent results.
  // Contracts come along in either case. A pure extern's `\result` denotes its
  // application; an impure extern keeps `\result` for the method out-parameter.
  const externDecls: Decl[] = (mod.externs ?? []).map(ext => {
    const fnCall: Expr = { kind: "app", fn: ext.flat, args: ext.params.map(p => ({ kind: "var" as const, name: p.name })) };
    return {
      kind: "extern" as const,
      name: ext.flat,
      typeParams: ext.typeParams,
      params: ext.params.map(p => ({ name: p.name, type: p.ty })),
      returnType: ext.returnTy,
      requires: ext.requires.map(transformExpr),
      ensures: ext.ensures.map(e => ext.impure
        ? transformExpr(e)
        : replaceVar(transformExpr(e), "\\result", fnCall)),
      impure: ext.impure,
    };
  });

  // Def file: Velvet methods
  // Pure functions get a thin wrapper. Lean keeps pure definitions in the
  // `Pure` namespace; Dafny flattens that namespace, so its call is unqualified.
  // def-by-method functions also skip their method wrappers
  const pureDefNames = new Set([...pureDefs.map(d => d.name), ...defByMethods.map(d => d.name)]);
  const methods: FnMethod[] = mod.functions.map(fn => {
    const ensures: Expr[] = [];
    for (const e of fn.ensures) {
      const m = ensuresToMatch(e, mod.typeDecls);
      if (m) ensures.push(m);
      else ensures.push(transformExpr(e));
    }

    _forofCounters.clear();
    let body = pureDefNames.has(fn.name)
      ? [{ kind: "return" as const, value: { kind: "app" as const, fn: _opts.backend === "lean" ? `Pure.${fn.name}` : fn.name, args: fn.params.map(p => ({ kind: "var" as const, name: p.name })) } }]
      : promoteAssignedLets(transformStmts(fn.body, mod.typeDecls));

    // Lean-only method-body rewrites (Velvet can't WP-synthesize monadic matches
    // and forbids `return` in loops):
    //   1. monadic statement-`match` on a user union → discriminator `if`-chains
    //   2. `return` inside a loop → result var + break (postcondition as invariant)
    // Dafny keeps the native forms. Breaking loops (including those synthesized
    // by rewrite 2) must carry a `//@ done_with` in the TS source — enforced here,
    // since loom's default loop-exit fact `¬guard` does not hold across a break.
    if (_opts.backend === "lean" && !pureDefNames.has(fn.name)) {
      body = matchToIfChains(body);
      const resultInvariants = fn.ensures.map(e => replaceVar(transformExpr(e), "\\result", { kind: "var", name: "_loopRet" }));
      body = eliminateReturnInLoops(body, fn.returnTy, resultInvariants);
      requireDoneWithForBreaks(body, fn.name);
    }

    // Shadow reassigned parameters with mutable locals
    const paramNames = new Set(fn.params.map(p => p.name));
    const reassigned = findReassignedNames(fn.body, paramNames);
    if (reassigned.size > 0) {
      const shadows: Stmt[] = fn.params
        .filter(p => reassigned.has(p.name))
        .map(p => ({ kind: "let" as const, name: p.name, type: p.ty, mutable: true, value: { kind: "var" as const, name: p.name } }));
      body = [...shadows, ...body];
    }

    return {
      kind: "method" as const,
      name: fn.name,
      typeParams: fn.typeParams,
      params: fn.params.map(p => ({ name: p.name, type: p.ty })),
      returnType: fn.returnTy,
      requires: fn.requires.map(transformExpr),
      ensures,
      decreases: fn.decreases ? transformExpr(fn.decreases) : null,
      body,
    };
  });

  // Class declarations
  const classDecls: Decl[] = (mod.classes ?? []).map(cls => {
    const classMethods: FnMethod[] = cls.methods.map(fn => {
      const ensures: Expr[] = fn.ensures.map(transformExpr);
      _forofCounters.clear();
      const body = promoteAssignedLets(transformStmts(fn.body, mod.typeDecls));
      return {
        kind: "method" as const,
        name: fn.name,
        typeParams: fn.typeParams,
        params: fn.params.map(p => ({ name: p.name, type: p.ty })),
        returnType: fn.returnTy,
        requires: fn.requires.map(transformExpr),
        ensures,
        decreases: fn.decreases ? transformExpr(fn.decreases) : null,
        body,
      };
    });
    return {
      kind: "class" as const,
      name: cls.name,
      fields: cls.fields.map(f => ({ name: f.name, type: f.ty })),
      methods: classMethods,
    };
  });

  // Types file — assembled after all body transforms, so needs discovered
  // there (discriminator kind-helpers) are included.
  const kindHelpers: Decl[] = [..._neededKindHelpers.values()].map(kindHelperDecl);

  // ── Imported / undeclared user types: opaque by default ─────────────
  // A module may reference types it imports (ir.ts uses typedir's `Ty`).
  // Standalone compilation has no declaration for them; synthesize an
  // opaque type — the value passes through, uninspectable, which is the
  // only sound use of an undeclared type (same doctrine as _synthOpaque).
  // Any attempted inspection still fails loudly: an opaque type has no
  // constructors and no operations. Signature-level coverage (type-decl
  // fields, params, returns, class fields, externs, consts); a body-level
  // reference to an undeclared type still errors in the backend.
  const referenced = new Set<string>();
  const collectTy = (ty: Ty): void => {
    switch (ty.kind) {
      case "user": referenced.add(tyBaseName(ty.name)); return;
      case "array": case "set": collectTy(ty.elem); return;
      case "optional": collectTy(ty.inner); return;
      case "map": collectTy(ty.key); collectTy(ty.value); return;
      case "tuple": ty.elems.forEach(collectTy); return;
      case "fn": ty.params.forEach(collectTy); collectTy(ty.result); return;
      default: return;
    }
  };
  const knownTypeNames = new Set<string>(typeDecls.map(d => (d as { name: string }).name));
  for (const cls of mod.classes ?? []) knownTypeNames.add(cls.name);
  const allTypeParams = new Set<string>();
  // Exclude type params from the *source* decls — the transformed IR drops
  // them for aliases (`type Step<S, A> = …`), and a generic alias's params
  // must not be mistaken for imported types. Params may carry a `//@ type`
  // decoration ("S(==)"); references collect as the bare name, so strip it.
  const addTp = (tp: string): void => { allTypeParams.add(tp.replace(/\(.*$/, "").trim()); };
  for (const d of mod.typeDecls) d.typeParams?.forEach(addTp);
  for (const d of typeDecls) {
    if (d.kind === "inductive") d.constructors.forEach(c => c.fields.forEach(f => collectTy(f.type)));
    else if (d.kind === "structure") d.fields.forEach(f => collectTy(f.type));
    else if (d.kind === "type-alias") collectTy(d.target);
  }
  for (const fn of mod.functions) { fn.typeParams.forEach(addTp); fn.params.forEach(p => collectTy(p.ty)); collectTy(fn.returnTy); }
  for (const cls of mod.classes ?? []) {
    cls.fields.forEach(f => collectTy(f.ty));
    for (const m of cls.methods) { m.typeParams.forEach(addTp); m.params.forEach(p => collectTy(p.ty)); collectTy(m.returnTy); }
  }
  for (const ext of mod.externs ?? []) { ext.typeParams.forEach(addTp); ext.params.forEach(p => collectTy(p.ty)); collectTy(ext.returnTy); }
  for (const c of mod.constants ?? []) collectTy(c.ty);
  const opaqueImports: Decl[] = [...referenced]
    .filter(n => !knownTypeNames.has(n) && !allTypeParams.has(n))
    .map(n => ({ kind: "opaque-type" as const, name: n }));
  const typesImports: string[] = ["LemmaScript"];
  let typesFile: Module | null = null;
  const pureNamespace: Decl[] = pureDefs.length > 0
    ? [{ kind: "namespace", name: "Pure", decls: pureDefs }]
    : [];
  if (typeDecls.length > 0 || pureDefs.length > 0 || externDecls.length > 0 || opaqueImports.length > 0) {
    // Declaration order differs by backend. Dafny allows forward references, so
    // externs go first to be in scope everywhere. Lean requires definition-before-use:
    // an extern's signature may reference a declared type (e.g. `estimateTokens(m: AgentMessage)`),
    // so types must precede externs, which in turn precede the pure mirrors that may call them.
    // Kind-helpers sit right after the datatypes they discriminate.
    const decls = _opts.backend === "lean"
      ? [...opaqueImports, ...typeDecls, ...kindHelpers, ...externDecls, ...pureNamespace]
      : [...externDecls, ...opaqueImports, ...typeDecls, ...kindHelpers, ...pureNamespace];
    typesFile = {
      comment: "  Generated by lsc — Lean types and pure function mirrors.",
      imports: typesImports,
      options: [],
      decls,
    };
  }

  const defImport = specImport ?? (typesFile ? `«${moduleBase}.types»` : null);
  const defBaseImports: string[] = defImport ? [defImport] : ["LemmaScript"];
  const defFile: Module = {
    comment: "  Generated by lsc from " + (mod.file.split("/").pop() ?? "") + "\n  Do not edit — re-run `lsc gen` to regenerate.",
    imports: defBaseImports,
    options: [
      { key: "velvet.semantics.termination", value: '"total"' },
    ],
    decls: [...constDecls, ...defByMethods, ...methods, ...classDecls],
  };

  return { typesFile, defFile };
}
