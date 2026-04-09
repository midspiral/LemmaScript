/**
 * Transform — Typed IR → Backend IR.
 *
 * Consumes resolved types and classifications.
 * No type lookups, no string parsing, no re-inference.
 */

import type { TExpr, TStmt, TFunction, TModule, Ty } from "./typedir.js";
import type { Expr, Stmt, Decl, Module, FnDef, FnMethod, MatchArm, StmtMatchArm } from "./ir.js";
import type { TypeDeclInfo } from "./types.js";
import { parseTsType } from "./types.js";

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
    case "var": case "num": case "bool": case "str": case "constructor": case "emptyMap": case "emptySet": return e;
    case "binop": return { ...e, left: r(e.left), right: r(e.right) };
    case "unop": return { ...e, expr: r(e.expr) };
    case "implies": return { ...e, premises: e.premises.map(r), conclusion: r(e.conclusion) };
    case "app": return { ...e, args: e.args.map(r) };
    case "field": return { ...e, obj: r(e.obj) };
    case "toNat": return { ...e, expr: r(e.expr) };
    case "index": return { ...e, arr: r(e.arr), idx: r(e.idx) };
    case "record": return { ...e, spread: e.spread ? r(e.spread) : null, fields: e.fields.map(fi => ({ ...fi, value: r(fi.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(r) };
    case "if": return { ...e, cond: r(e.cond), then: r(e.then), else: r(e.else) };
    case "match": return { ...e, arms: e.arms.map(a => ({ ...a, body: r(a.body) })) };
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
    case "match": return { ...s, arms: s.arms.map(a => ({ ...a, body: a.body.map(t => mapStmt(t, f)) })) };
    case "while": return { ...s, cond: r(s.cond), invariants: s.invariants.map(r), body: s.body.map(t => mapStmt(t, f)) };
    case "forin": return { ...s, bound: r(s.bound), invariants: s.invariants.map(r), body: s.body.map(t => mapStmt(t, f)) };
    case "ghostLet": return { ...s, value: r(s.value) };
    case "ghostAssign": return { ...s, value: r(s.value) };
    case "assert": return { ...s, expr: r(s.expr) };
  }
}

function mapStmts(stmts: Stmt[], f: (e: Expr) => Expr | null): Stmt[] {
  return stmts.map(s => mapStmt(s, f));
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
let _opts: TransformOptions = LEAN_OPTIONS;

/** Prefix match-bound field names to avoid capturing user variables. */
function matchBinder(fieldName: string): string {
  return `_${fieldName}`;
}

const _forofCounters = new Map<string, number>();
function isNat(ty: Ty): boolean { return ty.kind === "nat"; }
function isArray(ty: Ty): boolean { return ty.kind === "array"; }
function isUser(ty: Ty): boolean { return ty.kind === "user"; }

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
  "==": "=", "!=": "≠",
};

/** Bool-valued operators (for code-level conditions needing Decidable). */
const BOOL_OP_MAP: Record<string, string> = {
  ...OP_MAP, "===": "==", "!==": "!=",
};

function transformExpr(e: TExpr): Expr { return lowerExpr(e, null); }

/**
 * Lower a typed expression to Backend IR.
 *
 * When `binds` is non-null, embedded method calls are extracted into
 * `let ← ` binds (monadic lifting / selective ANF).  Lifting propagates
 * through binop, unop, and call arguments — the expression kinds where
 * a method call can appear inline in TS.  It does NOT propagate into
 * field, index, record, forall, or exists sub-expressions.
 */
function lowerExpr(e: TExpr, binds: Stmt[] | null): Expr {
  // Monadic lifting: extract embedded method calls to let-binds
  // Pass binds through to args so nested method calls are also lifted
  if (binds && e.kind === "call" && e.callKind === "method") {
    const name = `_t${_liftCounter++}`;
    const fn = e.fn.kind === "var" ? e.fn.name : `${lowerExpr(e.fn, binds)}`;
    const args = e.args.map(a => lowerExpr(a, binds));
    binds.push({ kind: "let-bind", name, value: { kind: "app", fn, args } });
    return { kind: "var", name };
  }

  switch (e.kind) {
    case "var": return { kind: "var", name: e.name };
    case "num": return { kind: "num", value: e.value };
    case "bool": return { kind: "bool", value: e.value };
    case "result": return { kind: "var", name: "res" };

    case "str":
      if (e.ty.kind === "user") return { kind: "constructor", name: e.value, type: e.ty.name };
      return { kind: "str", value: e.value };

    case "unop":
      if (e.op === "-" && e.expr.kind === "num")
        return { kind: "num", value: -e.expr.value };
      // String truthiness: !str → str == ""
      if (e.op === "!" && e.expr.ty.kind === "string")
        return { kind: "binop", op: "=", left: lowerExpr(e.expr, binds), right: { kind: "str", value: "" } };
      return { kind: "unop", op: e.op === "!" ? "¬" : e.op, expr: lowerExpr(e.expr, binds) };

    case "binop": {
      // Implication: flatten (A && B) ==> C → implies [A, B] C
      // Spec-only — no lifting through premises/conclusion.
      if (e.op === "==>") {
        const { premises, conclusion } = flattenImpl(e);
        return { kind: "implies", premises: premises.map(transformExpr), conclusion: transformExpr(conclusion) };
      }
      // Discriminant check: x.discriminant === "foo" → x = .foo (before generic string literal comparison)
      if ((e.op === "===" || e.op === "!==") && e.left.kind === "field" && e.left.isDiscriminant && e.right.kind === "str") {
        const objTy = e.left.obj.ty.kind === "user" ? e.left.obj.ty.name : undefined;
        return {
          kind: "binop",
          op: e.op === "===" ? "=" : "≠",
          left: transformExpr(e.left.obj),
          right: { kind: "constructor", name: e.right.value, type: objTy },
        };
      }
      // String literal comparison — constructor if user type, string literal if string
      if ((e.op === "===" || e.op === "!==") && e.right.kind === "str") {
        const left = lowerExpr(e.left, binds);
        const leftTy = e.left.ty.kind === "user" ? e.left.ty.name : undefined;
        const right: Expr = isUser(e.left.ty)
          ? { kind: "constructor", name: e.right.value, type: leftTy }
          : { kind: "str", value: e.right.value };
        return { kind: "binop", op: e.op === "===" ? "=" : "≠", left, right };
      }
      // Optional comparison: optExpr op val → match optExpr { Some(v) => v op val, None => false/true }
      if (["===", "!==", ">=", "<=", ">", "<"].includes(e.op) &&
          (e.left.ty.kind === "optional") !== (e.right.ty.kind === "optional")) {
        const [optSide, valSide] = e.left.ty.kind === "optional" ? [e.left, e.right] : [e.right, e.left];
        const optExpr = lowerExpr(optSide, binds);
        const valExpr = lowerExpr(valSide, binds);
        const cmpOp = BOOL_OP_MAP[e.op] ?? e.op;
        const noneVal = e.op === "!==" ? true : false;
        const bound = matchBinder("value");
        return {
          kind: "match", scrutinee: optExpr,
          arms: [
            { pattern: `.some ${bound}`, body: { kind: "binop", op: cmpOp, left: { kind: "var", name: bound }, right: valExpr } },
            { pattern: ".none", body: { kind: "bool", value: noneVal } },
          ],
        };
      }
      return {
        kind: "binop",
        op: OP_MAP[e.op] ?? e.op,
        left: lowerExpr(e.left, binds),
        right: lowerExpr(e.right, binds),
      };
    }

    case "field":
      if (e.field === "length" && isArray(e.obj.ty))
        return { kind: "field", obj: transformExpr(e.obj), field: "size" };
      if (e.field === "length" && e.obj.ty.kind === "string")
        return { kind: "field", obj: transformExpr(e.obj), field: "length" };
      if (e.field === "size" && (e.obj.ty.kind === "map" || e.obj.ty.kind === "set"))
        return { kind: "field", obj: transformExpr(e.obj), field: "collectionSize" };
      return { kind: "field", obj: transformExpr(e.obj), field: e.field };

    case "index": {
      const idx = transformExpr(e.idx);
      const wrappedIdx = isArray(e.obj.ty) && !isNat(e.idx.ty) ? { kind: "toNat" as const, expr: idx } : idx;
      return { kind: "index", arr: transformExpr(e.obj), idx: wrappedIdx };
    }

    case "call": {
      // Math.floor(a / b): Lean int div floors (erase), Dafny truncates (emit JSFloorDiv)
      if (e.fn.kind === "field" && e.fn.field === "floor" && e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1) {
        const arg = e.args[0];
        if (_opts.backend === "dafny" && arg.kind === "binop" && arg.op === "/")
          return { kind: "app", fn: "JSFloorDiv", args: [lowerExpr(arg.left, binds), lowerExpr(arg.right, binds)] };
        return lowerExpr(arg, binds);
      }
      // Method call: receiver.method(args) → methodCall node
      if (e.fn.kind === "field") {
        const recv = lowerExpr(e.fn.obj, binds);
        let method = e.fn.field;
        const args = e.args.map((a, i) => {
          const lowered = lowerExpr(a, binds);
          // arr.with index (first arg) needs .toNat when Int-typed
          if (e.fn.kind === "field" && e.fn.field === "with" && e.fn.obj.ty.kind === "array" && i === 0 && !isNat(a.ty))
            return { kind: "toNat" as const, expr: lowered };
          return lowered;
        });
        // Spec-context map get: result type is non-optional → direct access
        if (method === "get" && e.fn.obj.ty.kind === "map" && e.ty.kind !== "optional") {
          method = "getDirect";
        }
        // Check if any lambda arg has monadic body
        const needsMonadic = _opts.monadic && args.some(a => a.kind === "lambda" && isMonadicBody(a.body));
        const result: Expr = { kind: "methodCall", obj: recv, objTy: e.fn.obj.ty, method, args, monadic: needsMonadic };
        // Monadic HOF call is itself monadic — lift via binds like a method call
        if (_opts.monadic && needsMonadic && binds) {
          const name = `_t${_liftCounter++}`;
          binds.push({ kind: "let-bind", name, value: result });
          return { kind: "var", name };
        }
        return result;
      }
      if (e.fn.kind !== "var")
        throw new Error(`Unsupported call expression: ${e.fn.kind}`);
      const prefix = e.callKind === "spec-pure" && _opts.backend === "lean" ? "Pure." : "";
      return { kind: "app", fn: prefix + e.fn.name, args: e.args.map(a => lowerExpr(a, binds)) };
    }

    case "record":
      return { kind: "record", spread: e.spread ? lowerExpr(e.spread, binds) : null, fields: e.fields.map(f => ({ name: f.name, value: lowerExpr(f.value, binds) })) };

    case "arrayLiteral":
      if (e.ty.kind === "map" && e.elems.length === 0) return { kind: "emptyMap" };
      if (e.ty.kind === "set" && e.elems.length === 0) return { kind: "emptySet" };
      return { kind: "arrayLiteral", elems: e.elems.map(el => lowerExpr(el, binds)) };

    case "lambda":
      return { kind: "lambda", params: e.params.map(p => ({ name: p.name, type: p.ty })), body: transformStmts(e.body, []) };

    case "forall":
      return { kind: "forall", var: e.var, type: e.varTy, body: transformExpr(e.body) };

    case "exists":
      return { kind: "exists", var: e.var, type: e.varTy, body: transformExpr(e.body) };

    case "conditional":
      return { kind: "if", cond: lowerExpr(e.cond, binds), then: lowerExpr(e.then, binds), else: lowerExpr(e.else, binds) };
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
  const decl = typeDecls.find(d => d.name === typeName && d.kind === "discriminated-union");
  if (!decl) return null;

  const variantName = e.left.right.value;
  const variant = decl.variants?.find(v => v.name === variantName);
  if (!variant) return null;

  const fields = variant.fields;
  const pattern = fields.length > 0 ? `.${variantName} ${fields.map(f => matchBinder(f.name)).join(" ")}` : `.${variantName}`;

  let rhs = transformExpr(e.right);
  rhs = replaceFieldAccess(rhs, obj.name, fields);

  return { kind: "match", scrutinee: obj.name, arms: [{ pattern, body: rhs }, { pattern: "_", body: { kind: "bool", value: true } }] };
}

function replaceFieldAccess(e: Expr, varName: string, fields: { name: string; tsType: string }[]): Expr {
  return mapExpr(e, x => {
    if (x.kind === "field" && x.obj.kind === "var" && x.obj.name === varName) {
      const f = fields.find(f => f.name === x.field);
      if (f) return { kind: "var", name: matchBinder(f.name) };
    }
    // If this let shadows the matched variable, stop replacing in the body
    if (x.kind === "let" && x.name === varName) return { ...x, value: replaceFieldAccess(x.value, varName, fields) };
    return null;
  });
}

// ── Transform statements ─────────────────────────────────────

function transformStmts(stmts: TStmt[], typeDecls: TypeDeclInfo[]): Stmt[] {
  const result: Stmt[] = [];
  let i = 0;
  while (i < stmts.length) {
    const s = stmts[i];
    // Detect discriminant if-chain → match
    if (s.kind === "if") {
      const chain = detectDiscriminantChain(stmts.slice(i));
      if (chain) {
        result.push(emitMatchStmt(chain.chain, typeDecls));
        i += chain.consumed;
        continue;
      }
      // Detect optional check → match on Some/None
      const opt = parseOptionalCheck(s.cond);
      if (opt) {
        result.push(emitOptionalMatch(opt.varName, opt.negated, s, typeDecls));
        i++;
        continue;
      }
    }
    // Transform for-of → for-in over range
    if (s.kind === "forof") {
      let iterExpr = transformExpr(s.iterable);
      // Sets aren't indexable — bind SetToSeq to a variable for iteration
      if (s.iterable.ty.kind === "set") {
        const seqName = `_${s.varName}_seq`;
        const convExpr: Expr = { kind: "app", fn: "SetToSeq", args: [iterExpr] };
        const elemTy: Ty = s.varTy.kind !== "unknown" ? s.varTy : { kind: "string" };
        result.push({ kind: "let", name: seqName, type: { kind: "array", elem: elemTy }, mutable: false, value: convExpr });
        iterExpr = { kind: "var", name: seqName };
      }
      const count = _forofCounters.get(s.varName) ?? 0;
      _forofCounters.set(s.varName, count + 1);
      const suffix = count === 0 ? "" : `${count + 1}`;
      const idxName = `_${s.varName}_idx${suffix}`;
      const idx: Expr = { kind: "var", name: idxName };
      const arrSize: Expr = { kind: "field", obj: iterExpr, field: "size" };
      const bodyStmts = transformStmts(s.body, typeDecls);
      const letElem: Stmt = { kind: "let", name: s.varName, type: s.varTy, mutable: false, value: { kind: "index", arr: iterExpr, idx } };
      // Auto-add bound invariant: idx ≤ bound (always true for range loops)
      const boundInv: Expr = { kind: "binop", op: "≤", left: idx, right: arrSize };
      result.push({
        kind: "forin",
        idx: idxName,
        bound: arrSize,
        invariants: [boundInv, ...s.invariants.map(transformExpr)],
        body: [letElem, ...bodyStmts],
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

function liftMethodCalls(e: TExpr): { binds: Stmt[]; expr: Expr } {
  const binds: Stmt[] = [];
  return { binds, expr: lowerExpr(e, binds) };
}

// ── Transform statements ─────────────────────────────────────

function transformStmt(s: TStmt, typeDecls: TypeDeclInfo[]): Stmt[] {
  switch (s.kind) {
    case "let": {
      const { binds, expr } = liftMethodCalls(s.init);
      return [...binds, { kind: "let", name: s.name, type: s.ty, mutable: s.mutable, value: expr }];
    }

    case "assign": {
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
      // Mutating collection call: m.set(k, v) → m := m.set(k, v)
      // Same for s.add(x) on sets
      if (s.expr.kind === "call" && s.expr.fn.kind === "field" &&
          s.expr.fn.obj.kind === "var" &&
          (s.expr.fn.obj.ty.kind === "map" || s.expr.fn.obj.ty.kind === "set") &&
          (s.expr.fn.field === "set" || s.expr.fn.field === "add")) {
        const receiver = s.expr.fn.obj.name;
        const { binds, expr } = liftMethodCalls(s.expr);
        return [...binds, { kind: "assign", target: receiver, value: expr }];
      }
      const { binds, expr } = liftMethodCalls(s.expr);
      return [...binds, { kind: "assign", target: "_", value: expr }];
    }

    case "if": {
      // Lift from condition only (Lean rule: don't lift from branches)
      const { binds, expr: cond } = liftMethodCalls(s.cond);
      return [...binds, { kind: "if", cond, then: transformStmts(s.then, typeDecls), else: transformStmts(s.else, typeDecls) }];
    }

    case "while":
      return [{
        kind: "while",
        cond: transformExpr(s.cond),
        invariants: s.invariants.map(transformExpr),
        decreasing: s.decreases ? transformExpr(s.decreases) : null,
        doneWith: s.doneWith ? transformExpr(s.doneWith) : null,
        body: transformStmts(s.body, typeDecls),
      }];

    case "forof":
      throw new Error("forof should be transformed to forin (range loop) in transformStmts");

    case "switch":
      return [emitSwitchStmt(s, typeDecls)];

    case "ghostLet":
      return [{ kind: "ghostLet", name: s.name, type: s.ty, value: transformExpr(s.init) }];

    case "ghostAssign":
      return [{ kind: "ghostAssign", target: s.target, value: transformExpr(s.value) }];

    case "assert":
      return [{ kind: "assert", expr: transformExpr(s.expr) }];
  }
}

// ── Discriminant if-chain detection ──────────────────────────

interface Chain {
  varName: string;
  typeName: string;
  cases: { variant: string; body: TStmt[] }[];
  fallthrough: TStmt[];
}

function detectDiscriminantChain(stmts: TStmt[]): { chain: Chain; consumed: number } | null {
  if (stmts.length === 0 || stmts[0].kind !== "if") return null;

  const first = parseDiscriminantCond(stmts[0].cond);
  if (!first) return null;

  const cases: { variant: string; body: TStmt[] }[] = [];

  // Follow else branches within one if-else-if tree
  function collectElse(s: TStmt & { kind: "if" }): TStmt[] {
    const p = parseDiscriminantCond(s.cond);
    if (!p || p.varName !== first!.varName) return [s];
    cases.push({ variant: p.variant, body: s.then });
    if (s.else.length === 0) return [];
    if (s.else.length === 1 && s.else[0].kind === "if") return collectElse(s.else[0]);
    return s.else;
  }

  // Walk consecutive top-level ifs on the same discriminant
  let consumed = 0;
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    if (s.kind !== "if") break;
    const p = parseDiscriminantCond(s.cond);
    if (!p || p.varName !== first.varName) break;
    cases.push({ variant: p.variant, body: s.then });
    consumed = i + 1;
    if (s.else.length > 0) {
      const ft = (s.else.length === 1 && s.else[0].kind === "if") ? collectElse(s.else[0]) : s.else;
      return cases.length > 0 ? { chain: { ...first, cases, fallthrough: ft }, consumed } : null;
    }
  }

  if (cases.length === 0) return null;
  return { chain: { ...first, cases, fallthrough: stmts.slice(consumed) }, consumed: stmts.length };
}

function parseDiscriminantCond(cond: TExpr): { varName: string; typeName: string; variant: string } | null {
  // Pattern: x.discriminant === "variant"
  if (cond.kind !== "binop" || cond.op !== "===" || cond.right.kind !== "str") return null;
  if (cond.left.kind !== "field" || !cond.left.isDiscriminant) return null;
  if (cond.left.obj.kind !== "var" || cond.left.obj.ty.kind !== "user") return null;
  return { varName: cond.left.obj.name, typeName: cond.left.obj.ty.name, variant: cond.right.value };
}

function emitOptionalMatch(varName: string, negated: boolean, s: TStmt & { kind: "if" }, typeDecls: TypeDeclInfo[]): Stmt {
  const someBranch = negated ? s.else : s.then;
  const noneBranch = negated ? s.then : s.else;
  const bound = matchBinder(`${varName}_val`);
  const someBody = transformStmts(someBranch, typeDecls);
  const r = (e: Expr): Expr => replaceVar(e, varName, { kind: "var", name: bound });
  const someReplaced = someBody.map(stmt => mapStmtExprs(stmt, r));
  const arms: StmtMatchArm[] = [
    { pattern: `.some ${bound}`, body: someReplaced },
    { pattern: ".none", body: noneBranch.length > 0 ? transformStmts(noneBranch, typeDecls) : [] },
  ];
  return { kind: "match", scrutinee: varName, arms };
}

/** Apply an expression transform to all expressions in a statement (convenience wrapper). */
function mapStmtExprs(s: Stmt, r: (e: Expr) => Expr): Stmt {
  return mapStmt(s, e => r(e));
}

/** Detect `v !== undefined` or `undefined !== v` where v has optional type. */
function parseOptionalCheck(cond: TExpr): { varName: string; negated: boolean } | null {
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) return null;
  let varExpr: TExpr | null = null;
  if (cond.right.kind === "var" && cond.right.name === "undefined") varExpr = cond.left;
  if (cond.left.kind === "var" && cond.left.name === "undefined") varExpr = cond.right;
  if (!varExpr || varExpr.kind !== "var" || varExpr.ty.kind !== "optional") return null;
  return { varName: varExpr.name, negated: cond.op === "===" };
}

function emitMatchStmt(chain: Chain, typeDecls: TypeDeclInfo[]): Stmt {
  const decl = typeDecls.find(d => d.name === chain.typeName);
  const arms: StmtMatchArm[] = chain.cases.map(c => {
    const variant = decl?.variants?.find(v => v.name === c.variant);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.variant} ${fields.map(f => matchBinder(f.name)).join(" ")}` : `.${c.variant}`;
    let body = transformStmts(c.body, typeDecls);
    body = replaceFieldAccessInStmts(body, chain.varName, fields);
    return { pattern, body };
  });
  if (chain.fallthrough.length > 0) arms.push({ pattern: "_", body: transformStmts(chain.fallthrough, typeDecls) });
  return { kind: "match", scrutinee: chain.varName, arms };
}

function emitSwitchStmt(s: TStmt & { kind: "switch" }, typeDecls: TypeDeclInfo[]): Stmt {
  const varName = s.expr.kind === "var" ? s.expr.name : "?";
  const typeName = s.expr.ty.kind === "user" ? s.expr.ty.name : undefined;
  const decl = typeName ? typeDecls.find(d => d.name === typeName) : undefined;
  const arms: StmtMatchArm[] = s.cases.map(c => {
    const variant = decl?.variants?.find(v => v.name === c.label);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.label} ${fields.map(f => matchBinder(f.name)).join(" ")}` : `.${c.label}`;
    let body = transformStmts(c.body, typeDecls);
    body = replaceFieldAccessInStmts(body, varName, fields);
    return { pattern, body };
  });
  if (s.defaultBody.length > 0) arms.push({ pattern: "_", body: transformStmts(s.defaultBody, typeDecls) });
  return { kind: "match", scrutinee: varName, arms };
}

function replaceFieldAccessInStmts(stmts: Stmt[], varName: string, fields: { name: string; tsType: string }[]): Stmt[] {
  if (fields.length === 0) return stmts;
  const f = (e: Expr): Expr | null => {
    if (e.kind === "field" && e.obj.kind === "var" && e.obj.name === varName) {
      const fi = fields.find(fi => fi.name === e.field);
      if (fi) return { kind: "var", name: matchBinder(fi.name) };
    }
    return null;
  };
  const result: Stmt[] = [];
  for (const s of stmts) {
    // If a let shadows the matched variable, stop replacing from here on
    if (s.kind === "let" && s.name === varName) {
      result.push({ ...s, value: mapExpr(s.value, f) });
      result.push(...stmts.slice(result.length));
      break;
    }
    result.push(mapStmt(s, f));
  }
  return result;
}

// ── Pure function generation ─────────────────────────────────

function transformPureBody(stmts: TStmt[], typeDecls: TypeDeclInfo[]): Expr | null {
  // Detect discriminant if-chain
  if (stmts.length > 0 && stmts[0].kind === "if") {
    const chain = detectDiscriminantChain(stmts);
    if (chain) return transformPureMatch(chain.chain, typeDecls);
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
        const thenExpr = transformPureBody(s.then, typeDecls);
        if (!thenExpr) return null;
        const elseBranch = s.else.length > 0 ? s.else : rest;
        const elseExpr = transformPureBody(elseBranch, typeDecls);
        if (!elseExpr) return null;
        return { kind: "if", cond: transformExpr(s.cond), then: thenExpr, else: elseExpr };
      }
      case "switch": return transformPureSwitch(s, typeDecls);
      default: return null;
    }
  }
  return null;
}

function transformPureSwitch(s: TStmt & { kind: "switch" }, typeDecls: TypeDeclInfo[]): Expr | null {
  const decl = typeDecls.find(d => d.name === (s.expr.ty.kind === "user" ? s.expr.ty.name : ""));
  if (!decl) return null;
  const arms: MatchArm[] = [];
  for (const c of s.cases) {
    const variant = decl.variants?.find(v => v.name === c.label);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.label} ${fields.map(f => matchBinder(f.name)).join(" ")}` : `.${c.label}`;
    let body = transformPureBody(c.body, typeDecls);
    if (!body) return null;
    if (fields.length > 0 && s.expr.kind === "var") body = replaceFieldAccess(body, s.expr.name, fields);
    arms.push({ pattern, body });
  }
  if (s.defaultBody.length > 0) {
    const body = transformPureBody(s.defaultBody, typeDecls);
    if (!body) return null;
    arms.push({ pattern: "_", body });
  }
  if (s.expr.kind !== "var") return null;
  return { kind: "match", scrutinee: s.expr.name, arms };
}

function transformPureMatch(chain: Chain, typeDecls: TypeDeclInfo[]): Expr | null {
  const decl = typeDecls.find(d => d.name === chain.typeName);
  const arms: MatchArm[] = [];
  for (const c of chain.cases) {
    const variant = decl?.variants?.find(v => v.name === c.variant);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.variant} ${fields.map(f => matchBinder(f.name)).join(" ")}` : `.${c.variant}`;
    let body = transformPureBody(c.body, typeDecls);
    if (!body) return null;
    if (fields.length > 0) body = replaceFieldAccess(body, chain.varName, fields);
    arms.push({ pattern, body });
  }
  // Idiomatic TS often has an unreachable fallthrough after exhaustive if-chains on
  // discriminated unions. Skip the catch-all arm when all variants are matched,
  // since Lean errors on redundant match arms.
  const allCovered = decl?.variants && chain.cases.length >= decl.variants.length;
  if (chain.fallthrough.length > 0 && !allCovered) {
    const body = transformPureBody(chain.fallthrough, typeDecls);
    if (!body) return null;
    arms.push({ pattern: "_", body });
  }
  return { kind: "match", scrutinee: chain.varName, arms };
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
      constructors: d.variants!.map(v => ({
        name: v.name,
        fields: v.fields.map(f => ({ name: f.name, type: parseTsType(f.tsType) })),
      })),
      deriving: ["Repr", "Inhabited"],
    };
  } else {
    return {
      kind: "structure", name: d.name,
      fields: d.fields!.map(f => ({ name: f.name, type: parseTsType(f.tsType) })),
      deriving: ["Repr", "Inhabited", "DecidableEq"],
    };
  }
}

// ── Helpers ──────────────────────────────────────────────────

/** Find parameter names that are reassigned anywhere in the body. */
function findReassignedNames(stmts: TStmt[], names: Set<string>): Set<string> {
  const found = new Set<string>();
  function scan(stmts: TStmt[]) {
    for (const s of stmts) {
      if (s.kind === "assign" && names.has(s.target)) found.add(s.target);
      if (s.kind === "ghostAssign" && names.has(s.target)) found.add(s.target);
      if (s.kind === "if") { scan(s.then); scan(s.else); }
      if (s.kind === "while") scan(s.body);
      if (s.kind === "forof") scan(s.body);
      if (s.kind === "switch") { for (const c of s.cases) scan(c.body); scan(s.defaultBody); }
    }
  }
  scan(stmts);
  return found;
}

/** Replace all occurrences of a variable name with a new expression. */
function replaceVar(e: Expr, name: string, replacement: Expr): Expr {
  return mapExpr(e, x => {
    if (x.kind === "var" && x.name === name) return replacement;
    // Don't descend past bindings that shadow the name
    if (x.kind === "forall" && x.var === name) return x;
    if (x.kind === "exists" && x.var === name) return x;
    if (x.kind === "let" && x.name === name) return { ...x, value: replaceVar(x.value, name, replacement) };
    return null;
  });
}

// ── Top-level transform ──────────────────────────────────────

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

export function transformModule(mod: TModule, specImport?: string): { typesFile: Module | null; defFile: Module } {
  _forofCounters.clear();
  const typeDecls = mod.typeDecls.map(transformTypeDecl);

  // Pure function mirrors
  const pureDefs: FnDef[] = [];
  for (const fn of mod.functions) {
    if (!fn.isPure) continue;
    const body = transformPureBody(fn.body, mod.typeDecls);
    if (!body) continue;
    // For ensures, replace \result (→ "res") with the function call
    const fnCall: Expr = { kind: "app", fn: fn.name, args: fn.params.map(p => ({ kind: "var" as const, name: p.name })) };
    const ensures = fn.ensures.map(e => replaceVar(transformExpr(e), "res", fnCall));
    pureDefs.push({
      kind: "def",
      name: fn.name,
      params: fn.params.map(p => ({ name: p.name, type: p.ty })),
      returnType: fn.returnTy,
      requires: fn.requires.map(transformExpr),
      ensures,
      body,
    });
  }

  const base = mod.file.split("/").pop()?.replace(/\.ts$/, "") ?? "module";

  // Types file
  const typesImports: string[] = ["LemmaScript"];
  let typesFile: Module | null = null;
  const pureNamespace: Decl[] = pureDefs.length > 0
    ? [{ kind: "namespace", name: "Pure", decls: pureDefs }]
    : [];
  if (typeDecls.length > 0 || pureDefs.length > 0) {
    typesFile = {
      comment: "  Generated by lsc — Lean types and pure function mirrors.",
      imports: typesImports,
      options: [],
      decls: [...typeDecls, ...pureNamespace],
    };
  }

  // Def file: Velvet methods
  // Pure functions get a thin wrapper that calls Pure.fnName
  const pureDefNames = new Set(pureDefs.map(d => d.name));
  const methods: FnMethod[] = mod.functions.map(fn => {
    const ensures: Expr[] = [];
    for (const e of fn.ensures) {
      const m = ensuresToMatch(e, mod.typeDecls);
      if (m) ensures.push(m);
      else ensures.push(transformExpr(e));
    }

    _forofCounters.clear();
    let body = pureDefNames.has(fn.name)
      ? [{ kind: "return" as const, value: { kind: "app" as const, fn: `Pure.${fn.name}`, args: fn.params.map(p => ({ kind: "var" as const, name: p.name })) } }]
      : transformStmts(fn.body, mod.typeDecls);

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
      params: fn.params.map(p => ({ name: p.name, type: p.ty })),
      returnType: fn.returnTy,
      requires: fn.requires.map(transformExpr),
      ensures,
      body,
    };
  });

  const defImport = specImport ?? (typesFile ? `«${base}.types»` : null);
  const defBaseImports: string[] = defImport ? [defImport] : ["LemmaScript"];
  const defFile: Module = {
    comment: "  Generated by lsc from " + (mod.file.split("/").pop() ?? "") + "\n  Do not edit — re-run `lsc gen` to regenerate.",
    imports: defBaseImports,
    options: [
      { key: "loom.semantics.termination", value: '"total"' },
      { key: "loom.semantics.choice", value: '"demonic"' },
    ],
    decls: methods,
  };

  return { typesFile, defFile };
}
