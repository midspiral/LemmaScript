/**
 * Resolve — Raw IR → Typed IR.
 *
 * Resolves types, classifies calls, identifies discriminants,
 * parses //@ annotations, rejects unsupported patterns.
 */

import type { RawExpr, RawStmt, RawFunction, RawModule } from "./rawir.js";
import type { Ty, TExpr, TStmt, TFunction, TModule, TParam, CallKind } from "./typedir.js";
import type { TypeDeclInfo } from "./types.js";
import { parseExpr } from "./specparser.js";

// ── Resolution context ───────────────────────────────────────

interface Ctx {
  /** Variable name → resolved type */
  vars: Map<string, Ty>;
  /** Type declarations from the module */
  typeDecls: TypeDeclInfo[];
  /** //@ type overrides */
  overrides: Map<string, string>;
  /** Whether \result is allowed (only in ensures) */
  allowResult: boolean;
  /** Return type (for \result) */
  returnTy: Ty;
}

// ── TS type string → Ty ─────────────────────────────────────

function resolveTsType(tsType: string, overrides: Map<string, string>, varName?: string): Ty {
  // Check override first
  if (varName) {
    const o = overrides.get(varName);
    if (o === "nat") return { kind: "nat" };
    if (o) return { kind: "user", name: o };
  }

  const t = tsType.trim();
  if (t === "number") return { kind: "int" };
  if (t === "boolean") return { kind: "bool" };
  if (t === "string") return { kind: "string" };
  if (t === "void" || t === "undefined") return { kind: "void" };

  // Array types
  if (t === "number[]") return { kind: "array", elem: { kind: "int" } };
  if (t === "boolean[]") return { kind: "array", elem: { kind: "bool" } };
  if (t === "string[]") return { kind: "array", elem: { kind: "string" } };
  const arrMatch = t.match(/^(?:Array<(.+)>|(.+)\[\])$/);
  if (arrMatch) return { kind: "array", elem: resolveTsType(arrMatch[1] || arrMatch[2], overrides) };

  // User-defined
  return { kind: "user", name: t };
}

function isNatTy(ty: Ty): boolean { return ty.kind === "nat"; }
function isArrayTy(ty: Ty): boolean { return ty.kind === "array"; }
function isUserTy(ty: Ty): boolean { return ty.kind === "user"; }

// ── Find type declaration info ───────────────────────────────

function findDecl(ctx: Ctx, name: string): TypeDeclInfo | undefined {
  return ctx.typeDecls.find(d => d.name === name);
}

function getDiscriminant(ctx: Ctx, typeName: string): string | undefined {
  const decl = findDecl(ctx, typeName);
  return decl?.discriminant;
}

function isNullaryVariant(ctx: Ctx, typeName: string, variantName: string): boolean {
  const decl = findDecl(ctx, typeName);
  const variant = decl?.variants?.find(v => v.name === variantName);
  return variant ? variant.fields.length === 0 : true;
}

// ── Classify calls ───────────────────────────────────────────

function classifyCall(fn: RawExpr, ctx: Ctx): CallKind {
  // Math.floor, Math.abs etc. are builtins → pure
  if (fn.kind === "field" && fn.obj.kind === "var" && fn.obj.name === "Math") return "pure";
  // If the callee is a known function name, check if it appears in the module
  // For now, assume all user function calls are method calls (monadic in Velvet)
  if (fn.kind === "var") return "method";
  return "unknown";
}

// ── Resolve expressions ──────────────────────────────────────

function resolveExpr(e: RawExpr, ctx: Ctx): TExpr {
  switch (e.kind) {
    case "var": {
      const ty = ctx.vars.get(e.name) ?? { kind: "unknown" as const };
      return { kind: "var", name: e.name, ty };
    }

    case "num":
      return { kind: "num", value: e.value, ty: e.value >= 0 ? { kind: "nat" } : { kind: "int" } };

    case "str":
      return { kind: "str", value: e.value, ty: { kind: "string" } };

    case "bool":
      return { kind: "bool", value: e.value, ty: { kind: "bool" } };

    case "binop": {
      const left = resolveExpr(e.left, ctx);
      const right = resolveExpr(e.right, ctx);
      // Result type depends on operator
      let ty: Ty = { kind: "unknown" };
      if (["===", "!==", ">=", "<=", ">", "<", "&&", "||"].includes(e.op)) ty = { kind: "bool" };
      else if (["+", "-", "*", "/", "%"].includes(e.op)) ty = left.ty;
      return { kind: "binop", op: e.op, left, right, ty };
    }

    case "unop": {
      const expr = resolveExpr(e.expr, ctx);
      const ty: Ty = e.op === "!" ? { kind: "bool" } : expr.ty;
      return { kind: "unop", op: e.op, expr, ty };
    }

    case "call": {
      const fn = resolveExpr(e.fn, ctx);
      const args = e.args.map(a => resolveExpr(a, ctx));
      const callKind = classifyCall(e.fn, ctx);
      // Return type: unknown for now (could look up function signatures)
      return { kind: "call", fn, args, ty: { kind: "unknown" }, callKind };
    }

    case "index": {
      const obj = resolveExpr(e.obj, ctx);
      const idx = resolveExpr(e.idx, ctx);
      const elemTy: Ty = obj.ty.kind === "array" ? obj.ty.elem : { kind: "unknown" };
      return { kind: "index", obj, idx, ty: elemTy };
    }

    case "field": {
      const obj = resolveExpr(e.obj, ctx);
      let isDiscriminant = false;
      let ty: Ty = { kind: "unknown" };

      // arr.length → Nat
      if (e.field === "length" && isArrayTy(obj.ty)) {
        ty = { kind: "nat" };
      }
      // x.field on a user type → check if discriminant
      else if (obj.ty.kind === "user") {
        const disc = getDiscriminant(ctx, obj.ty.name);
        if (disc === e.field) isDiscriminant = true;
        const decl = findDecl(ctx, obj.ty.name);
        if (decl?.kind === "record") {
          const f = decl.fields?.find(f => f.name === e.field);
          if (f) ty = resolveTsType(f.tsType, ctx.overrides);
        }
      }

      return { kind: "field", obj, field: e.field, ty, isDiscriminant };
    }

    case "record": {
      const fields = e.fields.map(f => ({ name: f.name, value: resolveExpr(f.value, ctx) }));
      return { kind: "record", fields, ty: { kind: "unknown" } };
    }

    // Spec-only nodes (from specparser):
    case "result":
      if (!ctx.allowResult) throw new Error("\\result is only valid in ensures");
      return { kind: "result", ty: ctx.returnTy };

    case "forall": {
      const varTy: Ty = e.varType === "nat" ? { kind: "nat" } : { kind: "int" };
      const innerCtx = { ...ctx, vars: new Map(ctx.vars).set(e.var, varTy) };
      return { kind: "forall", var: e.var, varTy, body: resolveExpr(e.body, innerCtx), ty: { kind: "bool" } };
    }

    case "exists": {
      const varTy: Ty = e.varType === "nat" ? { kind: "nat" } : { kind: "int" };
      const innerCtx = { ...ctx, vars: new Map(ctx.vars).set(e.var, varTy) };
      return { kind: "exists", var: e.var, varTy, body: resolveExpr(e.body, innerCtx), ty: { kind: "bool" } };
    }
  }
}

// ── Resolve spec annotations (strings → TExpr) ──────────────

function resolveSpec(spec: string, ctx: Ctx): TExpr {
  const raw = parseExpr(spec);
  return resolveExpr(raw, ctx);
}

function resolveSpecs(specs: string[], ctx: Ctx): TExpr[] {
  // Split top-level && into separate clauses
  const result: TExpr[] = [];
  for (const spec of specs) {
    const raw = parseExpr(spec);
    for (const clause of splitConj(raw)) {
      result.push(resolveExpr(clause, ctx));
    }
  }
  return result;
}

function splitConj(e: RawExpr): RawExpr[] {
  if (e.kind === "binop" && e.op === "&&") return [...splitConj(e.left), ...splitConj(e.right)];
  return [e];
}

// ── Resolve statements ───────────────────────────────────────

function resolveStmts(stmts: RawStmt[], ctx: Ctx): TStmt[] {
  const result: TStmt[] = [];
  for (const s of stmts) {
    result.push(resolveStmt(s, ctx));
  }
  return result;
}

function resolveStmt(s: RawStmt, ctx: Ctx): TStmt {
  switch (s.kind) {
    case "let": {
      const ty = resolveTsType(s.tsType, ctx.overrides, s.name);
      ctx.vars.set(s.name, ty);
      return { kind: "let", name: s.name, ty, mutable: s.mutable, init: resolveExpr(s.init, ctx) };
    }

    case "assign":
      return { kind: "assign", target: s.target, value: resolveExpr(s.value, ctx) };

    case "return":
      return { kind: "return", value: resolveExpr(s.value, ctx) };

    case "break":
      return { kind: "break" };

    case "expr":
      return { kind: "expr", expr: resolveExpr(s.expr, ctx) };

    case "if":
      return {
        kind: "if",
        cond: resolveExpr(s.cond, ctx),
        then: resolveStmts(s.then, ctx),
        else: resolveStmts(s.else, ctx),
      };

    case "while": {
      const bodyCtx = { ...ctx, vars: new Map(ctx.vars) };
      return {
        kind: "while",
        cond: resolveExpr(s.cond, bodyCtx),
        invariants: resolveSpecs(s.invariants, bodyCtx),
        decreases: s.decreases ? resolveSpec(s.decreases, bodyCtx) : null,
        doneWith: s.doneWith ? resolveSpec(s.doneWith, bodyCtx) : null,
        body: resolveStmts(s.body, bodyCtx),
      };
    }

    case "switch":
      return {
        kind: "switch",
        expr: resolveExpr(s.expr, ctx),
        discriminant: s.discriminant,
        cases: s.cases.map(c => ({ label: c.label, body: resolveStmts(c.body, ctx) })),
        defaultBody: resolveStmts(s.defaultBody, ctx),
      };
  }
}

// ── Pure function detection ──────────────────────────────────

function isPure(stmts: RawStmt[]): boolean {
  for (const s of stmts) {
    switch (s.kind) {
      case "while": return false;
      case "let": if (s.mutable) return false; break;
      case "if": if (!isPure(s.then) || !isPure(s.else)) return false; break;
      case "switch": if (!s.cases.every(c => isPure(c.body)) || !isPure(s.defaultBody)) return false; break;
    }
  }
  return true;
}

// ── Return-in-loop detection ─────────────────────────────────

function hasReturnInLoop(stmts: RawStmt[]): boolean {
  for (const s of stmts) {
    if (s.kind === "while" && containsReturn(s.body)) return true;
    if (s.kind === "if" && (hasReturnInLoop(s.then) || hasReturnInLoop(s.else))) return true;
    if (s.kind === "switch" && (s.cases.some(c => hasReturnInLoop(c.body)) || hasReturnInLoop(s.defaultBody))) return true;
  }
  return false;
}

function containsReturn(stmts: RawStmt[]): boolean {
  for (const s of stmts) {
    if (s.kind === "return") return true;
    if (s.kind === "if" && (containsReturn(s.then) || containsReturn(s.else))) return true;
    if (s.kind === "while" && containsReturn(s.body)) return true;
    if (s.kind === "switch" && (s.cases.some(c => containsReturn(c.body)) || containsReturn(s.defaultBody))) return true;
  }
  return false;
}

// ── Resolve function ─────────────────────────────────────────

function resolveFunction(fn: RawFunction, typeDecls: TypeDeclInfo[]): TFunction {
  if (hasReturnInLoop(fn.body)) {
    throw new Error(`${fn.name}: return inside a loop is not supported. Restructure to use break + result variable.`);
  }

  const overrides = new Map(fn.typeAnnotations.map(a => [a.name, a.type]));

  const params: TParam[] = fn.params.map(p => ({
    name: p.name,
    ty: resolveTsType(p.tsType, overrides, p.name),
  }));

  const returnTy = resolveTsType(fn.returnType, overrides, "\\result");

  // Build variable context from params
  const vars = new Map<string, Ty>();
  for (const p of params) vars.set(p.name, p.ty);

  const baseCtx: Ctx = { vars, typeDecls, overrides, allowResult: false, returnTy };
  const ensuresCtx: Ctx = { ...baseCtx, allowResult: true };

  return {
    name: fn.name,
    params,
    returnTy,
    requires: resolveSpecs(fn.requires, baseCtx),
    ensures: resolveSpecs(fn.ensures, ensuresCtx),
    isPure: isPure(fn.body),
    body: resolveStmts(fn.body, baseCtx),
  };
}

// ── Resolve module ───────────────────────────────────────────

export function resolveModule(raw: RawModule): TModule {
  return {
    file: raw.file,
    typeDecls: raw.typeDecls,
    functions: raw.functions.map(fn => resolveFunction(fn, raw.typeDecls)),
  };
}
