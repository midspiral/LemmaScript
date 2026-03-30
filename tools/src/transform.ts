/**
 * Transform — raw IR → Lean IR.
 *
 * All intelligence lives here: type resolution, discriminant detection,
 * spec expression translation, pure function extraction.
 */

import type { ModuleSpec, FunctionSpec, StmtSpec, IfSpec, SwitchSpec, LetSpec } from "./extract.js";
import type { LeanExpr, LeanStmt, LeanDecl, LeanFile, LeanDef, LeanMethod, LeanMatchArm, LeanStmtMatchArm } from "./ir.js";
import type { TypeDeclInfo, VariantInfo } from "./types.js";
import { tsTypeToLean } from "./types.js";
import { parseExpr, type Expr, type EmitContext } from "./specparser.js";

// ── Context ──────────────────────────────────────────────────

interface TransformCtx {
  arrayVars: Set<string>;
  natVars: Set<string>;
  userTypes: Map<string, string>;  // var name → Lean type name
  typeDecls: TypeDeclInfo[];
  resultVar?: string;              // set to "res" in ensures context
}

function makeCtx(fn: FunctionSpec, typeDecls: TypeDeclInfo[]): TransformCtx {
  const arrayVars = new Set<string>();
  const userTypes = new Map<string, string>();
  for (const p of fn.params) {
    const lt = tsTypeToLean(p.type);
    if (lt.startsWith("Array ")) arrayVars.add(p.name);
    if (!isPrimitive(p.type)) userTypes.set(p.name, lt);
  }
  if (!isPrimitive(fn.returnType)) userTypes.set("\\result", tsTypeToLean(fn.returnType));
  const natVars = new Set(fn.typeAnnotations.filter(t => t.type === "nat").map(t => t.name));
  return { arrayVars, natVars, userTypes, typeDecls };
}

function isPrimitive(t: string): boolean {
  return ["number", "boolean", "string", "void", "undefined"].includes(t.trim());
}

function resolveType(name: string, tsType: string, annotations: { name: string; type: string }[]): string {
  const o = annotations.find(a => a.name === name);
  if (o) return o.type === "nat" ? "Nat" : o.type;
  return tsTypeToLean(tsType);
}

// ── Spec expression → LeanExpr ──────────────────────────────

function isNatExpr(e: Expr, ctx: TransformCtx): boolean {
  switch (e.kind) {
    case "num": return e.value >= 0;
    case "var": return ctx.natVars.has(e.name);
    case "prop": return e.prop === "length" && e.obj.kind === "var" && ctx.arrayVars.has(e.obj.name);
    case "binop": return ["+", "-", "*", "/", "%"].includes(e.op) && isNatExpr(e.left, ctx) && isNatExpr(e.right, ctx);
    default: return false;
  }
}

const OP_MAP: Record<string, string> = {
  "===": "=", "!==": "≠", ">=": "≥", "<=": "≤", ">": ">", "<": "<",
  "&&": "∧", "||": "∨", "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
};

function transformSpecExpr(e: Expr, ctx: TransformCtx): LeanExpr {
  switch (e.kind) {
    case "num": return { kind: "num", value: e.value };
    case "bool": return { kind: "bool", value: e.value };
    case "var": return { kind: "var", name: e.name };
    case "str": return { kind: "constructor", name: e.value };
    case "result":
      if (!ctx.resultVar) throw new Error("\\result is only valid in ensures");
      return { kind: "var", name: ctx.resultVar };

    case "unop":
      if (e.op === "-" && e.expr.kind === "num")
        return { kind: "num", value: -e.expr.value };
      return { kind: "unop", op: e.op === "!" ? "¬" : e.op, expr: transformSpecExpr(e.expr, ctx) };

    case "binop": {
      // Implication: flatten (A && B) ==> C → implies [A, B] C
      if (e.op === "==>") {
        const { premises, conclusion } = flattenImpl(e);
        return {
          kind: "implies",
          premises: premises.map(p => transformSpecExpr(p, ctx)),
          conclusion: transformSpecExpr(conclusion, ctx),
        };
      }
      // String literal comparison: x === "foo" → x = .foo (for user-defined types)
      if ((e.op === "===" || e.op === "!==") && e.right.kind === "str") {
        const left = transformSpecExpr(e.left, ctx);
        const right: LeanExpr = { kind: "constructor", name: e.right.value };
        return { kind: "binop", op: e.op === "===" ? "=" : "≠", left, right };
      }
      // Discriminant check: x.tag === "foo" → x = .foo (for data-free) or handled by match
      if ((e.op === "===" || e.op === "!==") && e.left.kind === "prop" && e.right.kind === "str") {
        const varName = e.left.obj.kind === "var" ? e.left.obj.name : undefined;
        const typeName = varName ? ctx.userTypes.get(varName) : undefined;
        const decl = typeName ? ctx.typeDecls.find(d => d.name === typeName) : undefined;
        if (decl && decl.discriminant === e.left.prop) {
          const left = transformSpecExpr(e.left.obj, ctx);
          const right: LeanExpr = { kind: "constructor", name: e.right.value };
          return { kind: "binop", op: e.op === "===" ? "=" : "≠", left, right };
        }
      }
      return {
        kind: "binop",
        op: OP_MAP[e.op] ?? e.op,
        left: transformSpecExpr(e.left, ctx),
        right: transformSpecExpr(e.right, ctx),
      };
    }

    case "prop":
      if (e.prop === "length" && e.obj.kind === "var" && ctx.arrayVars.has(e.obj.name))
        return { kind: "field", obj: transformSpecExpr(e.obj, ctx), field: "size" };
      return { kind: "field", obj: transformSpecExpr(e.obj, ctx), field: e.prop };

    case "index":
      if (e.obj.kind === "var" && ctx.arrayVars.has(e.obj.name))
        return { kind: "index", arr: transformSpecExpr(e.obj, ctx), idx: transformSpecExpr(e.idx, ctx), toNat: !isNatExpr(e.idx, ctx) };
      return { kind: "index", arr: transformSpecExpr(e.obj, ctx), idx: transformSpecExpr(e.idx, ctx), toNat: false };

    case "call":
      // Math.floor(x) → x
      if (e.fn.kind === "prop" && e.fn.prop === "floor" && e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1)
        return transformSpecExpr(e.args[0], ctx);
      return { kind: "app", fn: e.fn.kind === "var" ? e.fn.name : "?", args: e.args.map(a => transformSpecExpr(a, ctx)) };

    case "record":
      return { kind: "record", fields: e.fields.map(f => ({ name: f.name, value: transformSpecExpr(f.value, ctx) })) };

    case "forall": {
      const ty = e.varType === "nat" ? "Nat" : "Int";
      const bodyCtx = e.varType === "nat" ? { ...ctx, natVars: new Set([...ctx.natVars, e.var]) } : ctx;
      return { kind: "forall", var: e.var, type: ty, body: transformSpecExpr(e.body, bodyCtx) };
    }
    case "exists": {
      const ty = e.varType === "nat" ? "Nat" : "Int";
      const bodyCtx = e.varType === "nat" ? { ...ctx, natVars: new Set([...ctx.natVars, e.var]) } : ctx;
      return { kind: "exists", var: e.var, type: ty, body: transformSpecExpr(e.body, bodyCtx) };
    }
  }
}

function flattenImpl(e: Expr): { premises: Expr[]; conclusion: Expr } {
  if (e.kind === "binop" && e.op === "==>") {
    const lhs = splitConj(e.left);
    const rest = flattenImpl(e.right);
    return { premises: [...lhs, ...rest.premises], conclusion: rest.conclusion };
  }
  return { premises: [], conclusion: e };
}

function splitConj(e: Expr): Expr[] {
  if (e.kind === "binop" && e.op === "&&") return [...splitConj(e.left), ...splitConj(e.right)];
  return [e];
}

/** Parse a spec string and split top-level && into separate LeanExprs. */
function specToClauses(spec: string, ctx: TransformCtx): LeanExpr[] {
  return splitConj(parseExpr(spec)).map(e => transformSpecExpr(e, ctx));
}

/** Parse a single spec string to LeanExpr. */
function specToExpr(spec: string, ctx: TransformCtx): LeanExpr {
  return transformSpecExpr(parseExpr(spec), ctx);
}

// ── Ensures-to-match for discriminated unions ────────────────

function ensuresToMatch(spec: string, ctx: TransformCtx): LeanExpr | null {
  const ast = parseExpr(spec);
  if (ast.kind !== "binop" || ast.op !== "==>") return null;
  if (ast.left.kind !== "binop" || ast.left.op !== "===") return null;
  const lhsLeft = ast.left.left;
  const lhsRight = ast.left.right;
  if (lhsLeft.kind !== "prop" || lhsRight.kind !== "str") return null;
  const varExpr = lhsLeft.obj;
  if (varExpr.kind !== "var") return null;
  const typeName = ctx.userTypes.get(varExpr.name);
  if (!typeName) return null;
  const decl = ctx.typeDecls.find(d => d.name === typeName && d.kind === "discriminated-union" && d.discriminant === lhsLeft.prop);
  if (!decl) return null;
  const variant = decl.variants?.find(v => v.name === lhsRight.value);
  if (!variant) return null;

  const fields = variant.fields;
  const pattern = fields.length > 0 ? `.${variant.name} ${fields.map(f => f.name).join(" ")}` : `.${variant.name}`;

  // Transform the RHS, replacing field accesses on the matched variable
  let rhs = transformSpecExpr(ast.right, ctx);
  rhs = replaceFieldAccess(rhs, varExpr.name, fields);

  return {
    kind: "match", scrutinee: varExpr.name,
    arms: [{ pattern, body: rhs }, { pattern: "_", body: { kind: "bool", value: true } }],
  };
}

function replaceFieldAccess(e: LeanExpr, varName: string, fields: { name: string; tsType: string }[]): LeanExpr {
  if (e.kind === "field" && e.obj.kind === "var" && e.obj.name === varName) {
    const f = fields.find(f => f.name === e.field);
    if (f) return { kind: "var", name: f.name };
  }
  // Recurse
  switch (e.kind) {
    case "binop": return { ...e, left: replaceFieldAccess(e.left, varName, fields), right: replaceFieldAccess(e.right, varName, fields) };
    case "unop": return { ...e, expr: replaceFieldAccess(e.expr, varName, fields) };
    case "implies": return { ...e, premises: e.premises.map(p => replaceFieldAccess(p, varName, fields)), conclusion: replaceFieldAccess(e.conclusion, varName, fields) };
    case "forall": return { ...e, body: replaceFieldAccess(e.body, varName, fields) };
    case "exists": return { ...e, body: replaceFieldAccess(e.body, varName, fields) };
    default: return e;
  }
}

// ── Body statements → LeanStmt ──────────────────────────────

function transformStmts(stmts: StmtSpec[], ctx: TransformCtx, fn: FunctionSpec): LeanStmt[] {
  const result: LeanStmt[] = [];
  let i = 0;
  while (i < stmts.length) {
    const s = stmts[i];

    // Detect discriminant if-chain → match
    if (s.kind === "if") {
      const chain = detectDiscriminantChain(stmts.slice(i), ctx);
      if (chain) {
        result.push(emitMatchStmt(chain.chain, ctx, fn));
        i += chain.consumed;
        continue;
      }
    }

    result.push(transformStmt(s, ctx, fn));
    i++;
  }
  return result;
}

function transformStmt(s: StmtSpec, ctx: TransformCtx, fn: FunctionSpec): LeanStmt {
  switch (s.kind) {
    case "let": {
      const nat = ctx.natVars.has(s.name);
      const ty = nat ? "Nat" : tsTypeToLean(s.type);
      if (!isPrimitive(s.type)) ctx.userTypes.set(s.name, tsTypeToLean(s.type));
      return { kind: "let", name: s.name, type: ty, mutable: s.mutable, value: specToExpr(s.init, ctx) };
    }
    case "assign": {
      const value = specToExpr(s.value, ctx);
      if (isMethodCall(s.value)) return { kind: "bind", target: s.target, value };
      return { kind: "assign", target: s.target, value };
    }
    case "return": return { kind: "return", value: specToExpr(s.value, ctx) };
    case "break": return { kind: "break" };
    case "expr": return { kind: "assign", target: "_", value: specToExpr(s.text, ctx) };

    case "if": {
      const cond = specToExpr(s.condition, ctx);
      return { kind: "if", cond, then: transformStmts(s.then, ctx, fn), else: transformStmts(s.else, ctx, fn) };
    }

    case "switch": return emitSwitchStmt(s, ctx, fn);

    case "while": {
      const bodyCtx = ctx; // same context
      const invariants: LeanExpr[] = [];
      for (const inv of s.invariants) invariants.push(...specToClauses(inv, bodyCtx));
      return {
        kind: "while",
        cond: specToExpr(s.condition, bodyCtx),
        invariants,
        decreasing: s.decreases ? specToExpr(s.decreases, bodyCtx) : null,
        doneWith: s.doneWith ? specToExpr(s.doneWith, bodyCtx) : null,
        body: transformStmts(s.body, bodyCtx, fn),
      };
    }
  }
}

function isMethodCall(value: string): boolean {
  return /^\w+\(.*\)$/.test(value.trim());
}

// ── Discriminant if-chain detection ──────────────────────────

interface Chain { varName: string; typeName: string; cases: { variant: string; body: StmtSpec[] }[]; fallthrough: StmtSpec[] }

function detectDiscriminantChain(stmts: StmtSpec[], ctx: TransformCtx): { chain: Chain; consumed: number } | null {
  if (stmts.length === 0 || stmts[0].kind !== "if") return null;
  const first = parseCondition(stmts[0].condition, ctx);
  if (!first) return null;

  const cases: { variant: string; body: StmtSpec[] }[] = [];
  let consumed = 0;

  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    if (s.kind !== "if") break;
    const p = parseCondition(s.condition, ctx);
    if (!p || p.varName !== first.varName) break;
    cases.push({ variant: p.literal, body: s.then });
    consumed = i + 1;
    if (s.else.length > 0) {
      if (s.else.length === 1 && s.else[0].kind === "if") {
        const ep = parseCondition((s.else[0] as IfSpec).condition, ctx);
        if (ep && ep.varName === first.varName) {
          cases.push({ variant: ep.literal, body: (s.else[0] as IfSpec).then });
          if ((s.else[0] as IfSpec).else.length > 0)
            return { chain: { varName: first.varName, typeName: first.typeName, cases, fallthrough: (s.else[0] as IfSpec).else }, consumed };
        }
      }
      return { chain: { varName: first.varName, typeName: first.typeName, cases, fallthrough: s.else }, consumed };
    }
  }
  const fallthrough = stmts.slice(consumed);
  return cases.length > 0 ? { chain: { varName: first.varName, typeName: first.typeName, cases, fallthrough }, consumed: stmts.length } : null;
}

function parseCondition(cond: string, ctx: TransformCtx): { varName: string; literal: string; typeName: string } | null {
  const m = cond.match(/^(\w+)\.(\w+)\s*===\s*"(\w+)"$/);
  if (m) {
    const [, varName, field, literal] = m;
    const typeName = ctx.userTypes.get(varName);
    if (!typeName) return null;
    const decl = ctx.typeDecls.find(d => d.name === typeName && d.kind === "discriminated-union" && d.discriminant === field);
    if (decl) return { varName, literal, typeName };
  }
  return null; // string unions stay as if
}

function emitMatchStmt(chain: Chain, ctx: TransformCtx, fn: FunctionSpec): LeanStmt {
  const decl = ctx.typeDecls.find(d => d.name === chain.typeName);
  const arms: LeanStmtMatchArm[] = chain.cases.map(c => {
    const variant = decl?.variants?.find(v => v.name === c.variant);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.variant} ${fields.map(f => f.name).join(" ")}` : `.${c.variant}`;
    let body = transformStmts(c.body, ctx, fn);
    body = replaceFieldAccessInStmts(body, chain.varName, fields);
    return { pattern, body };
  });
  if (chain.fallthrough.length > 0) arms.push({ pattern: "_", body: transformStmts(chain.fallthrough, ctx, fn) });
  return { kind: "match", scrutinee: chain.varName, arms };
}

function emitSwitchStmt(s: SwitchSpec, ctx: TransformCtx, fn: FunctionSpec): LeanStmt {
  const typeName = ctx.userTypes.get(s.expr);
  const decl = typeName ? ctx.typeDecls.find(d => d.name === typeName) : undefined;
  const arms: LeanStmtMatchArm[] = s.cases.map(c => {
    const variant = decl?.variants?.find(v => v.name === c.label);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.label} ${fields.map(f => f.name).join(" ")}` : `.${c.label}`;
    let body = transformStmts(c.body, ctx, fn);
    body = replaceFieldAccessInStmts(body, s.expr, fields);
    return { pattern, body };
  });
  if (s.defaultBody.length > 0) arms.push({ pattern: "_", body: transformStmts(s.defaultBody, ctx, fn) });
  return { kind: "match", scrutinee: s.expr, arms };
}

function replaceFieldAccessInStmts(stmts: LeanStmt[], varName: string, fields: { name: string; tsType: string }[]): LeanStmt[] {
  if (fields.length === 0) return stmts;
  return stmts.map(s => replaceFieldAccessInStmt(s, varName, fields));
}

function replaceFieldAccessInStmt(s: LeanStmt, varName: string, fields: { name: string; tsType: string }[]): LeanStmt {
  const r = (e: LeanExpr) => replaceFieldAccess(e, varName, fields);
  switch (s.kind) {
    case "let": return { ...s, value: r(s.value) };
    case "assign": return { ...s, value: r(s.value) };
    case "bind": return { ...s, value: r(s.value) };
    case "return": return { ...s, value: r(s.value) };
    case "break": return s;
    case "if": return { ...s, cond: r(s.cond), then: replaceFieldAccessInStmts(s.then, varName, fields), else: replaceFieldAccessInStmts(s.else, varName, fields) };
    case "match": return { ...s, arms: s.arms.map(a => ({ ...a, body: replaceFieldAccessInStmts(a.body, varName, fields) })) };
    case "while": return { ...s, cond: r(s.cond), body: replaceFieldAccessInStmts(s.body, varName, fields) };
  }
}

// ── Pure function detection and generation ───────────────────

function isPureBody(stmts: StmtSpec[]): boolean {
  for (const s of stmts) {
    switch (s.kind) {
      case "while": return false;
      case "let": if (s.mutable) return false; break;
      case "if": if (!isPureBody(s.then) || !isPureBody(s.else)) return false; break;
      case "switch": if (!s.cases.every(c => isPureBody(c.body)) || !isPureBody(s.defaultBody)) return false; break;
    }
  }
  return true;
}

function transformPureBody(stmts: StmtSpec[], ctx: TransformCtx): LeanExpr | null {
  // Detect discriminant if-chain
  if (stmts.length > 0 && stmts[0].kind === "if") {
    const chain = detectDiscriminantChain(stmts, ctx);
    if (chain) return transformPureMatch(chain.chain, ctx);
  }

  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    const rest = stmts.slice(i + 1);
    switch (s.kind) {
      case "return": return specToExpr(s.value, ctx);
      case "let": {
        const restExpr = transformPureBody(rest, ctx);
        if (!restExpr) return null;
        return { kind: "let", name: s.name, value: specToExpr(s.init, ctx), body: restExpr };
      }
      case "if": {
        const thenExpr = transformPureBody(s.then, ctx);
        if (!thenExpr) return null;
        const elseBranch = s.else.length > 0 ? s.else : rest;
        const elseExpr = transformPureBody(elseBranch, ctx);
        if (!elseExpr) return null;
        return { kind: "if", cond: specToExpr(s.condition, ctx), then: thenExpr, else: elseExpr };
      }
      default: return null;
    }
  }
  return null;
}

function transformPureMatch(chain: Chain, ctx: TransformCtx): LeanExpr | null {
  const decl = ctx.typeDecls.find(d => d.name === chain.typeName);
  const arms: LeanMatchArm[] = [];
  for (const c of chain.cases) {
    const variant = decl?.variants?.find(v => v.name === c.variant);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.variant} ${fields.map(f => f.name).join(" ")}` : `.${c.variant}`;
    let body = transformPureBody(c.body, ctx);
    if (!body) return null;
    if (fields.length > 0) body = replaceFieldAccess(body, chain.varName, fields);
    arms.push({ pattern, body });
  }
  if (chain.fallthrough.length > 0) {
    const body = transformPureBody(chain.fallthrough, ctx);
    if (!body) return null;
    arms.push({ pattern: "_", body });
  }
  return { kind: "match", scrutinee: chain.varName, arms };
}

// ── Return-in-loop check ─────────────────────────────────────

function containsReturn(stmts: StmtSpec[]): boolean {
  for (const s of stmts) {
    if (s.kind === "return") return true;
    if (s.kind === "if" && (containsReturn(s.then) || containsReturn(s.else))) return true;
    if (s.kind === "while" && containsReturn(s.body)) return true;
  }
  return false;
}

// ── Top-level transform ─────────────────────────────────────

function transformTypeDecl(d: TypeDeclInfo): LeanDecl {
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
        fields: v.fields.map(f => ({ name: f.name, type: tsTypeToLean(f.tsType) })),
      })),
      deriving: ["Repr", "Inhabited"],
    };
  } else {
    return {
      kind: "structure", name: d.name,
      fields: d.fields!.map(f => ({ name: f.name, type: tsTypeToLean(f.tsType) })),
      deriving: ["Repr", "Inhabited", "DecidableEq"],
    };
  }
}

function transformFunction(fn: FunctionSpec, typeDecls: TypeDeclInfo[]): LeanMethod {
  if (fn.body.some(s => s.kind === "while") && containsReturn(fn.body.filter(s => s.kind === "while").flatMap(s => (s as any).body)))
    throw new Error(`${fn.name}: return inside a loop is not supported.`);

  const ctx = makeCtx(fn, typeDecls);
  const eCtx = { ...ctx, resultVar: "res" };

  const requires: LeanExpr[] = [];
  for (const r of fn.requires) requires.push(...specToClauses(r, ctx));
  const ensures: LeanExpr[] = [];
  for (const e of fn.ensures) {
    const m = ensuresToMatch(e, eCtx);
    if (m) ensures.push(m);
    else ensures.push(...specToClauses(e, eCtx));
  }

  return {
    kind: "method", name: fn.name,
    params: fn.params.map(p => ({ name: p.name, type: resolveType(p.name, p.type, fn.typeAnnotations) })),
    returnType: resolveType("\\result", fn.returnType, fn.typeAnnotations),
    requires, ensures,
    body: transformStmts(fn.body, ctx, fn),
  };
}

function transformPureFunction(fn: FunctionSpec, typeDecls: TypeDeclInfo[]): LeanDef | null {
  if (!isPureBody(fn.body)) return null;
  const ctx = makeCtx(fn, typeDecls);
  const body = transformPureBody(fn.body, ctx);
  if (!body) return null;
  return {
    kind: "def", name: `${fn.name}_pure`,
    params: fn.params.map(p => ({ name: p.name, type: resolveType(p.name, p.type, fn.typeAnnotations) })),
    returnType: resolveType("\\result", fn.returnType, fn.typeAnnotations),
    body,
  };
}

// ── Module transform → LeanFiles ─────────────────────────────

export function transformModule(mod: ModuleSpec, specImport?: string): { typesFile: LeanFile | null; defFile: LeanFile } {
  const typeDecls = mod.typeDecls.map(transformTypeDecl);
  const pureDefs: LeanDef[] = [];
  for (const fn of mod.functions) {
    const pd = transformPureFunction(fn, mod.typeDecls);
    if (pd) pureDefs.push(pd);
  }

  const base = mod.file.split("/").pop()?.replace(/\.ts$/, "") ?? "module";

  // Types file: type declarations + pure defs (if any)
  let typesFile: LeanFile | null = null;
  if (typeDecls.length > 0 || pureDefs.length > 0) {
    typesFile = {
      comment: "  Generated by lsc — Lean types and pure function mirrors.",
      imports: ["Velvet.Syntax", "Velvet.Std"],
      options: [],
      decls: [...typeDecls, ...pureDefs],
    };
  }

  // Def file: Velvet methods
  const methods = mod.functions.map(fn => transformFunction(fn, mod.typeDecls));
  const defImport = specImport ?? (typesFile ? `«${base}.types»` : null);
  const defFile: LeanFile = {
    comment: "  Generated by lsc from " + (mod.file.split("/").pop() ?? "") + "\n  Do not edit — re-run `lsc gen` to regenerate.",
    imports: defImport ? [defImport] : ["Velvet.Syntax", "Velvet.Std"],
    options: [
      { key: "loom.semantics.termination", value: '"total"' },
      { key: "loom.semantics.choice", value: '"demonic"' },
    ],
    decls: methods,
  };

  return { typesFile, defFile };
}
