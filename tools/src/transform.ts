/**
 * Transform — Typed IR → Lean IR.
 *
 * Consumes resolved types and classifications.
 * No type lookups, no string parsing, no re-inference.
 */

import type { TExpr, TStmt, TFunction, TModule, Ty } from "./typedir.js";
import type { LeanExpr, LeanStmt, LeanDecl, LeanFile, LeanDef, LeanMethod, LeanMatchArm, LeanStmtMatchArm } from "./ir.js";
import type { TypeDeclInfo } from "./types.js";
import { tsTypeToLean } from "./types.js";

/** Prefix match-bound field names to avoid capturing user variables. */
function matchBinder(fieldName: string): string {
  return `_${fieldName}`;
}

// ── Ty → Lean type string ────────────────────────────────────

function tyToLean(ty: Ty): string {
  switch (ty.kind) {
    case "nat": return "Nat";
    case "int": return "Int";
    case "bool": return "Bool";
    case "string": return "String";
    case "void": return "Unit";
    case "array": return `Array ${tyToLean(ty.elem)}`;
    case "user": return ty.name;
    case "unknown": return "Int"; // fallback
  }
}

function isNat(ty: Ty): boolean { return ty.kind === "nat"; }
function isArray(ty: Ty): boolean { return ty.kind === "array"; }
function isUser(ty: Ty): boolean { return ty.kind === "user"; }

// ── Built-in method table ───────────────────────────────────

const METHOD_TABLE: Record<string, Record<string, string>> = {
  string: {
    indexOf: "JSString.indexOf",
    slice:   "JSString.slice",
  },
};

const usedImports = new Set<string>();

function lookupMethod(recvTy: Ty, method: string): string | undefined {
  const tyKey = recvTy.kind === "array" ? "array" : recvTy.kind;
  const lean = METHOD_TABLE[tyKey]?.[method];
  if (lean) usedImports.add(lean.split(".")[0]);
  return lean;
}

// ── Transform expressions ────────────────────────────────────

const OP_MAP: Record<string, string> = {
  "===": "=", "!==": "≠", ">=": "≥", "<=": "≤", ">": ">", "<": "<",
  "&&": "∧", "||": "∨", "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
  "==": "=", "!=": "≠",
};

function transformExpr(e: TExpr): LeanExpr {
  switch (e.kind) {
    case "var": return { kind: "var", name: e.name };
    case "num": return { kind: "num", value: e.value };
    case "bool": return { kind: "bool", value: e.value };
    case "result": return { kind: "var", name: "res" };

    case "str":
      if (e.ty.kind === "user") return { kind: "constructor", name: e.value };
      return { kind: "str", value: e.value };

    case "unop":
      if (e.op === "-" && e.expr.kind === "num")
        return { kind: "num", value: -e.expr.value };
      return { kind: "unop", op: e.op === "!" ? "¬" : e.op, expr: transformExpr(e.expr) };

    case "binop": {
      // Implication: flatten (A && B) ==> C → implies [A, B] C
      if (e.op === "==>") {
        const { premises, conclusion } = flattenImpl(e);
        return { kind: "implies", premises: premises.map(transformExpr), conclusion: transformExpr(conclusion) };
      }
      // Discriminant check: x.discriminant === "foo" → x = .foo (before generic string literal comparison)
      if ((e.op === "===" || e.op === "!==") && e.left.kind === "field" && e.left.isDiscriminant && e.right.kind === "str") {
        return {
          kind: "binop",
          op: e.op === "===" ? "=" : "≠",
          left: transformExpr(e.left.obj),
          right: { kind: "constructor", name: e.right.value },
        };
      }
      // String literal comparison — constructor if user type, string literal if string
      if ((e.op === "===" || e.op === "!==") && e.right.kind === "str") {
        const left = transformExpr(e.left);
        const right: LeanExpr = isUser(e.left.ty)
          ? { kind: "constructor", name: e.right.value }
          : { kind: "str", value: e.right.value };
        return { kind: "binop", op: e.op === "===" ? "=" : "≠", left, right };
      }
      return {
        kind: "binop",
        op: OP_MAP[e.op] ?? e.op,
        left: transformExpr(e.left),
        right: transformExpr(e.right),
      };
    }

    case "field":
      if (e.field === "length" && isArray(e.obj.ty))
        return { kind: "field", obj: transformExpr(e.obj), field: "size" };
      if (e.field === "length" && e.obj.ty.kind === "string")
        return { kind: "field", obj: transformExpr(e.obj), field: "length" };
      return { kind: "field", obj: transformExpr(e.obj), field: e.field };

    case "index":
      if (isArray(e.obj.ty))
        return { kind: "index", arr: transformExpr(e.obj), idx: transformExpr(e.idx), toNat: !isNat(e.idx.ty) };
      return { kind: "index", arr: transformExpr(e.obj), idx: transformExpr(e.idx), toNat: false };

    case "call": {
      // Math.floor(x) → x
      if (e.fn.kind === "field" && e.fn.field === "floor" && e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1)
        return transformExpr(e.args[0]);
      // Built-in method call: receiver.method(args) → leanFn receiver args
      if (e.fn.kind === "field") {
        const lean = lookupMethod(e.fn.obj.ty, e.fn.field);
        if (lean)
          return { kind: "app", fn: lean, args: [transformExpr(e.fn.obj), ...e.args.map(transformExpr)] };
        throw new Error(`Unsupported method call: .${e.fn.field}() on ${e.fn.obj.ty.kind}`);
      }
      if (e.fn.kind !== "var")
        throw new Error(`Unsupported call expression: ${e.fn.kind}`);
      const prefix = e.callKind === "spec-pure" ? "Pure." : "";
      return { kind: "app", fn: prefix + e.fn.name, args: e.args.map(transformExpr) };
    }

    case "record":
      return { kind: "record", fields: e.fields.map(f => ({ name: f.name, value: transformExpr(f.value) })) };

    case "forall":
      return { kind: "forall", var: e.var, type: tyToLean(e.varTy), body: transformExpr(e.body) };

    case "exists":
      return { kind: "exists", var: e.var, type: tyToLean(e.varTy), body: transformExpr(e.body) };
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

function ensuresToMatch(e: TExpr, typeDecls: TypeDeclInfo[]): LeanExpr | null {
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

function replaceFieldAccess(e: LeanExpr, varName: string, fields: { name: string; tsType: string }[]): LeanExpr {
  if (e.kind === "field" && e.obj.kind === "var" && e.obj.name === varName) {
    const f = fields.find(f => f.name === e.field);
    if (f) return { kind: "var", name: matchBinder(f.name) };
  }
  const r = (x: LeanExpr) => replaceFieldAccess(x, varName, fields);
  switch (e.kind) {
    case "binop": return { ...e, left: r(e.left), right: r(e.right) };
    case "unop": return { ...e, expr: r(e.expr) };
    case "implies": return { ...e, premises: e.premises.map(r), conclusion: r(e.conclusion) };
    case "forall": return { ...e, body: r(e.body) };
    case "exists": return { ...e, body: r(e.body) };
    case "app": return { ...e, args: e.args.map(r) };
    case "record": return { ...e, fields: e.fields.map(f => ({ ...f, value: r(f.value) })) };
    case "if": return { ...e, cond: r(e.cond), then: r(e.then), else: r(e.else) };
    case "let":
      // If this let shadows the matched variable, stop replacing in the body
      if (e.name === varName) return { ...e, value: r(e.value) };
      return { ...e, value: r(e.value), body: r(e.body) };
    case "index": return { ...e, arr: r(e.arr), idx: r(e.idx) };
    case "field": return { ...e, obj: r(e.obj) };
    case "match": return { ...e, arms: e.arms.map(a => ({ ...a, body: r(a.body) })) };
    default: return e;
  }
}

// ── Transform statements ─────────────────────────────────────

function transformStmts(stmts: TStmt[], typeDecls: TypeDeclInfo[]): LeanStmt[] {
  const result: LeanStmt[] = [];
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
    }
    // Transform for-of → for-in over range
    if (s.kind === "forof") {
      const arrExpr = transformExpr(s.iterable);
      const idxName = `_${s.varName}_idx`;
      const idx: LeanExpr = { kind: "var", name: idxName };
      const arrSize: LeanExpr = { kind: "field", obj: arrExpr, field: "size" };
      const bodyStmts = transformStmts(s.body, typeDecls);
      const letElem: LeanStmt = { kind: "let", name: s.varName, type: tyToLean(s.varTy), mutable: false, value: { kind: "index", arr: arrExpr, idx, toNat: false } };
      result.push({
        kind: "forin",
        idx: idxName,
        bound: arrSize,
        invariants: s.invariants.map(transformExpr),
        body: [letElem, ...bodyStmts],
      });
      i++;
      continue;
    }
    result.push(transformStmt(s, typeDecls));
    i++;
  }
  return result;
}

function transformStmt(s: TStmt, typeDecls: TypeDeclInfo[]): LeanStmt {
  switch (s.kind) {
    case "let":
      return { kind: "let", name: s.name, type: tyToLean(s.ty), mutable: s.mutable, value: transformExpr(s.init) };

    case "assign": {
      const value = transformExpr(s.value);
      // Method call → monadic bind
      if (s.value.kind === "call" && s.value.callKind === "method")
        return { kind: "bind", target: s.target, value };
      return { kind: "assign", target: s.target, value };
    }

    case "return": return { kind: "return", value: transformExpr(s.value) };
    case "break": return { kind: "break" };
    case "continue": return { kind: "continue" };
    case "expr": return { kind: "assign", target: "_", value: transformExpr(s.expr) };

    case "if":
      return { kind: "if", cond: transformExpr(s.cond), then: transformStmts(s.then, typeDecls), else: transformStmts(s.else, typeDecls) };

    case "while":
      return {
        kind: "while",
        cond: transformExpr(s.cond),
        invariants: s.invariants.map(transformExpr),
        decreasing: s.decreases ? transformExpr(s.decreases) : null,
        doneWith: s.doneWith ? transformExpr(s.doneWith) : null,
        body: transformStmts(s.body, typeDecls),
      };

    case "forof":
      throw new Error("forof should be transformed to forin (range loop) in transformStmts");

    case "switch":
      return emitSwitchStmt(s, typeDecls);
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

function emitMatchStmt(chain: Chain, typeDecls: TypeDeclInfo[]): LeanStmt {
  const decl = typeDecls.find(d => d.name === chain.typeName);
  const arms: LeanStmtMatchArm[] = chain.cases.map(c => {
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

function emitSwitchStmt(s: TStmt & { kind: "switch" }, typeDecls: TypeDeclInfo[]): LeanStmt {
  const varName = s.expr.kind === "var" ? s.expr.name : "?";
  const typeName = s.expr.ty.kind === "user" ? s.expr.ty.name : undefined;
  const decl = typeName ? typeDecls.find(d => d.name === typeName) : undefined;
  const arms: LeanStmtMatchArm[] = s.cases.map(c => {
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

function replaceFieldAccessInStmts(stmts: LeanStmt[], varName: string, fields: { name: string; tsType: string }[]): LeanStmt[] {
  if (fields.length === 0) return stmts;
  const result: LeanStmt[] = [];
  for (const s of stmts) {
    // If a let shadows the matched variable, stop replacing from here on
    if (s.kind === "let" && s.name === varName) {
      const r = (e: LeanExpr) => replaceFieldAccess(e, varName, fields);
      result.push({ ...s, value: r(s.value) });
      // Remaining statements see the shadowed name — no more replacement
      result.push(...stmts.slice(result.length));
      break;
    }
    result.push(replaceFieldAccessInStmt(s, varName, fields));
  }
  return result;
}

function replaceFieldAccessInStmt(s: LeanStmt, varName: string, fields: { name: string; tsType: string }[]): LeanStmt {
  const r = (e: LeanExpr) => replaceFieldAccess(e, varName, fields);
  switch (s.kind) {
    case "let": return { ...s, value: r(s.value) };
    case "assign": return { ...s, value: r(s.value) };
    case "bind": return { ...s, value: r(s.value) };
    case "return": return { ...s, value: r(s.value) };
    case "break": case "continue": return s;
    case "if": return { ...s, cond: r(s.cond), then: replaceFieldAccessInStmts(s.then, varName, fields), else: replaceFieldAccessInStmts(s.else, varName, fields) };
    case "match": return { ...s, arms: s.arms.map(a => ({ ...a, body: replaceFieldAccessInStmts(a.body, varName, fields) })) };
    case "while": return { ...s, cond: r(s.cond), body: replaceFieldAccessInStmts(s.body, varName, fields) };
    case "forin": return { ...s, invariants: s.invariants.map(r), body: replaceFieldAccessInStmts(s.body, varName, fields) };
  }
}

// ── Pure function generation ─────────────────────────────────

function transformPureBody(stmts: TStmt[], typeDecls: TypeDeclInfo[]): LeanExpr | null {
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
      default: return null;
    }
  }
  return null;
}

function transformPureMatch(chain: Chain, typeDecls: TypeDeclInfo[]): LeanExpr | null {
  const decl = typeDecls.find(d => d.name === chain.typeName);
  const arms: LeanMatchArm[] = [];
  for (const c of chain.cases) {
    const variant = decl?.variants?.find(v => v.name === c.variant);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0 ? `.${c.variant} ${fields.map(f => matchBinder(f.name)).join(" ")}` : `.${c.variant}`;
    let body = transformPureBody(c.body, typeDecls);
    if (!body) return null;
    if (fields.length > 0) body = replaceFieldAccess(body, chain.varName, fields);
    arms.push({ pattern, body });
  }
  if (chain.fallthrough.length > 0) {
    const body = transformPureBody(chain.fallthrough, typeDecls);
    if (!body) return null;
    arms.push({ pattern: "_", body });
  }
  return { kind: "match", scrutinee: chain.varName, arms };
}

// ── Generate type declarations ───────────────────────────────

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

// ── Top-level transform ──────────────────────────────────────

export function transformModule(mod: TModule, specImport?: string): { typesFile: LeanFile | null; defFile: LeanFile } {
  const typeDecls = mod.typeDecls.map(transformTypeDecl);

  // Pure function mirrors
  const pureDefs: LeanDef[] = [];
  for (const fn of mod.functions) {
    if (!fn.isPure) continue;
    const body = transformPureBody(fn.body, mod.typeDecls);
    if (!body) continue;
    pureDefs.push({
      kind: "def",
      name: fn.name,
      params: fn.params.map(p => ({ name: p.name, type: tyToLean(p.ty) })),
      returnType: tyToLean(fn.returnTy),
      body,
    });
  }

  const base = mod.file.split("/").pop()?.replace(/\.ts$/, "") ?? "module";

  // Types file
  const typesImports = ["Velvet.Syntax", "Velvet.Std"];
  for (const m of usedImports) typesImports.push(m);
  usedImports.clear();
  let typesFile: LeanFile | null = null;
  const pureNamespace: LeanDecl[] = pureDefs.length > 0
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
  const methods: LeanMethod[] = mod.functions.map(fn => {
    const ensures: LeanExpr[] = [];
    for (const e of fn.ensures) {
      const m = ensuresToMatch(e, mod.typeDecls);
      if (m) ensures.push(m);
      else ensures.push(transformExpr(e));
    }

    return {
      kind: "method" as const,
      name: fn.name,
      params: fn.params.map(p => ({ name: p.name, type: tyToLean(p.ty) })),
      returnType: tyToLean(fn.returnTy),
      requires: fn.requires.map(transformExpr),
      ensures,
      body: transformStmts(fn.body, mod.typeDecls),
    };
  });

  const defImport = specImport ?? (typesFile ? `«${base}.types»` : null);
  const defBaseImports = defImport ? [defImport] : ["Velvet.Syntax", "Velvet.Std"];
  // If no types file, method-body imports need to go on the def file directly
  if (!typesFile) for (const m of usedImports) defBaseImports.push(m);
  usedImports.clear();
  const defFile: LeanFile = {
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
