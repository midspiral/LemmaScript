/**
 * Transform — Typed IR → Dafny IR.
 *
 * All TS functions become Dafny methods (imperative, with while loops).
 * Pure Dafny functions can be added by the LLM in the .dfy file if needed for proofs.
 */

import type { TExpr, TStmt, TFunction, TModule, Ty } from "./typedir.js";
import type { DafnyExpr, DafnyStmt, DafnyDecl, DafnyFile } from "./dafny-ir.js";
import type { TypeDeclInfo } from "./types.js";
import { parseTsType, tyToDafny } from "./types.js";

class UnsupportedError extends Error {
  constructor(feature: string) { super(`Unsupported Dafny feature: ${feature}`); }
}

// ── Operator mapping ────────────────────────────────────────

const OP_MAP: Record<string, string> = {
  "===": "==", "!==": "!=", ">=": ">=", "<=": "<=", ">": ">", "<": "<",
  "&&": "&&", "||": "||", "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
  "==": "==", "!=": "!=",
};

// ── Expression transform ────────────────────────────────────

let needsJSFloorDiv = false;

function transformExpr(e: TExpr): DafnyExpr {
  switch (e.kind) {
    case "var": return { kind: "var", name: e.name };
    case "num": return { kind: "num", value: e.value };
    case "bool": return { kind: "bool", value: e.value };
    case "str": return { kind: "str", value: e.value };
    case "result": return { kind: "var", name: "res" };

    case "unop":
      if (e.op === "-" && e.expr.kind === "num")
        return { kind: "num", value: -e.expr.value };
      return { kind: "unop", op: e.op === "!" ? "!" : e.op, expr: transformExpr(e.expr) };

    case "binop":
      return {
        kind: "binop",
        op: OP_MAP[e.op] ?? e.op,
        left: transformExpr(e.left),
        right: transformExpr(e.right),
      };

    case "field":
      if (e.field === "length" && (e.obj.ty.kind === "array" || e.obj.ty.kind === "string"))
        return { kind: "seqLength", seq: transformExpr(e.obj) };
      if (e.field === "toNat") return transformExpr(e.obj);
      return { kind: "field", obj: transformExpr(e.obj), field: e.field };

    case "index":
      return { kind: "index", seq: transformExpr(e.obj), idx: transformExpr(e.idx) };

    case "call": {
      if (e.fn.kind === "field" && e.fn.field === "floor" &&
          e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1) {
        const arg = e.args[0];
        if (arg.kind === "binop" && arg.op === "/") {
          needsJSFloorDiv = true;
          return { kind: "app", fn: "JSFloorDiv", args: [transformExpr(arg.left), transformExpr(arg.right)] };
        }
        return transformExpr(arg);
      }
      if (e.fn.kind === "field" && e.fn.obj.ty.kind === "array" && e.fn.field === "includes")
        return { kind: "binop", op: "in", left: transformExpr(e.args[0]), right: transformExpr(e.fn.obj) };
      if (e.fn.kind === "var")
        return { kind: "app", fn: e.fn.name, args: e.args.map(transformExpr) };
      if (e.fn.kind === "field")
        return { kind: "app", fn: e.fn.field, args: [transformExpr(e.fn.obj), ...e.args.map(transformExpr)] };
      throw new Error(`Unsupported call: ${e.fn.kind}`);
    }

    case "record":
      return { kind: "record", fields: e.fields.map(f => ({ name: f.name, value: transformExpr(f.value) })) };
    case "arrayLiteral":
      return { kind: "seqLiteral", elems: e.elems.map(transformExpr) };
    case "forall":
      return { kind: "forall", vars: [{ name: e.var, type: tyToDafny(e.varTy) }], body: transformExpr(e.body) };
    case "exists":
      return { kind: "exists", vars: [{ name: e.var, type: tyToDafny(e.varTy) }], body: transformExpr(e.body) };
    case "conditional":
      return { kind: "if", cond: transformExpr(e.cond), then: transformExpr(e.then), else: transformExpr(e.else) };
    case "lambda":
      throw new UnsupportedError("lambda");
  }
}

// ── Statement transform ─────────────────────────────────────

function transformStmts(stmts: TStmt[]): DafnyStmt[] {
  const result: DafnyStmt[] = [];
  for (const s of stmts) result.push(...transformStmt(s));
  return result;
}

function transformStmt(s: TStmt): DafnyStmt[] {
  switch (s.kind) {
    case "let":
      return [{ kind: "var", name: s.name, type: tyToDafny(s.ty), mutable: s.mutable, value: transformExpr(s.init) }];
    case "assign":
      return [{ kind: "assign", target: s.target, value: transformExpr(s.value) }];
    case "return":
      return [{ kind: "return", value: transformExpr(s.value) }];
    case "break":
      return [{ kind: "break" }];
    case "if":
      return [{ kind: "if", cond: transformExpr(s.cond), then: transformStmts(s.then), else: transformStmts(s.else) }];
    case "while":
      return [{
        kind: "while",
        cond: transformExpr(s.cond),
        invariants: s.invariants.map(transformExpr),
        decreases: s.decreases ? transformExpr(s.decreases) : null,
        body: transformStmts(s.body),
      }];
    case "expr":
      return [];
    case "continue":
      return [];
    case "switch":
      return [];
    case "forof":
      return [];
  }
}

// ── Type declarations ───────────────────────────────────────

function transformTypeDecl(d: TypeDeclInfo): DafnyDecl {
  if (d.kind === "string-union") {
    return {
      kind: "datatype",
      name: d.name,
      constructors: d.values!.map(v => ({ name: v, fields: [] })),
    };
  } else if (d.kind === "discriminated-union") {
    return {
      kind: "datatype",
      name: d.name,
      constructors: d.variants!.map(v => ({
        name: v.name,
        fields: v.fields.map(f => ({ name: f.name, type: tyToDafny(parseTsType(f.tsType)) })),
      })),
    };
  } else {
    return {
      kind: "datatype",
      name: d.name,
      constructors: [{ name: d.name, fields: d.fields!.map(f => ({ name: f.name, type: tyToDafny(parseTsType(f.tsType)) })) }],
    };
  }
}

// ── JSFloorDiv ──────────────────────────────────────────────

const JS_FLOOR_DIV: DafnyDecl = {
  kind: "function",
  name: "JSFloorDiv",
  params: [{ name: "a", type: "int" }, { name: "b", type: "int" }],
  returnType: "int",
  requires: [{ kind: "binop", op: "!=", left: { kind: "var", name: "b" }, right: { kind: "num", value: 0 } }],
  decreases: null,
  body: {
    kind: "if",
    cond: { kind: "binop", op: ">", left: { kind: "var", name: "b" }, right: { kind: "num", value: 0 } },
    then: {
      kind: "if",
      cond: { kind: "binop", op: ">=", left: { kind: "var", name: "a" }, right: { kind: "num", value: 0 } },
      then: { kind: "binop", op: "/", left: { kind: "var", name: "a" }, right: { kind: "var", name: "b" } },
      else: {
        kind: "binop", op: "-",
        left: { kind: "unop", op: "-", expr: {
          kind: "binop", op: "/",
          left: { kind: "binop", op: "-", left: { kind: "unop", op: "-", expr: { kind: "var", name: "a" } }, right: { kind: "num", value: 1 } },
          right: { kind: "var", name: "b" },
        }},
        right: { kind: "num", value: 1 },
      },
    },
    else: {
      kind: "if",
      cond: { kind: "binop", op: "<=", left: { kind: "var", name: "a" }, right: { kind: "num", value: 0 } },
      then: {
        kind: "binop", op: "/",
        left: { kind: "unop", op: "-", expr: { kind: "var", name: "a" } },
        right: { kind: "unop", op: "-", expr: { kind: "var", name: "b" } },
      },
      else: {
        kind: "binop", op: "-",
        left: { kind: "unop", op: "-", expr: {
          kind: "binop", op: "/",
          left: { kind: "binop", op: "-", left: { kind: "var", name: "a" }, right: { kind: "num", value: 1 } },
          right: { kind: "unop", op: "-", expr: { kind: "var", name: "b" } },
        }},
        right: { kind: "num", value: 1 },
      },
    },
  },
};

// ── Top-level ───────────────────────────────────────────────

export function transformDafnyModule(mod: TModule): DafnyFile {
  needsJSFloorDiv = false;
  const decls: DafnyDecl[] = [];

  for (const td of mod.typeDecls) decls.push(transformTypeDecl(td));

  for (const fn of mod.functions) {
    try {
      decls.push({
        kind: "method",
        name: fn.name,
        params: fn.params.map(p => ({ name: p.name, type: tyToDafny(p.ty) })),
        returns: [{ name: "res", type: tyToDafny(fn.returnTy) }],
        requires: fn.requires.map(transformExpr),
        ensures: fn.ensures.map(transformExpr),
        decreases: null,
        body: transformStmts(fn.body),
      });
    } catch (e) {
      if (e instanceof UnsupportedError) {
        console.error(`Skipping ${fn.name}: ${e.message}`);
        continue;
      }
      throw e;
    }
  }

  if (needsJSFloorDiv) decls.unshift(JS_FLOOR_DIV);

  const base = mod.file.split("/").pop() ?? "";
  return { comment: `Generated by lsc from ${base}`, decls };
}
