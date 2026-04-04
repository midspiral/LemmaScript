/**
 * Transform — Typed IR → Dafny IR.
 *
 * Pure functions: imperative-to-functional lowering (loops → recursion).
 * Effectful functions: preserve imperative structure as Dafny methods.
 */

import type { TExpr, TStmt, TFunction, TModule, Ty } from "./typedir.js";
import type { DafnyExpr, DafnyStmt, DafnyDecl, DafnyFile, DafnyMatchArm, DafnyStmtMatchArm } from "./dafny-ir.js";
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

    case "binop": {
      if (e.op === "==>") {
        return { kind: "binop", op: "==>", left: transformExpr(e.left), right: transformExpr(e.right) };
      }
      return {
        kind: "binop",
        op: OP_MAP[e.op] ?? e.op,
        left: transformExpr(e.left),
        right: transformExpr(e.right),
      };
    }

    case "field":
      if (e.field === "length" && (e.obj.ty.kind === "array" || e.obj.ty.kind === "string"))
        return { kind: "seqLength", seq: transformExpr(e.obj) };
      // .toNat is a Lean-ism; Dafny doesn't need it — just emit the inner expression
      if (e.field === "toNat") return transformExpr(e.obj);
      return { kind: "field", obj: transformExpr(e.obj), field: e.field };

    case "index":
      return { kind: "index", seq: transformExpr(e.obj), idx: transformExpr(e.idx) };

    case "call": {
      // Math.floor(x / y) → JSFloorDiv(x, y) if dividing, else just x
      if (e.fn.kind === "field" && e.fn.field === "floor" &&
          e.fn.obj.kind === "var" && e.fn.obj.name === "Math" && e.args.length === 1) {
        const arg = e.args[0];
        if (arg.kind === "binop" && arg.op === "/") {
          needsJSFloorDiv = true;
          return { kind: "app", fn: "JSFloorDiv", args: [transformExpr(arg.left), transformExpr(arg.right)] };
        }
        return transformExpr(arg);
      }
      // Array method calls
      if (e.fn.kind === "field" && e.fn.obj.ty.kind === "array") {
        const recv = transformExpr(e.fn.obj);
        const method = e.fn.field;
        if (method === "includes") {
          return { kind: "binop", op: "in", left: transformExpr(e.args[0]), right: recv };
        }
      }
      // Regular function call
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

// ── Pure function: imperative → functional ──────────────────

/**
 * Transform a pure function body to a Dafny expression.
 * let → let-in, if/else → if-then-else, return → the expression.
 */
function transformPureBody(stmts: TStmt[]): DafnyExpr | null {
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    const rest = stmts.slice(i + 1);
    switch (s.kind) {
      case "return": return transformExpr(s.value);
      case "let": {
        const restExpr = transformPureBody(rest);
        if (!restExpr) return null;
        return { kind: "let", name: s.name, value: transformExpr(s.init), body: restExpr };
      }
      case "if": {
        const thenExpr = transformPureBody(s.then);
        if (!thenExpr) return null;
        const elseBranch = s.else.length > 0 ? s.else : rest;
        const elseExpr = transformPureBody(elseBranch);
        if (!elseExpr) return null;
        return { kind: "if", cond: transformExpr(s.cond), then: thenExpr, else: elseExpr };
      }
      default: return null;
    }
  }
  return null;
}

/**
 * Transform a while loop into a recursive Dafny function.
 * Returns the helper function declaration and the call expression.
 *
 * while (cond) { body } →
 *   function loop(vars...) { if cond then body; loop(updated_vars) else result }
 */
function transformWhileToRecursion(
  fn: TFunction,
  whileIdx: number,
  stmts: TStmt[],
): { helpers: DafnyDecl[]; body: DafnyExpr } | null {
  // Collect mutable variables declared before the while
  const mutVars: { name: string; ty: Ty; init: TExpr }[] = [];
  const letVars: { name: string; ty: Ty; init: TExpr }[] = [];

  for (let i = 0; i < whileIdx; i++) {
    const s = stmts[i];
    if (s.kind === "let") {
      if (s.mutable) mutVars.push({ name: s.name, ty: s.ty, init: s.init });
      else letVars.push({ name: s.name, ty: s.ty, init: s.init });
    }
  }

  const whileStmt = stmts[whileIdx];
  if (whileStmt.kind !== "while") return null;

  // The return statement after the while
  const afterWhile = stmts.slice(whileIdx + 1);
  const returnStmt = afterWhile.find(s => s.kind === "return");
  if (!returnStmt || returnStmt.kind !== "return") return null;

  // The loop helper takes all mutable variables as parameters
  const loopName = `${fn.name}_loop`;
  const loopParams = [
    ...fn.params.map(p => ({ name: p.name, type: tyToDafny(p.ty) })),
    ...mutVars.map(v => ({ name: v.name, type: tyToDafny(v.ty) })),
  ];

  // Transform the while body: collect assignments to mutable vars
  const loopBody = transformWhileBody(whileStmt.body, mutVars.map(v => v.name), loopName, fn.params.map(p => p.name));
  if (!loopBody) return null;

  // Build the recursive function body: if cond then loopBody else returnExpr
  const returnExpr = transformExpr(returnStmt.value);
  const condExpr = transformExpr(whileStmt.cond);

  const recursiveBody: DafnyExpr = {
    kind: "if",
    cond: condExpr,
    then: loopBody,
    else: returnExpr,
  };

  const loopFn: DafnyDecl = {
    kind: "function",
    name: loopName,
    params: loopParams,
    returnType: tyToDafny(fn.returnTy),
    requires: fn.requires.map(transformExpr),
    decreases: whileStmt.decreases ? transformExpr(whileStmt.decreases) : null,
    body: recursiveBody,
  };

  // Build the call: wrap let-bindings around the initial call
  const initialCall: DafnyExpr = {
    kind: "app",
    fn: loopName,
    args: [
      ...fn.params.map(p => ({ kind: "var" as const, name: p.name })),
      ...mutVars.map(v => transformExpr(v.init)),
    ],
  };

  // Wrap immutable lets around the call
  let body: DafnyExpr = initialCall;
  for (let i = letVars.length - 1; i >= 0; i--) {
    body = { kind: "let", name: letVars[i].name, value: transformExpr(letVars[i].init), body };
  }

  return { helpers: [loopFn], body };
}

/**
 * Transform while loop body into the "then" branch of the recursive function.
 * Tracks assignments to mutable variables and produces a recursive call with updated values.
 */
function transformWhileBody(
  stmts: TStmt[],
  mutNames: string[],
  loopName: string,
  fnParamNames: string[],
): DafnyExpr | null {
  // We need to thread the mutable variables through.
  // Strategy: transform to nested let/if expressions, ending with a recursive call.
  return transformWhileStmts(stmts, 0, mutNames, loopName, fnParamNames);
}

function transformWhileStmts(
  stmts: TStmt[],
  idx: number,
  mutNames: string[],
  loopName: string,
  fnParamNames: string[],
): DafnyExpr | null {
  if (idx >= stmts.length) {
    // End of loop body → recursive call with current variable names
    return {
      kind: "app",
      fn: loopName,
      args: [
        ...fnParamNames.map(n => ({ kind: "var" as const, name: n })),
        ...mutNames.map(n => ({ kind: "var" as const, name: n })),
      ],
    };
  }

  const s = stmts[idx];
  const rest = () => transformWhileStmts(stmts, idx + 1, mutNames, loopName, fnParamNames);

  switch (s.kind) {
    case "let": {
      const restExpr = rest();
      if (!restExpr) return null;
      return { kind: "let", name: s.name, value: transformExpr(s.init), body: restExpr };
    }

    case "assign": {
      // Rename: let newVar := value; continue with newVar
      const restExpr = rest();
      if (!restExpr) return null;
      return { kind: "let", name: s.target, value: transformExpr(s.value), body: restExpr };
    }

    case "if": {
      // If the then branch has a break, it exits the loop
      if (hasBranch(s.then, "break")) {
        const thenBreak = transformBreakBranch(s.then, stmts.slice(idx + 1), mutNames, loopName, fnParamNames);
        if (!thenBreak) return null;
        if (s.else.length > 0) {
          const elseExpr = transformWhileStmts(s.else, 0, mutNames, loopName, fnParamNames);
          if (!elseExpr) return null;
          return { kind: "if", cond: transformExpr(s.cond), then: thenBreak, else: elseExpr };
        }
        const elseExpr = rest();
        if (!elseExpr) return null;
        return { kind: "if", cond: transformExpr(s.cond), then: thenBreak, else: elseExpr };
      }

      if (s.else.length > 0) {
        // Both branches fully handle the rest (e.g. if/else if/else chains)
        const thenExpr = transformWhileStmts(s.then, 0, mutNames, loopName, fnParamNames);
        if (!thenExpr) return null;
        const elseExpr = transformWhileStmts(s.else, 0, mutNames, loopName, fnParamNames);
        if (!elseExpr) return null;
        return { kind: "if", cond: transformExpr(s.cond), then: thenExpr, else: elseExpr };
      }

      // No else — the if applies some assignments, then falls through to rest.
      // Wrap the then-assignments around rest, and use if-then-else to choose.
      const restExpr = rest();
      if (!restExpr) return null;
      // Apply then-branch assignments as let-bindings around restExpr
      let thenWithRest: DafnyExpr = restExpr;
      // Process then-branch assignments in reverse to build nested lets
      const assigns: { target: string; value: TExpr }[] = [];
      for (const ts of s.then) {
        if (ts.kind === "assign") assigns.push({ target: ts.target, value: ts.value });
      }
      for (let i = assigns.length - 1; i >= 0; i--) {
        thenWithRest = { kind: "let", name: assigns[i].target, value: transformExpr(assigns[i].value), body: thenWithRest };
      }
      return { kind: "if", cond: transformExpr(s.cond), then: thenWithRest, else: restExpr };
    }

    case "break":
      // break exits the loop — return current values without recursing
      // This is handled by the caller (the function wrapping the loop)
      return null; // signal: break encountered

    case "return":
      return transformExpr(s.value);

    default:
      return null;
  }
}

/**
 * Transform a break branch: the statements before break execute,
 * then we skip to the post-loop return.
 */
function transformBreakBranch(
  stmts: TStmt[],
  afterLoop: TStmt[],
  mutNames: string[],
  _loopName: string,
  _fnParamNames: string[],
): DafnyExpr | null {
  // Find the return value after the loop
  const returnStmt = afterLoop.find(s => s.kind === "return");
  const returnExpr = returnStmt && returnStmt.kind === "return"
    ? transformExpr(returnStmt.value)
    : { kind: "var" as const, name: mutNames[mutNames.length - 1] ?? "result" };

  // Process stmts before break
  let result: DafnyExpr = returnExpr;
  for (let i = stmts.length - 1; i >= 0; i--) {
    const s = stmts[i];
    if (s.kind === "break") continue;
    if (s.kind === "assign") {
      result = { kind: "let", name: s.target, value: transformExpr(s.value), body: result };
    } else if (s.kind === "let") {
      result = { kind: "let", name: s.name, value: transformExpr(s.init), body: result };
    }
  }
  return result;
}

function hasBranch(stmts: TStmt[], kind: string): boolean {
  for (const s of stmts) {
    if (s.kind === kind) return true;
    if (s.kind === "if" && (hasBranch(s.then, kind) || hasBranch(s.else, kind))) return true;
  }
  return false;
}

// ── Method transform (imperative) ───────────────────────────

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
      return []; // discard expression statements for now
    case "continue":
      return []; // not supported in Dafny methods yet
    case "switch":
      return []; // TODO
    case "forof":
      return []; // TODO
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

// ── JSFloorDiv preamble ─────────────────────────────────────

let needsJSFloorDiv = false;

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

  // Type declarations
  for (const td of mod.typeDecls) decls.push(transformTypeDecl(td));

  // Functions
  for (const fn of mod.functions) {
    try {
      if (fn.isPure) {
        const pureBody = transformPureBody(fn.body);
        if (pureBody) {
          decls.push({
            kind: "function",
            name: fn.name,
            params: fn.params.map(p => ({ name: p.name, type: tyToDafny(p.ty) })),
            returnType: tyToDafny(fn.returnTy),
            requires: fn.requires.map(transformExpr),
            decreases: null,
            body: pureBody,
          });
          continue;
        }
      }

      // Check for while-loop-based function → recursive helper
      const whileIdx = fn.body.findIndex(s => s.kind === "while");
      if (whileIdx >= 0) {
        const result = transformWhileToRecursion(fn, whileIdx, fn.body);
        if (result) {
          for (const h of result.helpers) decls.push(h);
          decls.push({
            kind: "function",
            name: fn.name,
            params: fn.params.map(p => ({ name: p.name, type: tyToDafny(p.ty) })),
            returnType: tyToDafny(fn.returnTy),
            requires: fn.requires.map(transformExpr),
            decreases: null,
            body: result.body,
          });
          continue;
        }
      }

      // Fallback: generate a Dafny method (imperative)
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

  // Prepend JSFloorDiv if needed
  if (needsJSFloorDiv) decls.unshift(JS_FLOOR_DIV);

  const base = mod.file.split("/").pop() ?? "";
  return {
    comment: `Generated by lsc from ${base}`,
    decls,
  };
}
