/**
 * LemmaScript code generator — IR → Lean/Velvet source
 *
 * Takes the ModuleSpec IR from extract.ts and produces a .lean file
 * containing a Velvet `method` + `prove_correct` that Loom can verify.
 */

import { exprToLean, astToLean, specToClauses, parseExpr, splitConjuncts, type Expr } from "./specparser.js";

// IR types (matching extract.ts output)
interface ParamSpec { name: string; type: string }
interface WhileSpec { kind: "while"; condition: string; invariants: string[]; decreases: string | null; body: StatementSpec[]; line: number }
interface IfSpec { kind: "if"; condition: string; then: StatementSpec[]; else: StatementSpec[]; line: number }
interface LetSpec { kind: "let"; name: string; mutable: boolean; type: string | null; init: string; line: number }
interface ReturnSpec { kind: "return"; value: string; line: number }
interface AssignSpec { kind: "assign"; target: string; value: string; line: number }
interface ExprStmtSpec { kind: "expr"; text: string; line: number }
type StatementSpec = WhileSpec | IfSpec | LetSpec | ReturnSpec | AssignSpec | ExprStmtSpec;
interface FunctionSpec { name: string; params: ParamSpec[]; returnType: string; requires: string[]; ensures: string[]; body: StatementSpec[]; line: number }
export interface ModuleSpec { file: string; imports: string[]; functions: FunctionSpec[] }

// ── Type mapping ─────────────────────────────────────────────

function tsTypeToLean(tsType: string): string {
  const t = tsType.trim();
  if (t === "number") return "Int";
  if (t === "number[]" || t === "Array<number>") return "Array Int";
  if (t === "boolean") return "Bool";
  if (t === "string") return "String";
  if (t === "void" || t === "undefined") return "Unit";
  const arrMatch = t.match(/^(?:Array<(.+)>|(.+)\[\])$/);
  if (arrMatch) return `Array ${tsTypeToLean(arrMatch[1] || arrMatch[2])}`;
  return t;
}

// ── Emit context ─────────────────────────────────────────────

function makeExprCtx(fn: FunctionSpec) {
  const arrayVars = new Set<string>();
  for (const p of fn.params) {
    if (p.type.includes("[]") || p.type.includes("Array")) {
      arrayVars.add(p.name);
    }
  }
  return { arrayVars, resultVar: "res", isSpec: true };
}

function makeBodyCtx(fn: FunctionSpec) {
  const ctx = makeExprCtx(fn);
  return { ...ctx, resultVar: "result", isSpec: false };
}

// ── Return-in-loop detection ─────────────────────────────────

function hasReturnInLoop(stmts: StatementSpec[]): boolean {
  for (const s of stmts) {
    if (s.kind === "while" && containsReturn(s.body)) return true;
  }
  return false;
}

function containsReturn(stmts: StatementSpec[]): boolean {
  for (const s of stmts) {
    if (s.kind === "return") return true;
    if (s.kind === "if" && (containsReturn(s.then) || containsReturn(s.else))) return true;
    if (s.kind === "while" && containsReturn(s.body)) return true;
  }
  return false;
}

function findDefaultReturn(stmts: StatementSpec[]): string | null {
  for (let i = stmts.length - 1; i >= 0; i--) {
    if (stmts[i].kind === "return") return (stmts[i] as ReturnSpec).value;
  }
  return null;
}

/**
 * Derive a result-tracking invariant from the ensures clauses.
 *
 * When the code generator introduces a `result` variable for return-in-loop,
 * the loop needs an invariant about what values `result` can take.
 * We derive: `result = <sentinel> ∨ (<ensures about result when ≠ sentinel>)`
 *
 * For ensures of the form `res <cmp> C` → include directly (with res → result)
 * For ensures of the form `P ==> Q` where P constrains res → include Q
 * For ensures of the form `res = sentinel ==> ...` → skip (sentinel branch)
 */
function deriveResultInvariant(
  ensures: string[],
  sentinel: string,
  specCtx: { arrayVars: Set<string>; resultVar: string; isSpec: boolean },
): string | null {
  const resultCtx = { ...specCtx, resultVar: "result" };
  const conjuncts: string[] = [];

  for (const ens of ensures) {
    const ast = parseExpr(ens);

    // Skip ensures of the form `result === sentinel ==> ...` (covers the sentinel case)
    if (ast.kind === "binop" && ast.op === "==>" && isSentinelGuard(ast.left, sentinel)) {
      continue;
    }

    // For implications `P ==> Q` where P constrains result: take Q as the property
    // that holds when result ≠ sentinel (the guard was satisfied on the break path)
    if (ast.kind === "binop" && ast.op === "==>") {
      const conclusion = flattenImplConclusion(ast);
      conjuncts.push(astToLean(conclusion, resultCtx));
      continue;
    }

    // For conjunctions, split and add each — but strengthen bounds:
    // When result ≠ sentinel, it was assigned from an array index (≥ 0),
    // so use 0 ≤ result instead of weaker sentinel-based bounds.
    for (const part of splitConjuncts(ast)) {
      // Detect `sentinel ≤ result` pattern and strengthen to `0 ≤ result`
      if (isSentinelLowerBound(part, sentinel)) {
        conjuncts.push("0 ≤ result");
        continue;
      }
      conjuncts.push(astToLean(part, resultCtx));
    }
  }

  if (conjuncts.length === 0) return null;
  const sentinelLean = exprToLean(sentinel, resultCtx);
  const body = conjuncts.join(" ∧ ");
  return `result = ${sentinelLean} ∨ (${body})`;
}

function isSentinelGuard(expr: Expr, sentinel: string): boolean {
  if (expr.kind === "binop" && expr.op === "===") {
    if (!(expr.left.kind === "var" && expr.left.name === "result")) return false;
    // Match sentinel value (handles negative: -1 parsed as unop(-, num(1)))
    const rhs = expr.right;
    if (rhs.kind === "num" && String(rhs.value) === sentinel) return true;
    if (rhs.kind === "unop" && rhs.op === "-" && rhs.expr.kind === "num"
        && `-${rhs.expr.value}` === sentinel) return true;
    return false;
  }
  return false;
}

/** Check if expr is `sentinel ≤ result` (e.g., `-1 ≤ result` from `result >= -1`). */
function isSentinelLowerBound(expr: Expr, sentinel: string): boolean {
  // After >= normalization, `result >= -1` becomes `binop{<=, unop{-,1}, var{result}}`
  if (expr.kind !== "binop" || expr.op !== "<=") return false;
  const rhs = expr.right;
  if (!(rhs.kind === "var" && rhs.name === "result")) return false;
  const lhs = expr.left;
  if (lhs.kind === "num" && String(lhs.value) === sentinel) return true;
  if (lhs.kind === "unop" && lhs.op === "-" && lhs.expr.kind === "num"
      && `-${lhs.expr.value}` === sentinel) return true;
  return false;
}

/** For `P ==> Q`, extract the conclusion Q (skipping premises about result range). */
function flattenImplConclusion(expr: Expr): Expr {
  if (expr.kind === "binop" && expr.op === "==>") {
    return flattenImplConclusion(expr.right);
  }
  return expr;
}

/** Negate a simple comparison for done_with clauses. */
function negateCondition(cond: string, ctx: ReturnType<typeof makeBodyCtx>): string {
  return `¬(${exprToLean(cond, ctx)})`;
}

// ── Body emission ────────────────────────────────────────────

interface EmitOpts {
  ctx: ReturnType<typeof makeBodyCtx>;
  specCtx: ReturnType<typeof makeExprCtx>;
  inLoop: boolean;
  resultTransform: boolean;
  sentinel: string | null;
  ensures: string[];
}

function emitBody(stmts: StatementSpec[], opts: EmitOpts): string[] {
  const { ctx, inLoop, resultTransform, sentinel } = opts;
  const lines: string[] = [];

  for (const s of stmts) {
    switch (s.kind) {
      case "let": {
        const leanInit = exprToLean(s.init, ctx);
        if (s.mutable) {
          lines.push(`let mut ${s.name} : Int := ${leanInit}`);
        } else {
          lines.push(`let ${s.name} := ${leanInit}`);
        }
        break;
      }

      case "while": {
        const cond = exprToLean(s.condition, ctx);
        lines.push(`while ${cond}`);

        for (const inv of s.invariants) {
          for (const c of specToClauses(inv, ctx)) lines.push(`  invariant ${c}`);
        }

        // done_with when there's a break from return transformation
        if (resultTransform && containsReturn(s.body) && sentinel !== null) {
          const sentinelLean = exprToLean(sentinel, ctx);
          const negCond = negateCondition(s.condition, ctx);
          lines.push(`  done_with result ≠ ${sentinelLean} ∨ ${negCond}`);
        }

        if (s.decreases) {
          lines.push(`  decreasing (${exprToLean(s.decreases, ctx)}).toNat`);
        }

        lines.push("do");
        const bodyLines = emitBody(s.body, { ...opts, inLoop: true });
        for (const bl of bodyLines) lines.push(`  ${bl}`);
        break;
      }

      case "if": {
        const cond = exprToLean(s.condition, ctx);
        lines.push(`if ${cond} then`);
        const thenLines = emitBody(s.then, opts);
        for (const tl of thenLines) lines.push(`  ${tl}`);
        if (s.else.length > 0) {
          if (s.else.length === 1 && s.else[0].kind === "if") {
            const elseIf = s.else[0] as IfSpec;
            lines.push(`else if ${exprToLean(elseIf.condition, ctx)} then`);
            const eifLines = emitBody(elseIf.then, opts);
            for (const el of eifLines) lines.push(`  ${el}`);
            if (elseIf.else.length > 0) {
              lines.push("else");
              const elLines = emitBody(elseIf.else, opts);
              for (const el of elLines) lines.push(`  ${el}`);
            }
          } else {
            lines.push("else");
            const elLines = emitBody(s.else, opts);
            for (const el of elLines) lines.push(`  ${el}`);
          }
        }
        break;
      }

      case "return": {
        if (inLoop && resultTransform) {
          lines.push(`result := ${exprToLean(s.value, ctx)}`);
          lines.push("break");
        } else if (resultTransform) {
          lines.push("return result");
        } else {
          lines.push(`return ${exprToLean(s.value, ctx)}`);
        }
        break;
      }

      case "assign": {
        lines.push(`${s.target} := ${exprToLean(s.value, ctx)}`);
        break;
      }

      case "expr": {
        lines.push(exprToLean(s.text, ctx));
        break;
      }
    }
  }

  return lines;
}

// ── Main generation ──────────────────────────────────────────

export function generateLean(mod: ModuleSpec, specLeanImport?: string): string {
  const lines: string[] = [];

  lines.push("/-");
  lines.push(`  Generated by lsc from ${mod.file.split("/").pop()}`);
  lines.push("  Do not edit — re-run \\`lsc check\\` to regenerate.");
  lines.push("-/");
  lines.push("import Velvet.Syntax");
  lines.push("import Velvet.Std");
  if (specLeanImport) lines.push(`import ${specLeanImport}`);
  lines.push("");
  lines.push('set_option loom.semantics.termination "total"');
  lines.push('set_option loom.semantics.choice "demonic"');

  for (const fn of mod.functions) {
    lines.push("");
    lines.push(...generateFunction(fn));
  }

  return lines.join("\n") + "\n";
}

function generateFunction(fn: FunctionSpec): string[] {
  const lines: string[] = [];
  const specCtx = makeExprCtx(fn);
  const bodyCtx = makeBodyCtx(fn);
  const retType = tsTypeToLean(fn.returnType);

  const resultTransform = hasReturnInLoop(fn.body);
  const sentinel = resultTransform ? findDefaultReturn(fn.body) : null;

  // Method signature
  const params = fn.params.map(p => `(${p.name} : ${tsTypeToLean(p.type)})`).join(" ");
  lines.push(`method ${fn.name} ${params} return (res : ${retType})`);

  for (const req of fn.requires) {
    for (const c of specToClauses(req, specCtx)) lines.push(`  require ${c}`);
  }
  for (const ens of fn.ensures) {
    for (const c of specToClauses(ens, specCtx)) lines.push(`  ensures ${c}`);
  }

  lines.push("  do");

  // Emit body, but insert result variable after leading let declarations
  // (Velvet's state tuple order depends on declaration order)
  const opts: EmitOpts = { ctx: bodyCtx, specCtx, inLoop: false, resultTransform, sentinel, ensures: fn.ensures };

  if (resultTransform && sentinel !== null) {
    // Split body into leading lets and the rest
    let splitIdx = 0;
    while (splitIdx < fn.body.length && fn.body[splitIdx].kind === "let") splitIdx++;

    const leadingLets = fn.body.slice(0, splitIdx);
    const rest = fn.body.slice(splitIdx);

    // Emit leading lets, then result variable, then the rest
    for (const bl of emitBody(leadingLets, opts)) lines.push(`    ${bl}`);
    lines.push(`    let mut result : ${retType} := ${exprToLean(sentinel, bodyCtx)}`);
    for (const bl of emitBody(rest, opts)) lines.push(`    ${bl}`);
  } else {
    for (const bl of emitBody(fn.body, opts)) lines.push(`    ${bl}`);
  }

  lines.push("");
  lines.push(`prove_correct ${fn.name} by`);
  lines.push("  loom_solve");

  return lines;
}
