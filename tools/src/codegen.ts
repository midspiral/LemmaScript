/**
 * LemmaScript code generator — IR → Lean/Velvet source
 *
 * Takes the ModuleSpec IR from extract.ts and produces a .lean file
 * containing a Velvet `method` + `prove_correct` that Loom can verify.
 */

import { exprToLean, specToClauses, parseExpr, isNat as specIsNat, type EmitContext } from "./specparser.js";

// IR types (matching extract.ts)
interface ParamSpec { name: string; type: string }
interface WhileSpec { kind: "while"; condition: string; invariants: string[]; decreases: string | null; body: StatementSpec[]; line: number }
interface IfSpec { kind: "if"; condition: string; then: StatementSpec[]; else: StatementSpec[]; line: number }
interface LetSpec { kind: "let"; name: string; mutable: boolean; type: string | null; init: string; line: number }
interface ReturnSpec { kind: "return"; value: string; line: number }
interface AssignSpec { kind: "assign"; target: string; value: string; line: number }
interface ExprStmtSpec { kind: "expr"; text: string; line: number }
type StatementSpec = WhileSpec | IfSpec | LetSpec | ReturnSpec | AssignSpec | ExprStmtSpec;
interface FunctionSpec { name: string; params: ParamSpec[]; returnType: string; requires: string[]; ensures: string[]; natVars: string[]; body: StatementSpec[]; line: number }
export interface ModuleSpec { file: string; imports: string[]; functions: FunctionSpec[] }

// ── Type mapping ─────────────────────────────────────────────

function leanType(tsType: string, isNat: boolean): string {
  const t = tsType.trim();
  if (t === "number") return isNat ? "Nat" : "Int";
  if (t === "number[]" || t === "Array<number>") return "Array Int";
  if (t === "boolean") return "Bool";
  if (t === "string") return "String";
  if (t === "void" || t === "undefined") return "Unit";
  const arrMatch = t.match(/^(?:Array<(.+)>|(.+)\[\])$/);
  if (arrMatch) return `Array ${leanType(arrMatch[1] || arrMatch[2], false)}`;
  return t;
}

// ── Emit context ─────────────────────────────────────────────

function makeCtx(fn: FunctionSpec, resultVar: string): EmitContext {
  const arrayVars = new Set<string>();
  for (const p of fn.params) {
    if (p.type.includes("[]") || p.type.includes("Array")) arrayVars.add(p.name);
  }
  return { arrayVars, natVars: new Set(fn.natVars), resultVar };
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

// ── Body emission ────────────────────────────────────────────

interface EmitOpts {
  ctx: EmitContext;
  natVars: Set<string>;
  inLoop: boolean;
  resultTransform: boolean;
  sentinel: string | null;
}

function emitBody(stmts: StatementSpec[], opts: EmitOpts): string[] {
  const { ctx, natVars, inLoop, resultTransform, sentinel } = opts;
  const lines: string[] = [];

  for (const s of stmts) {
    switch (s.kind) {
      case "let": {
        const varIsNat = natVars.has(s.name);
        const ty = leanType("number", varIsNat);
        const init = exprToLean(s.init, ctx);
        lines.push(s.mutable ? `let mut ${s.name} : ${ty} := ${init}` : `let ${s.name} := ${init}`);
        break;
      }

      case "while": {
        lines.push(`while ${exprToLean(s.condition, ctx)}`);

        for (const inv of s.invariants) {
          for (const c of specToClauses(inv, ctx)) lines.push(`  invariant ${c}`);
        }

        if (resultTransform && containsReturn(s.body) && sentinel !== null) {
          lines.push(`  done_with result ≠ ${exprToLean(sentinel, ctx)} ∨ ¬(${exprToLean(s.condition, ctx)})`);
        }

        if (s.decreases) {
          // If the expression is Nat-typed, emit directly; otherwise wrap in .toNat
          const ast = parseExpr(s.decreases);
          const decreasesIsNat = specIsNat(ast, ctx);
          const dec = exprToLean(s.decreases, ctx);
          lines.push(decreasesIsNat ? `  decreasing ${dec}` : `  decreasing (${dec}).toNat`);
        }

        lines.push("do");
        for (const bl of emitBody(s.body, { ...opts, inLoop: true })) lines.push(`  ${bl}`);
        break;
      }

      case "if": {
        const cond = exprToLean(s.condition, ctx);
        lines.push(`if ${cond} then`);
        for (const tl of emitBody(s.then, opts)) lines.push(`  ${tl}`);
        if (s.else.length > 0) {
          if (s.else.length === 1 && s.else[0].kind === "if") {
            const ei = s.else[0] as IfSpec;
            lines.push(`else if ${exprToLean(ei.condition, ctx)} then`);
            for (const el of emitBody(ei.then, opts)) lines.push(`  ${el}`);
            if (ei.else.length > 0) {
              lines.push("else");
              for (const el of emitBody(ei.else, opts)) lines.push(`  ${el}`);
            }
          } else {
            lines.push("else");
            for (const el of emitBody(s.else, opts)) lines.push(`  ${el}`);
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

      case "assign":
        lines.push(`${s.target} := ${exprToLean(s.value, ctx)}`);
        break;

      case "expr":
        lines.push(exprToLean(s.text, ctx));
        break;
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
  const specCtx = makeCtx(fn, "res");
  const bodyCtx = makeCtx(fn, "result");
  const natVars = new Set(fn.natVars);

  const resultTransform = hasReturnInLoop(fn.body);
  const sentinel = resultTransform ? findDefaultReturn(fn.body) : null;

  // Method signature
  const params = fn.params.map(p => `(${p.name} : ${leanType(p.type, false)})`).join(" ");
  const retType = leanType(fn.returnType, false);
  lines.push(`method ${fn.name} ${params} return (res : ${retType})`);

  for (const req of fn.requires) {
    for (const c of specToClauses(req, specCtx)) lines.push(`  require ${c}`);
  }
  for (const ens of fn.ensures) {
    for (const c of specToClauses(ens, specCtx)) lines.push(`  ensures ${c}`);
  }

  lines.push("  do");

  // Emit body. Insert result variable after leading lets if needed.
  const opts: EmitOpts = { ctx: bodyCtx, natVars, inLoop: false, resultTransform, sentinel };

  if (resultTransform && sentinel !== null) {
    let splitIdx = 0;
    while (splitIdx < fn.body.length && fn.body[splitIdx].kind === "let") splitIdx++;
    const leading = fn.body.slice(0, splitIdx);
    const rest = fn.body.slice(splitIdx);
    for (const bl of emitBody(leading, opts)) lines.push(`    ${bl}`);
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
