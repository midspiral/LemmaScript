/**
 * Code generator — IR → .def.lean
 *
 * Produces a Velvet `method` definition (no `prove_correct`).
 * Translation is mechanical per SPEC.md §4–§5.
 */

import { exprToLean, specToClauses, parseExpr, isNat, type EmitContext } from "./specparser.js";
import type { ModuleSpec, FunctionSpec, StmtSpec, IfSpec } from "./extract.js";

// ── Type mapping (SPEC.md §8) ────────────────────────────────

function leanType(tsType: string, nat: boolean): string {
  const t = tsType.trim();
  if (t === "number") return nat ? "Nat" : "Int";
  if (t === "number[]" || t === "Array<number>") return "Array Int";
  if (t === "boolean") return "Bool";
  if (t === "string") return "String";
  if (t === "void" || t === "undefined") return "Unit";
  const m = t.match(/^(?:Array<(.+)>|(.+)\[\])$/);
  if (m) return `Array ${leanType(m[1] || m[2], false)}`;
  return t;
}

// ── Context ──────────────────────────────────────────────────

function makeCtx(fn: FunctionSpec, resultVar: string): EmitContext {
  const arrayVars = new Set<string>();
  for (const p of fn.params) if (p.type.includes("[]") || p.type.includes("Array")) arrayVars.add(p.name);
  const natVars = new Set(fn.typeAnnotations.filter(t => t.type === "nat").map(t => t.name));
  return { arrayVars, natVars, resultVar };
}

// ── Return-in-loop check (SPEC.md §5.3) ─────────────────────

function hasReturnInLoop(stmts: StmtSpec[]): boolean {
  for (const s of stmts) {
    if (s.kind !== "while") continue;
    if (containsReturn(s.body)) return true;
  }
  return false;
}

function containsReturn(stmts: StmtSpec[]): boolean {
  for (const s of stmts) {
    if (s.kind === "return") return true;
    if (s.kind === "if" && (containsReturn(s.then) || containsReturn(s.else))) return true;
    if (s.kind === "while" && containsReturn(s.body)) return true;
  }
  return false;
}

// ── Body emission ────────────────────────────────────────────

function emitBody(stmts: StmtSpec[], ctx: EmitContext, natNames: Set<string>): string[] {
  const lines: string[] = [];
  for (const s of stmts) {
    switch (s.kind) {
      case "let": {
        const nat = natNames.has(s.name);
        const ty = leanType("number", nat);
        const init = exprToLean(s.init, ctx);
        lines.push(s.mutable ? `let mut ${s.name} : ${ty} := ${init}` : `let ${s.name} := ${init}`);
        break;
      }
      case "assign":
        lines.push(`${s.target} := ${exprToLean(s.value, ctx)}`);
        break;
      case "return":
        lines.push(`return ${exprToLean(s.value, ctx)}`);
        break;
      case "break":
        lines.push("break");
        break;
      case "expr":
        lines.push(exprToLean(s.text, ctx));
        break;

      case "while": {
        lines.push(`while ${exprToLean(s.condition, ctx)}`);
        for (const inv of s.invariants)
          for (const c of specToClauses(inv, ctx)) lines.push(`  invariant ${c}`);
        if (s.doneWith) lines.push(`  done_with ${exprToLean(s.doneWith, ctx)}`);
        if (s.decreases) lines.push(`  decreasing ${exprToLean(s.decreases, ctx)}`);
        lines.push("do");
        for (const bl of emitBody(s.body, ctx, natNames)) lines.push(`  ${bl}`);
        break;
      }

      case "if": {
        lines.push(`if ${exprToLean(s.condition, ctx)} then`);
        for (const tl of emitBody(s.then, ctx, natNames)) lines.push(`  ${tl}`);
        if (s.else.length > 0) {
          if (s.else.length === 1 && s.else[0].kind === "if") {
            const ei = s.else[0] as IfSpec;
            lines.push(`else if ${exprToLean(ei.condition, ctx)} then`);
            for (const el of emitBody(ei.then, ctx, natNames)) lines.push(`  ${el}`);
            if (ei.else.length > 0) {
              lines.push("else");
              for (const el of emitBody(ei.else, ctx, natNames)) lines.push(`  ${el}`);
            }
          } else {
            lines.push("else");
            for (const el of emitBody(s.else, ctx, natNames)) lines.push(`  ${el}`);
          }
        }
        break;
      }
    }
  }
  return lines;
}

// ── Function generation ──────────────────────────────────────

function generateFunction(fn: FunctionSpec): string[] {
  // Error on return inside loop
  if (hasReturnInLoop(fn.body)) {
    throw new Error(
      `${fn.name}: return inside a loop is not supported. ` +
      `Restructure to use break + a result variable (SPEC.md §5.3).`
    );
  }

  const lines: string[] = [];
  const specCtx = makeCtx(fn, "res");
  const bodyCtx = makeCtx(fn, "res"); // \result doesn't appear in body, but just in case
  const natNames = new Set(fn.typeAnnotations.filter(t => t.type === "nat").map(t => t.name));

  const params = fn.params.map(p => `(${p.name} : ${leanType(p.type, false)})`).join(" ");
  lines.push(`method ${fn.name} ${params} return (res : ${leanType(fn.returnType, false)})`);
  for (const r of fn.requires) for (const c of specToClauses(r, specCtx)) lines.push(`  require ${c}`);
  for (const e of fn.ensures) for (const c of specToClauses(e, specCtx)) lines.push(`  ensures ${c}`);
  lines.push("  do");
  for (const bl of emitBody(fn.body, bodyCtx, natNames)) lines.push(`    ${bl}`);

  return lines;
}

// ── Module generation ────────────────────────────────────────

export function generateDef(mod: ModuleSpec, specImport?: string): string {
  const lines: string[] = [];
  lines.push("/-");
  lines.push(`  Generated by lsc from ${mod.file.split("/").pop()}`);
  lines.push("  Do not edit — re-run \\`lsc gen\\` to regenerate.");
  lines.push("-/");
  if (specImport) {
    lines.push(`import ${specImport}`);
  } else {
    lines.push("import Velvet.Syntax");
    lines.push("import Velvet.Std");
  }
  lines.push("");
  lines.push('set_option loom.semantics.termination "total"');
  lines.push('set_option loom.semantics.choice "demonic"');
  for (const fn of mod.functions) {
    lines.push("");
    lines.push(...generateFunction(fn));
  }
  return lines.join("\n") + "\n";
}
