/**
 * Code generator — IR → .types.lean + .def.lean
 *
 * Produces Velvet `method` definitions. Translation is mechanical per SPEC.md.
 */

import { exprToLean, specToClauses, parseExpr, isNat, type EmitContext } from "./specparser.js";
import { tsTypeToLean, isNatType, isArrayType, generateTypesLean, type TypeDeclInfo } from "./types.js";
import type { ModuleSpec, FunctionSpec, StmtSpec, IfSpec, SwitchSpec } from "./extract.js";

// ── Context ──────────────────────────────────────────────────

function makeCtx(fn: FunctionSpec, typeDecls: TypeDeclInfo[]): EmitContext {
  const arrayVars = new Set<string>();
  const userTypes = new Map<string, string>();

  for (const p of fn.params) {
    const leanType = resolveVarType(p.name, p.type, fn.typeAnnotations);
    if (isArrayType(leanType)) arrayVars.add(p.name);
    if (!isPrimitive(p.type)) userTypes.set(p.name, tsTypeToLean(p.type));
  }

  // Return type for \result
  if (!isPrimitive(fn.returnType)) {
    userTypes.set("\\result", tsTypeToLean(fn.returnType));
  }

  const natVars = new Set(fn.typeAnnotations.filter(t => t.type === "nat").map(t => t.name));
  return { arrayVars, natVars, userTypes, typeDecls };
}

function ensuresCtx(fn: FunctionSpec, typeDecls: TypeDeclInfo[]): EmitContext {
  return { ...makeCtx(fn, typeDecls), resultVar: "res" };
}

function resolveVarType(name: string, tsType: string, annotations: { name: string; type: string }[]): string {
  const override = annotations.find(a => a.name === name);
  if (override) return override.type === "nat" ? "Nat" : override.type;
  return tsTypeToLean(tsType);
}

function isPrimitive(tsType: string): boolean {
  return ["number", "boolean", "string", "void", "undefined"].includes(tsType.trim());
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

function hasReturnInLoop(stmts: StmtSpec[]): boolean {
  for (const s of stmts) {
    if (s.kind === "while" && containsReturn(s.body)) return true;
  }
  return false;
}

// ── Discriminant if-chain detection ──────────────────────────

interface DiscriminantChain {
  varName: string;
  discriminant: string;
  typeName: string;
  cases: { variant: string; body: StmtSpec[] }[];
  fallthrough: StmtSpec[];
}

/**
 * Detect a sequence of if statements that form a discriminant dispatch.
 * Pattern: if (x.tag === "a") ... if (x.tag === "b") ... return default;
 * Returns null if the pattern doesn't match.
 */
function detectDiscriminantChain(stmts: StmtSpec[], ctx: EmitContext): { chain: DiscriminantChain; consumed: number } | null {
  if (stmts.length === 0) return null;
  const first = stmts[0];
  if (first.kind !== "if") return null;

  // Parse condition: x.field === "literal" or x === "literal"
  const parsed = parseDiscriminantCondition(first.condition, ctx);
  if (!parsed) return null;

  const { varName, field, typeName } = parsed;
  const cases: { variant: string; body: StmtSpec[] }[] = [];
  let consumed = 0;

  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    if (s.kind !== "if") break;

    const p = parseDiscriminantCondition(s.condition, ctx);
    if (!p || p.varName !== varName || p.field !== field) break;

    cases.push({ variant: p.literal, body: s.then });
    consumed = i + 1;

    // If there's an else, it might be another if (else-if chain) or the fallthrough
    if (s.else.length > 0) {
      if (s.else.length === 1 && s.else[0].kind === "if") {
        // Flatten else-if: pretend the else-if is the next statement
        const elseIf = s.else[0] as IfSpec;
        const ep = parseDiscriminantCondition(elseIf.condition, ctx);
        if (ep && ep.varName === varName && ep.field === field) {
          cases.push({ variant: ep.literal, body: elseIf.then });
          // Continue with elseIf's else
          if (elseIf.else.length > 0) {
            return { chain: { varName, discriminant: field, typeName, cases, fallthrough: elseIf.else }, consumed };
          }
        }
      }
      return { chain: { varName, discriminant: field, typeName, cases, fallthrough: s.else }, consumed };
    }
  }

  // Remaining statements after the if-chain are fallthrough
  const fallthrough = stmts.slice(consumed);
  return cases.length > 0 ? { chain: { varName, discriminant: field, typeName, cases, fallthrough }, consumed: stmts.length } : null;
}

interface ParsedCondition { varName: string; field: string; literal: string; typeName: string }

function parseDiscriminantCondition(condition: string, ctx: EmitContext): ParsedCondition | null {
  // Match: x.field === "literal" or x === "literal"
  const m1 = condition.match(/^(\w+)\.(\w+)\s*===\s*"(\w+)"$/);
  if (m1) {
    const [, varName, field, literal] = m1;
    const typeName = ctx.userTypes.get(varName);
    if (typeName) {
      const decl = ctx.typeDecls.find(d => d.name === typeName);
      if (decl && decl.kind === "discriminated-union" && decl.discriminant === field) {
        return { varName, field, literal, typeName };
      }
    }
  }
  // String-unions use if with DecidableEq, not match. No detection needed.
  return null;
}

// ── Body emission ────────────────────────────────────────────

function emitBody(stmts: StmtSpec[], ctx: EmitContext, natNames: Set<string>, typeDecls: TypeDeclInfo[]): string[] {
  const lines: string[] = [];
  let i = 0;

  while (i < stmts.length) {
    const s = stmts[i];

    // Try to detect discriminant if-chain
    if (s.kind === "if") {
      const chain = detectDiscriminantChain(stmts.slice(i), ctx);
      if (chain) {
        lines.push(...emitMatch(chain.chain, ctx, natNames, typeDecls));
        i += chain.consumed;
        continue;
      }
    }

    lines.push(...emitStmt(s, ctx, natNames, typeDecls));
    i++;
  }

  return lines;
}

function emitStmt(s: StmtSpec, ctx: EmitContext, natNames: Set<string>, typeDecls: TypeDeclInfo[]): string[] {
  const lines: string[] = [];

  switch (s.kind) {
    case "let": {
      const nat = natNames.has(s.name);
      const ty = nat ? "Nat" : tsTypeToLean(s.type);
      const init = exprToLean(s.init, ctx);
      // Track user-defined types for variables declared in the body
      if (!isPrimitive(s.type)) ctx.userTypes.set(s.name, tsTypeToLean(s.type));
      lines.push(s.mutable ? `let mut ${s.name} : ${ty} := ${init}` : `let ${s.name} := ${init}`);
      break;
    }
    case "assign": {
      const value = exprToLean(s.value, ctx);
      // Method call detection: target = f(args) where f is a known method
      if (isMethodCall(s.value)) {
        lines.push(`${s.target} ← ${value}`);
      } else {
        lines.push(`${s.target} := ${value}`);
      }
      break;
    }
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
      for (const bl of emitBody(s.body, ctx, natNames, typeDecls)) lines.push(`  ${bl}`);
      break;
    }

    case "if": {
      lines.push(`if ${exprToLean(s.condition, ctx)} then`);
      for (const tl of emitBody(s.then, ctx, natNames, typeDecls)) lines.push(`  ${tl}`);
      if (s.else.length > 0) {
        if (s.else.length === 1 && s.else[0].kind === "if") {
          const ei = s.else[0] as IfSpec;
          lines.push(`else if ${exprToLean(ei.condition, ctx)} then`);
          for (const el of emitBody(ei.then, ctx, natNames, typeDecls)) lines.push(`  ${el}`);
          if (ei.else.length > 0) {
            lines.push("else");
            for (const el of emitBody(ei.else, ctx, natNames, typeDecls)) lines.push(`  ${el}`);
          }
        } else {
          lines.push("else");
          for (const el of emitBody(s.else, ctx, natNames, typeDecls)) lines.push(`  ${el}`);
        }
      }
      break;
    }

    case "switch":
      lines.push(...emitSwitchAsMatch(s, ctx, natNames, typeDecls));
      break;
  }

  return lines;
}

/** Emit a detected discriminant if-chain as a Lean match. */
function emitMatch(chain: DiscriminantChain, ctx: EmitContext, natNames: Set<string>, typeDecls: TypeDeclInfo[]): string[] {
  const lines: string[] = [];
  const decl = typeDecls.find(d => d.name === chain.typeName);

  lines.push(`match ${chain.varName} with`);
  for (const c of chain.cases) {
    const variant = decl?.variants?.find(v => v.name === c.variant);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0
      ? `.${c.variant} ${fields.map(f => f.name).join(" ")}`
      : `.${c.variant}`;

    // Create a context where field accesses on the matched variable resolve to bound names
    const branchCtx = { ...ctx };
    lines.push(`| ${pattern} =>`);
    const bodyLines = emitBody(c.body, branchCtx, natNames, typeDecls);
    // Replace x.field with the bound variable name in body
    for (let bl of bodyLines) {
      for (const f of fields) {
        bl = bl.replaceAll(`${chain.varName}.${f.name}`, f.name);
      }
      lines.push(`  ${bl}`);
    }
  }

  if (chain.fallthrough.length > 0) {
    lines.push("| _ =>");
    for (const bl of emitBody(chain.fallthrough, ctx, natNames, typeDecls)) lines.push(`  ${bl}`);
  }

  return lines;
}

/** Emit a switch statement as a Lean match. */
function emitSwitchAsMatch(s: SwitchSpec, ctx: EmitContext, natNames: Set<string>, typeDecls: TypeDeclInfo[]): string[] {
  const lines: string[] = [];
  const typeName = ctx.userTypes.get(s.expr);
  const decl = typeName ? typeDecls.find(d => d.name === typeName) : undefined;

  lines.push(`match ${s.expr} with`);
  for (const c of s.cases) {
    const variant = decl?.variants?.find(v => v.name === c.label);
    const fields = variant?.fields ?? [];
    const pattern = fields.length > 0
      ? `.${c.label} ${fields.map(f => f.name).join(" ")}`
      : `.${c.label}`;
    lines.push(`| ${pattern} =>`);
    for (let bl of emitBody(c.body, ctx, natNames, typeDecls)) {
      for (const f of fields) {
        bl = bl.replaceAll(`${s.expr}.${f.name}`, f.name);
      }
      lines.push(`  ${bl}`);
    }
  }
  if (s.defaultBody.length > 0) {
    lines.push("| _ =>");
    for (const bl of emitBody(s.defaultBody, ctx, natNames, typeDecls)) lines.push(`  ${bl}`);
  }

  return lines;
}

/** Heuristic: is this value a function call (x(...))? */
function isMethodCall(value: string): boolean {
  // Match patterns like: transition(state, events[i]) or f(x, y)
  return /^\w+\(.*\)$/.test(value.trim());
}

// ── Ensures-to-match translation ─────────────────────────────

/**
 * Translate ensures like `pkt.tag === "syn" ==> \result === pkt.seq`
 * into `match pkt with | .syn seq => res = seq | _ => True`.
 *
 * Returns the Lean string, or null if the ensures is not a discriminant pattern.
 */
function ensuresToMatch(ensuresStr: string, ctx: EmitContext): string | null {
  const ast = parseExpr(ensuresStr);

  // Must be an implication: LHS ==> RHS
  if (ast.kind !== "binop" || ast.op !== "==>") return null;

  // LHS must be x.discriminant === "variant"
  const lhs = ast.left;
  if (lhs.kind !== "binop" || lhs.op !== "===") return null;
  if (lhs.left.kind !== "prop" || lhs.right.kind !== "str") return null;

  const varExpr = lhs.left.obj;
  if (varExpr.kind !== "var") return null;
  const varName = varExpr.name;
  const field = lhs.left.prop;
  const variant = lhs.right.value;

  const typeName = ctx.userTypes.get(varName);
  if (!typeName) return null;
  const decl = ctx.typeDecls.find(d => d.name === typeName);
  if (!decl || decl.kind !== "discriminated-union" || decl.discriminant !== field) return null;

  const variantInfo = decl.variants?.find(v => v.name === variant);
  if (!variantInfo) return null;

  // Build the match pattern with field bindings
  const fields = variantInfo.fields;
  const pattern = fields.length > 0
    ? `.${variant} ${fields.map(f => f.name).join(" ")}`
    : `.${variant}`;

  // Translate RHS to Lean, then replace x.fieldName with the bound variable
  let rhs = exprToLean(ensuresStr.slice(ensuresStr.indexOf("==>") + 3).trim(), ctx);
  for (const f of fields) {
    rhs = rhs.replaceAll(`${varName}.${f.name}`, f.name);
  }

  return `match ${varName} with | ${pattern} => ${rhs} | _ => True`;
}

// ── Function generation ──────────────────────────────────────

function generateFunction(fn: FunctionSpec, typeDecls: TypeDeclInfo[]): string[] {
  if (hasReturnInLoop(fn.body)) {
    throw new Error(
      `${fn.name}: return inside a loop is not supported. ` +
      `Restructure to use break + a result variable (SPEC.md §5.3).`
    );
  }

  const lines: string[] = [];
  const ctx = makeCtx(fn, typeDecls);
  const eCtx = ensuresCtx(fn, typeDecls);
  const natNames = new Set(fn.typeAnnotations.filter(t => t.type === "nat").map(t => t.name));

  const params = fn.params.map(p => {
    const ty = resolveVarType(p.name, p.type, fn.typeAnnotations);
    return `(${p.name} : ${ty})`;
  }).join(" ");
  const retType = resolveVarType("\\result", fn.returnType, fn.typeAnnotations);

  lines.push(`method ${fn.name} ${params} return (res : ${retType})`);
  for (const r of fn.requires) for (const c of specToClauses(r, ctx)) lines.push(`  require ${c}`);
  for (const e of fn.ensures) {
    const matchForm = ensuresToMatch(e, eCtx);
    if (matchForm) {
      lines.push(`  ensures ${matchForm}`);
    } else {
      for (const c of specToClauses(e, eCtx)) lines.push(`  ensures ${c}`);
    }
  }
  lines.push("  do");
  for (const bl of emitBody(fn.body, ctx, natNames, typeDecls)) lines.push(`    ${bl}`);

  return lines;
}

// ── Module generation ────────────────────────────────────────

export function generateDef(mod: ModuleSpec, specImport?: string, typesImport?: string): string {
  const lines: string[] = [];
  lines.push("/-");
  lines.push(`  Generated by lsc from ${mod.file.split("/").pop()}`);
  lines.push("  Do not edit — re-run \\`lsc gen\\` to regenerate.");
  lines.push("-/");
  if (specImport) {
    lines.push(`import ${specImport}`);
  } else if (typesImport) {
    lines.push(`import ${typesImport}`);
  } else {
    lines.push("import Velvet.Syntax");
    lines.push("import Velvet.Std");
  }
  lines.push("");
  lines.push('set_option loom.semantics.termination "total"');
  lines.push('set_option loom.semantics.choice "demonic"');
  for (const fn of mod.functions) {
    lines.push("");
    lines.push(...generateFunction(fn, mod.typeDecls));
  }
  return lines.join("\n") + "\n";
}
