/**
 * Spec expression parser and Lean emitter.
 *
 * Parses the //@ expression language (SPEC.md §3.2) and emits Lean 4 syntax.
 */

import type { TypeDeclInfo } from "./types.js";

// ── AST ──────────────────────────────────────────────────────

import type { RawExpr } from "./rawir.js";

// Re-export RawExpr as the parser's output type
export type Expr = RawExpr;

// ── Tokenizer ────────────────────────────────────────────────

type Token =
  | { type: "num"; value: number }
  | { type: "str"; value: string }
  | { type: "ident"; value: string }
  | { type: "op"; value: string }
  | { type: "punc"; value: string }
  | { type: "result"; value: undefined };

function tokenValue(t: Token): string | number | undefined {
  return t.value;
}

const MULTI_OPS = ["==>", "===", "!==", ">=", "<=", "&&", "||"];

function tokenize(input: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;
  while (i < input.length) {
    if (/\s/.test(input[i])) { i++; continue; }

    if (input[i] === "\\" && input.slice(i + 1, i + 7) === "result") {
      tokens.push({ type: "result", value: undefined });
      i += 7;
      continue;
    }

    // String literals (double or single quotes)
    if (input[i] === '"' || input[i] === "'") {
      const quote = input[i];
      i++;
      let s = "";
      while (i < input.length && input[i] !== quote) s += input[i++];
      if (i < input.length) i++;
      tokens.push({ type: "str", value: s });
      continue;
    }

    if (/[0-9]/.test(input[i])) {
      let n = "";
      while (i < input.length && /[0-9]/.test(input[i])) n += input[i++];
      tokens.push({ type: "num", value: parseInt(n) });
      continue;
    }

    if (/[a-zA-Z_]/.test(input[i])) {
      let id = "";
      while (i < input.length && /[a-zA-Z_0-9]/.test(input[i])) id += input[i++];
      tokens.push({ type: "ident", value: id });
      continue;
    }

    let matched = false;
    for (const op of MULTI_OPS) {
      if (input.slice(i, i + op.length) === op) {
        tokens.push({ type: "op", value: op });
        i += op.length;
        matched = true;
        break;
      }
    }
    if (matched) continue;

    const ch = input[i];
    if ("+-*/%><!".includes(ch)) {
      tokens.push({ type: "op", value: ch });
    } else if ("()[],:.{}".includes(ch)) {
      tokens.push({ type: "punc", value: ch });
    } else {
      throw new Error(`Unexpected '${ch}' at ${i} in: ${input}`);
    }
    i++;
  }
  return tokens;
}

// ── Parser ───────────────────────────────────────────────────

class Parser {
  pos = 0;
  constructor(private tokens: Token[]) {}

  peek() { return this.tokens[this.pos]; }
  advance() { return this.tokens[this.pos++]; }
  expect(type: string, value?: string) {
    const t = this.advance();
    if (!t || t.type !== type || (value !== undefined && t.value !== value))
      throw new Error(`Expected ${type}${value ? ` '${value}'` : ""}, got ${t ? JSON.stringify(t) : "EOF"}`);
    return t;
  }
  match(type: string, value?: string) {
    const t = this.peek();
    if (t && t.type === type && (value === undefined || t.value === value)) {
      this.pos++;
      return true;
    }
    return false;
  }

  parse(): Expr {
    const r = this.parseImplies();
    if (this.pos < this.tokens.length) throw new Error(`Unexpected: ${JSON.stringify(this.peek())}`);
    return r;
  }

  parseImplies(): Expr {
    const left = this.parseOr();
    if (this.match("op", "==>")) return { kind: "binop", op: "==>", left, right: this.parseImplies() };
    return left;
  }

  parseOr(): Expr {
    let left = this.parseAnd();
    while (this.match("op", "||")) left = { kind: "binop", op: "||", left, right: this.parseAnd() };
    return left;
  }

  parseAnd(): Expr {
    let left = this.parseCmp();
    while (this.match("op", "&&")) left = { kind: "binop", op: "&&", left, right: this.parseCmp() };
    return left;
  }

  parseCmp(): Expr {
    const left = this.parseAdd();
    const t = this.peek();
    if (t?.type === "op" && ["===", "!==", ">=", "<=", ">", "<"].includes(t.value)) {
      this.advance();
      return { kind: "binop", op: t.value, left, right: this.parseAdd() };
    }
    return left;
  }

  parseAdd(): Expr {
    let left = this.parseMul();
    while (this.peek()?.type === "op" && ["+", "-"].includes(this.peek()!.value as string)) {
      const op = this.advance().value as string;
      left = { kind: "binop", op, left, right: this.parseMul() };
    }
    return left;
  }

  parseMul(): Expr {
    let left = this.parseUnary();
    while (this.peek()?.type === "op" && ["*", "/", "%"].includes(this.peek()!.value as string)) {
      const op = this.advance().value as string;
      left = { kind: "binop", op, left, right: this.parseUnary() };
    }
    return left;
  }

  parseUnary(): Expr {
    if (this.match("op", "!")) return { kind: "unop", op: "!", expr: this.parseUnary() };
    if (this.peek()?.type === "op" && this.peek()!.value === "-") {
      const prev = this.pos > 0 ? this.tokens[this.pos - 1] : undefined;
      if (!prev || prev.type === "op" || (prev.type === "punc" && prev.value !== ")")) {
        this.advance();
        return { kind: "unop", op: "-", expr: this.parseUnary() };
      }
    }
    return this.parsePostfix();
  }

  parsePostfix(): Expr {
    let expr = this.parseAtom();
    while (true) {
      if (this.match("punc", ".")) {
        expr = { kind: "field", obj: expr, field: (this.expect("ident").value as string) };
      } else if (this.match("punc", "[")) {
        const idx = this.parseImplies();
        this.expect("punc", "]");
        expr = { kind: "index", obj: expr, idx };
      } else if (this.match("punc", "(")) {
        const args: Expr[] = [];
        if (!this.match("punc", ")")) {
          args.push(this.parseImplies());
          while (this.match("punc", ",")) args.push(this.parseImplies());
          this.expect("punc", ")");
        }
        expr = { kind: "call", fn: expr, args };
      } else break;
    }
    return expr;
  }

  parseAtom(): Expr {
    const t = this.peek();
    if (!t) throw new Error("Unexpected end of expression");
    if (t.type === "result") { this.advance(); return { kind: "result" }; }
    if (t.type === "num") { this.advance(); return { kind: "num", value: t.value }; }
    if (t.type === "str") { this.advance(); return { kind: "str", value: t.value }; }
    if (t.type === "ident") {
      if (t.value === "true") { this.advance(); return { kind: "bool", value: true }; }
      if (t.value === "false") { this.advance(); return { kind: "bool", value: false }; }
      if (t.value === "forall" || t.value === "exists") {
        const q = t.value as "forall" | "exists";
        this.advance();
        this.expect("punc", "(");
        const v = this.expect("ident").value as string;
        let varType: "nat" | "int" = "int";
        if (this.match("punc", ":")) {
          const ty = this.expect("ident").value as string;
          if (ty !== "nat" && ty !== "int") throw new Error(`Unknown type '${ty}'`);
          varType = ty;
        }
        this.expect("punc", ",");
        const body = this.parseImplies();
        this.expect("punc", ")");
        return { kind: q, var: v, varType, body };
      }
      this.advance();
      return { kind: "var", name: t.value };
    }
    if (t.type === "punc" && t.value === "(") {
      this.advance();
      const expr = this.parseImplies();
      this.expect("punc", ")");
      return expr;
    }
    // Object literal: { field: value, ... }
    if (t.type === "punc" && t.value === "{") {
      this.advance();
      const fields: { name: string; value: Expr }[] = [];
      if (!this.match("punc", "}")) {
        const name = this.expect("ident").value as string;
        this.expect("punc", ":");
        fields.push({ name, value: this.parseImplies() });
        while (this.match("punc", ",")) {
          const n = this.expect("ident").value as string;
          this.expect("punc", ":");
          fields.push({ name: n, value: this.parseImplies() });
        }
        this.expect("punc", "}");
      }
      return { kind: "record", fields };
    }
    throw new Error(`Unexpected: ${JSON.stringify(t)}`);
  }
}

// ── Lean emitter ─────────────────────────────────────────────

export interface EmitContext {
  arrayVars: Set<string>;
  natVars: Set<string>;
  resultVar?: string;
  /** Maps variable name → type name for user-defined types */
  userTypes: Map<string, string>;
  /** Type declarations for looking up constructors and fields */
  typeDecls: TypeDeclInfo[];
}

export function isNat(expr: Expr, ctx: EmitContext): boolean {
  switch (expr.kind) {
    case "num": return expr.value >= 0;
    case "var": return ctx.natVars.has(expr.name);
    case "field": return expr.field === "length" && expr.obj.kind === "var" && ctx.arrayVars.has(expr.obj.name);
    case "binop": return ["+", "-", "*", "/", "%"].includes(expr.op) && isNat(expr.left, ctx) && isNat(expr.right, ctx);
    default: return false;
  }
}

function findTypeDecl(ctx: EmitContext, typeName: string): TypeDeclInfo | undefined {
  return ctx.typeDecls.find(d => d.name === typeName);
}

function varTypeName(expr: Expr, ctx: EmitContext): string | undefined {
  if (expr.kind === "var") return ctx.userTypes.get(expr.name);
  if (expr.kind === "result" && ctx.resultVar) return ctx.userTypes.get("\\result");
  return undefined;
}

function splitConj(expr: Expr): Expr[] {
  if (expr.kind === "binop" && expr.op === "&&") return [...splitConj(expr.left), ...splitConj(expr.right)];
  return [expr];
}

function flattenImpl(expr: Expr): { premises: Expr[]; conclusion: Expr } {
  if (expr.kind === "binop" && expr.op === "==>") {
    const lhs = splitConj(expr.left);
    const rest = flattenImpl(expr.right);
    return { premises: [...lhs, ...rest.premises], conclusion: rest.conclusion };
  }
  return { premises: [], conclusion: expr };
}

function prec(op: string): number {
  const p: Record<string, number> = {
    "==>": 1, "||": 2, "&&": 3,
    "===": 4, "!==": 4, ">=": 4, "<=": 4, ">": 4, "<": 4,
    "+": 5, "-": 5, "*": 6, "/": 6, "%": 6,
  };
  return p[op] ?? 10;
}

function emit(expr: Expr, ctx: EmitContext, parentOp?: string): string {
  const e = (x: Expr, p?: string) => emit(x, ctx, p);

  switch (expr.kind) {
    case "num": return `${expr.value}`;
    case "bool": return expr.value ? "true" : "false";
    case "var": return expr.name;
    case "result":
      if (!ctx.resultVar) throw new Error("\\result is only valid in ensures");
      return ctx.resultVar;

    case "str": {
      // String literal → Lean constructor (.value) if in a typed context
      // The caller is responsible for context; here we just emit .value
      return `.${expr.value}`;
    }

    case "unop":
      if (expr.op === "!") return `¬(${e(expr.expr)})`;
      if (expr.op === "-") {
        if (expr.expr.kind === "num") return `-${expr.expr.value}`;
        return `(-${e(expr.expr)})`;
      }
      return `(${expr.op} ${e(expr.expr)})`;

    case "binop": {
      if (expr.op === "==>") {
        const { premises, conclusion } = flattenImpl(expr);
        const r = [...premises.map(p => e(p)), e(conclusion)].join(" → ");
        return parentOp ? `(${r})` : r;
      }

      // Comparison with string literal → constructor equality
      if ((expr.op === "===" || expr.op === "!==") && expr.right.kind === "str") {
        const lhs = e(expr.left);
        const rhs = `.${expr.right.value}`;
        const op = expr.op === "===" ? "=" : "≠";
        const r = `${lhs} ${op} ${rhs}`;
        return parentOp ? `(${r})` : r;
      }

      // Property access on discriminant (x.tag === "foo") → constructor equality
      if ((expr.op === "===" || expr.op === "!==") &&
          expr.left.kind === "field" && expr.right.kind === "str") {
        const varExpr = expr.left.obj;
        const typeName = varTypeName(varExpr, ctx);
        const decl = typeName ? findTypeDecl(ctx, typeName) : undefined;
        if (decl && decl.discriminant === expr.left.field) {
          const lhs = e(varExpr);
          const op = expr.op === "===" ? "=" : "≠";
          // For data-free variant, just .name. For data variant, need to handle differently.
          const strVal = (expr.right as { kind: "str"; value: string }).value;
          const variant = decl.variants?.find(v => v.name === strVal);
          if (variant && variant.fields.length === 0) {
            const r = `${lhs} ${op} .${strVal}`;
            return parentOp ? `(${r})` : r;
          }
          // Data-carrying variant: can't use simple equality. This will be handled by match.
          // For now, emit a comment indicating the pattern.
        }
      }

      const ops: Record<string, string> = {
        "===": "=", "!==": "≠", ">=": "≥", "<=": "≤", ">": ">", "<": "<",
        "&&": "∧", "||": "∨", "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
      };
      const r = `${e(expr.left, expr.op)} ${ops[expr.op] ?? expr.op} ${e(expr.right, expr.op)}`;
      return (parentOp && prec(expr.op) < prec(parentOp)) ? `(${r})` : r;
    }

    case "field": {
      if (expr.field === "length" && expr.obj.kind === "var" && ctx.arrayVars.has(expr.obj.name))
        return `${e(expr.obj)}.size`;
      const obj = e(expr.obj);
      const atomic = expr.obj.kind === "var" || expr.obj.kind === "num" || expr.obj.kind === "bool";
      return atomic ? `${obj}.${expr.field}` : `(${obj}).${expr.field}`;
    }

    case "index": {
      if (expr.obj.kind === "var" && ctx.arrayVars.has(expr.obj.name)) {
        const idx = e(expr.idx);
        return isNat(expr.idx, ctx) ? `${e(expr.obj)}[${idx}]!` : `${e(expr.obj)}[${idx}.toNat]!`;
      }
      return `${e(expr.obj)}[${e(expr.idx)}]`;
    }

    case "call": {
      if (expr.fn.kind === "field" && expr.fn.field === "floor" &&
          expr.fn.obj.kind === "var" && expr.fn.obj.name === "Math" && expr.args.length === 1)
        return e(expr.args[0]);
      const fn = expr.fn.kind === "var" ? expr.fn.name : e(expr.fn);
      const args = expr.args.map(a => {
        const s = e(a);
        return (a.kind === "binop" || a.kind === "unop") ? `(${s})` : s;
      });
      return `${fn} ${args.join(" ")}`;
    }

    case "record": {
      const fields = expr.fields.map(f => `${f.name} := ${e(f.value)}`).join(", ");
      return `{ ${fields} }`;
    }

    case "forall":
    case "exists": {
      const sym = expr.kind === "forall" ? "∀" : "∃";
      const ty = expr.varType === "nat" ? "Nat" : "Int";
      const bodyCtx = expr.varType === "nat"
        ? { ...ctx, natVars: new Set([...ctx.natVars, expr.var]) }
        : ctx;
      return `${sym} ${expr.var} : ${ty}, ${emit(expr.body, bodyCtx)}`;
    }
  }
}

// ── Public API ───────────────────────────────────────────────

export function parseExpr(input: string): Expr {
  return new Parser(tokenize(input)).parse();
}

export function exprToLean(input: string, ctx: EmitContext): string {
  return emit(parseExpr(input), ctx);
}

export function specToClauses(input: string, ctx: EmitContext): string[] {
  return splitConj(parseExpr(input)).map(e => emit(e, ctx));
}
