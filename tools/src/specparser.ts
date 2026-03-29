/**
 * LemmaScript spec expression parser
 *
 * Parses the TS-flavored expression language used in //@ annotations
 * and computational expressions, and emits Lean 4 syntax.
 *
 * Grammar (precedence low→high):
 *   expr     := implies
 *   implies  := or ('==>' implies)?
 *   or       := and ('||' and)*
 *   and      := compare ('&&' compare)*
 *   compare  := add (cmpOp add)?
 *   add      := mul (('+' | '-') mul)*
 *   mul      := unary (('*' | '/' | '%') unary)*
 *   unary    := '!' unary | '-' unary | postfix
 *   postfix  := atom ('.' ident | '[' expr ']' | '(' args ')')*
 *   atom     := NUM | IDENT | 'true' | 'false' | 'result'
 *             | 'forall' '(' IDENT (':' TYPE)? ',' expr ')'
 *             | 'exists' '(' IDENT (':' TYPE)? ',' expr ')'
 *             | '(' expr ')'
 *   TYPE     := 'nat' | 'int'
 */

// ── AST ──────────────────────────────────────────────────────

export type LeanType = "nat" | "int";

export type Expr =
  | { kind: "num"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "var"; name: string }
  | { kind: "binop"; op: string; left: Expr; right: Expr }
  | { kind: "unop"; op: string; expr: Expr }
  | { kind: "call"; fn: Expr; args: Expr[] }
  | { kind: "index"; obj: Expr; idx: Expr }
  | { kind: "prop"; obj: Expr; prop: string }
  | { kind: "forall"; var: string; varType: LeanType; body: Expr }
  | { kind: "exists"; var: string; varType: LeanType; body: Expr };

// ── Tokenizer ────────────────────────────────────────────────

type Token =
  | { type: "num"; value: number }
  | { type: "ident"; value: string }
  | { type: "op"; value: string }
  | { type: "punc"; value: string };

const MULTI_CHAR_OPS = ["==>", "===", "!==", ">=", "<=", "&&", "||"];

function tokenize(input: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;

  while (i < input.length) {
    if (/\s/.test(input[i])) { i++; continue; }

    if (/[0-9]/.test(input[i])) {
      let num = "";
      while (i < input.length && /[0-9]/.test(input[i])) num += input[i++];
      tokens.push({ type: "num", value: parseInt(num) });
      continue;
    }

    if (/[a-zA-Z_]/.test(input[i])) {
      let id = "";
      while (i < input.length && /[a-zA-Z_0-9]/.test(input[i])) id += input[i++];
      tokens.push({ type: "ident", value: id });
      continue;
    }

    let matched = false;
    for (const op of MULTI_CHAR_OPS) {
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
      i++;
    } else if ("()[],.:" .includes(ch)) {
      tokens.push({ type: "punc", value: ch });
      i++;
    } else {
      throw new Error(`Unexpected character '${ch}' at position ${i} in: ${input}`);
    }
  }

  return tokens;
}

// ── Parser ───────────────────────────────────────────────────

class Parser {
  private pos = 0;
  constructor(private tokens: Token[]) {}

  private peek(): Token | undefined { return this.tokens[this.pos]; }
  private advance(): Token { return this.tokens[this.pos++]; }

  private expect(type: string, value?: string): Token {
    const t = this.advance();
    if (!t || t.type !== type || (value !== undefined && (t as any).value !== value))
      throw new Error(`Expected ${type}${value ? ` '${value}'` : ""}, got ${t ? `${t.type} '${(t as any).value}'` : "EOF"}`);
    return t;
  }

  private match(type: string, value?: string): boolean {
    const t = this.peek();
    if (t && t.type === type && (value === undefined || (t as any).value === value)) {
      this.pos++;
      return true;
    }
    return false;
  }

  parse(): Expr {
    const result = this.parseImplies();
    if (this.pos < this.tokens.length)
      throw new Error(`Unexpected token at end: ${JSON.stringify(this.peek())}`);
    return result;
  }

  private parseImplies(): Expr {
    const left = this.parseOr();
    if (this.match("op", "==>")) {
      const right = this.parseImplies();
      return { kind: "binop", op: "==>", left, right };
    }
    return left;
  }

  private parseOr(): Expr {
    let left = this.parseAnd();
    while (this.match("op", "||")) {
      const right = this.parseAnd();
      left = { kind: "binop", op: "||", left, right };
    }
    return left;
  }

  private parseAnd(): Expr {
    let left = this.parseCompare();
    while (this.match("op", "&&")) {
      const right = this.parseCompare();
      left = { kind: "binop", op: "&&", left, right };
    }
    return left;
  }

  private parseCompare(): Expr {
    const left = this.parseAdd();
    const t = this.peek();
    if (t?.type === "op" && ["===", "!==", ">=", "<=", ">", "<"].includes(t.value)) {
      this.advance();
      const right = this.parseAdd();
      return { kind: "binop", op: t.value, left, right };
    }
    return left;
  }

  private parseAdd(): Expr {
    let left = this.parseMul();
    while (this.peek()?.type === "op" && ["+", "-"].includes(this.peek()!.value)) {
      const op = this.advance().value;
      const right = this.parseMul();
      left = { kind: "binop", op, left, right };
    }
    return left;
  }

  private parseMul(): Expr {
    let left = this.parseUnary();
    while (this.peek()?.type === "op" && ["*", "/", "%"].includes(this.peek()!.value)) {
      const op = this.advance().value;
      const right = this.parseUnary();
      left = { kind: "binop", op, left, right };
    }
    return left;
  }

  private parseUnary(): Expr {
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

  private parsePostfix(): Expr {
    let expr = this.parseAtom();
    while (true) {
      if (this.match("punc", ".")) {
        const prop = this.expect("ident").value as string;
        expr = { kind: "prop", obj: expr, prop };
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

  private parseAtom(): Expr {
    const t = this.peek();
    if (!t) throw new Error("Unexpected end of expression");

    if (t.type === "num") { this.advance(); return { kind: "num", value: t.value }; }

    if (t.type === "ident") {
      if (t.value === "true") { this.advance(); return { kind: "bool", value: true }; }
      if (t.value === "false") { this.advance(); return { kind: "bool", value: false }; }

      // forall(k, body) or forall(k: nat, body)
      if (t.value === "forall" || t.value === "exists") {
        const q = t.value;
        this.advance();
        this.expect("punc", "(");
        const v = this.expect("ident").value as string;
        let varType: LeanType = "int"; // default
        if (this.match("punc", ":")) {
          const ty = this.expect("ident").value as string;
          if (ty === "nat") varType = "nat";
          else if (ty !== "int") throw new Error(`Unknown type '${ty}', expected 'nat' or 'int'`);
        }
        this.expect("punc", ",");
        const body = this.parseImplies();
        this.expect("punc", ")");
        return { kind: q as "forall" | "exists", var: v, varType, body };
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

    throw new Error(`Unexpected token: ${JSON.stringify(t)}`);
  }
}

// ── Lean emitter ─────────────────────────────────────────────

export interface EmitContext {
  arrayVars: Set<string>;
  natVars: Set<string>;
  resultVar: string;
}

const defaultContext: EmitContext = {
  arrayVars: new Set(),
  natVars: new Set(),
  resultVar: "result",
};

/** Is this expression Nat-typed given the context? */
export function isNat(expr: Expr, ctx: EmitContext): boolean {
  switch (expr.kind) {
    case "num": return expr.value >= 0;
    case "var": return ctx.natVars.has(expr.name);
    case "prop": return expr.prop === "length" && isArrayExpr(expr.obj, ctx); // arr.size is Nat
    case "binop":
      if (["+", "-", "*", "/", "%"].includes(expr.op))
        return isNat(expr.left, ctx) && isNat(expr.right, ctx);
      return false;
    case "unop": return false; // -x is Int
    case "call": return false; // conservative
    default: return false;
  }
}

function isArrayExpr(expr: Expr, ctx: EmitContext): boolean {
  return expr.kind === "var" && ctx.arrayVars.has(expr.name);
}

export function splitConjuncts(expr: Expr): Expr[] {
  if (expr.kind === "binop" && expr.op === "&&") {
    return [...splitConjuncts(expr.left), ...splitConjuncts(expr.right)];
  }
  return [expr];
}

function flattenImplication(expr: Expr): { premises: Expr[]; conclusion: Expr } {
  if (expr.kind === "binop" && expr.op === "==>") {
    const lhsParts = splitConjuncts(expr.left);
    const rest = flattenImplication(expr.right);
    return { premises: [...lhsParts, ...rest.premises], conclusion: rest.conclusion };
  }
  return { premises: [], conclusion: expr };
}

function needsParens(expr: Expr, parentOp?: string): boolean {
  if (expr.kind !== "binop") return false;
  const prec: Record<string, number> = {
    "==>": 1, "||": 2, "&&": 3,
    "===": 4, "!==": 4, ">=": 4, "<=": 4, ">": 4, "<": 4,
    "+": 5, "-": 5, "*": 6, "/": 6, "%": 6,
  };
  if (!parentOp) return false;
  return (prec[expr.op] ?? 10) < (prec[parentOp] ?? 10);
}

function emitLean(expr: Expr, ctx: EmitContext, parentOp?: string): string {
  const emit = (e: Expr, pOp?: string) => emitLean(e, ctx, pOp);

  switch (expr.kind) {
    case "num":
      return expr.value < 0 ? `(${expr.value})` : `${expr.value}`;

    case "bool":
      return expr.value ? "True" : "False";

    case "var":
      if (expr.name === "result") return ctx.resultVar;
      return expr.name;

    case "unop":
      if (expr.op === "!") return `¬${emit(expr.expr)}`;
      if (expr.op === "-") {
        if (expr.expr.kind === "num") return `-${expr.expr.value}`;
        return `(-${emit(expr.expr)})`;
      }
      return `(${expr.op} ${emit(expr.expr)})`;

    case "binop": {
      if (expr.op === "==>") {
        const { premises, conclusion } = flattenImplication(expr);
        const parts = [...premises.map(p => emit(p)), emit(conclusion)];
        const result = parts.join(" → ");
        return parentOp ? `(${result})` : result;
      }

      const opMap: Record<string, string> = {
        "===": "=", "!==": "≠", ">=": "≥", "<=": "≤",
        "&&": "∧", "||": "∨",
        "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
        ">": ">", "<": "<",
      };
      const leanOp = opMap[expr.op] ?? expr.op;
      const result = `${emit(expr.left, expr.op)} ${leanOp} ${emit(expr.right, expr.op)}`;
      return needsParens(expr, parentOp) ? `(${result})` : result;
    }

    case "prop":
      if (expr.prop === "length" && isArrayExpr(expr.obj, ctx)) {
        return `${emit(expr.obj)}.size`;
      }
      return `${emit(expr.obj)}.${expr.prop}`;

    case "index": {
      if (isArrayExpr(expr.obj, ctx)) {
        const idx = emit(expr.idx);
        // Nat index: arr[i]!  Int index: arr[i.toNat]!
        return isNat(expr.idx, ctx) ? `${emit(expr.obj)}[${idx}]!` : `${emit(expr.obj)}[${idx}.toNat]!`;
      }
      return `${emit(expr.obj)}[${emit(expr.idx)}]`;
    }

    case "call": {
      if (expr.fn.kind === "prop" && expr.fn.prop === "floor" &&
          expr.fn.obj.kind === "var" && expr.fn.obj.name === "Math" &&
          expr.args.length === 1) {
        return emit(expr.args[0]);
      }
      const fnName = expr.fn.kind === "var" ? expr.fn.name : emit(expr.fn);
      const leanArgs = expr.args.map(a => {
        const s = emit(a);
        return a.kind === "binop" || a.kind === "unop" ? `(${s})` : s;
      });
      return `${fnName} ${leanArgs.join(" ")}`;
    }

    case "forall": {
      const leanType = expr.varType === "nat" ? "Nat" : "Int";
      // Add quantified variable to natVars for body emission
      const bodyCtx = expr.varType === "nat"
        ? { ...ctx, natVars: new Set([...ctx.natVars, expr.var]) }
        : ctx;
      return `∀ ${expr.var} : ${leanType}, ${emitLean(expr.body, bodyCtx)}`;
    }

    case "exists": {
      const leanType = expr.varType === "nat" ? "Nat" : "Int";
      const bodyCtx = expr.varType === "nat"
        ? { ...ctx, natVars: new Set([...ctx.natVars, expr.var]) }
        : ctx;
      return `∃ ${expr.var} : ${leanType}, ${emitLean(expr.body, bodyCtx)}`;
    }
  }
}

// ── Public API ───────────────────────────────────────────────

export function parseExpr(input: string): Expr {
  return new Parser(tokenize(input)).parse();
}

export function exprToLean(input: string, ctx?: Partial<EmitContext>): string {
  return emitLean(parseExpr(input), { ...defaultContext, ...ctx });
}

export function astToLean(expr: Expr, ctx?: Partial<EmitContext>): string {
  return emitLean(expr, { ...defaultContext, ...ctx });
}

export function specToClauses(input: string, ctx?: Partial<EmitContext>): string[] {
  const fullCtx = { ...defaultContext, ...ctx };
  return splitConjuncts(parseExpr(input)).map(e => emitLean(e, fullCtx));
}
