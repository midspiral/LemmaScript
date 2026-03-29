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
 *             | 'forall' '(' IDENT ',' expr ')'
 *             | 'exists' '(' IDENT ',' expr ')'
 *             | '(' expr ')'
 */

// ── AST ──────────────────────────────────────────────────────

export type Expr =
  | { kind: "num"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "var"; name: string }
  | { kind: "binop"; op: string; left: Expr; right: Expr }
  | { kind: "unop"; op: string; expr: Expr }
  | { kind: "call"; fn: Expr; args: Expr[] }
  | { kind: "index"; obj: Expr; idx: Expr }
  | { kind: "prop"; obj: Expr; prop: string }
  | { kind: "forall"; var: string; body: Expr }
  | { kind: "exists"; var: string; body: Expr };

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
    // Skip whitespace
    if (/\s/.test(input[i])) { i++; continue; }

    // Number
    if (/[0-9]/.test(input[i])) {
      let num = "";
      while (i < input.length && /[0-9]/.test(input[i])) num += input[i++];
      tokens.push({ type: "num", value: parseInt(num) });
      continue;
    }

    // Identifier / keyword
    if (/[a-zA-Z_]/.test(input[i])) {
      let id = "";
      while (i < input.length && /[a-zA-Z_0-9]/.test(input[i])) id += input[i++];
      tokens.push({ type: "ident", value: id });
      continue;
    }

    // Multi-char operators
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

    // Single-char operators and punctuation
    const ch = input[i];
    if ("+-*/%><!".includes(ch)) {
      tokens.push({ type: "op", value: ch });
      i++;
    } else if ("()[],.".includes(ch)) {
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
      const right = this.parseImplies(); // right-associative
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
      // Only treat as unary minus if not after a number/ident/close-paren
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
        // Function call — only if expr looks callable
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

      if (t.value === "forall" || t.value === "exists") {
        const q = t.value;
        this.advance();
        this.expect("punc", "(");
        const v = this.expect("ident").value as string;
        this.expect("punc", ",");
        const body = this.parseImplies();
        this.expect("punc", ")");
        return { kind: q as "forall" | "exists", var: v, body };
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

interface EmitContext {
  /** Variables known to be arrays (for .length and [i] translation) */
  arrayVars: Set<string>;
  /** Replace 'result' with this name (e.g., 'res' for Velvet ensures) */
  resultVar: string;
  /** Are we inside a spec context? (affects quantifier output) */
  isSpec: boolean;
}

const defaultContext: EmitContext = {
  arrayVars: new Set(),
  resultVar: "result",
  isSpec: false,
};

/**
 * Flatten a conjunction into its conjuncts (for splitting && into separate clauses).
 */
export function splitConjuncts(expr: Expr): Expr[] {
  if (expr.kind === "binop" && expr.op === "&&") {
    return [...splitConjuncts(expr.left), ...splitConjuncts(expr.right)];
  }
  return [expr];
}

/**
 * Flatten the LHS of an implication: (A && B) ==> C → [A, B, C] as chained →
 * Returns premises and conclusion separately for curried Lean output.
 */
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
        // Negative literal: emit as -N without parens
        if (expr.expr.kind === "num") return `-${expr.expr.value}`;
        return `(-${emit(expr.expr)})`;
      }
      return `(${expr.op} ${emit(expr.expr)})`;

    case "binop": {
      // Implication with curried LHS
      if (expr.op === "==>") {
        const { premises, conclusion } = flattenImplication(expr);
        const parts = [...premises.map(p => emit(p)), emit(conclusion)];
        const result = parts.join(" → ");
        return parentOp ? `(${result})` : result;
      }

      // Normalize >= to ≤ and > to < (flip operands).
      // loom_solve handles ≤ and < but not ≥ and >.
      if (expr.op === ">=") {
        const result = `${emit(expr.right, "<=")} ≤ ${emit(expr.left, "<=")}`;
        return needsParens(expr, parentOp) ? `(${result})` : result;
      }
      if (expr.op === ">") {
        const result = `${emit(expr.right, "<")} < ${emit(expr.left, "<")}`;
        return needsParens(expr, parentOp) ? `(${result})` : result;
      }

      const opMap: Record<string, string> = {
        "===": "=", "!==": "≠", "<=": "≤",
        "&&": "∧", "||": "∨",
        "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
        "<": "<",
      };
      const leanOp = opMap[expr.op] ?? expr.op;
      const result = `${emit(expr.left, expr.op)} ${leanOp} ${emit(expr.right, expr.op)}`;
      return needsParens(expr, parentOp) ? `(${result})` : result;
    }

    case "prop":
      // arr.length → arr.size (Lean coerces Nat→Int automatically)
      if (expr.prop === "length" && isArrayExpr(expr.obj, ctx)) {
        return `${emit(expr.obj)}.size`;
      }
      return `${emit(expr.obj)}.${expr.prop}`;

    case "index": {
      // arr[i] → arr[i.toNat]!
      if (isArrayExpr(expr.obj, ctx)) {
        return `${emit(expr.obj)}[${emit(expr.idx)}.toNat]!`;
      }
      return `${emit(expr.obj)}[${emit(expr.idx)}]`;
    }

    case "call": {
      // Math.floor(x) → strip (Int division is floor in Lean)
      if (expr.fn.kind === "prop" && expr.fn.prop === "floor" &&
          expr.fn.obj.kind === "var" && expr.fn.obj.name === "Math" &&
          expr.args.length === 1) {
        return emit(expr.args[0]);
      }
      // Ghost function call: f(a, b) → f a b
      const fnName = expr.fn.kind === "var" ? expr.fn.name : emit(expr.fn);
      const args = expr.args.map(a => emit(a));
      // Wrap complex args in parens
      const leanArgs = expr.args.map(a => {
        const s = emit(a);
        return a.kind === "binop" || a.kind === "unop" ? `(${s})` : s;
      });
      return `${fnName} ${leanArgs.join(" ")}`;
    }

    case "forall":
      return `∀ ${expr.var} : Int, ${emitLean(expr.body, ctx)}`;

    case "exists":
      return `∃ ${expr.var} : Int, ${emitLean(expr.body, ctx)}`;
  }
}

function isArrayExpr(expr: Expr, ctx: EmitContext): boolean {
  return expr.kind === "var" && ctx.arrayVars.has(expr.name);
}

// ── Public API ───────────────────────────────────────────────

export function parseExpr(input: string): Expr {
  return new Parser(tokenize(input)).parse();
}

export function exprToLean(input: string, ctx?: Partial<EmitContext>): string {
  const fullCtx = { ...defaultContext, ...ctx };
  return emitLean(parseExpr(input), fullCtx);
}

export function astToLean(expr: Expr, ctx?: Partial<EmitContext>): string {
  const fullCtx = { ...defaultContext, ...ctx };
  return emitLean(expr, fullCtx);
}

/**
 * Parse a spec expression and split top-level && into separate Lean clauses.
 */
export function specToClauses(input: string, ctx?: Partial<EmitContext>): string[] {
  const fullCtx = { ...defaultContext, ...ctx };
  const ast = parseExpr(input);
  return splitConjuncts(ast).map(e => emitLean(e, fullCtx));
}
