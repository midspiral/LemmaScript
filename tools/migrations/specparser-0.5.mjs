/**
 * Frozen parser for the LemmaScript 0.5 annotation expression language.
 *
 * This exists only for the versioned 0.5 → 0.6 migration utility. Production
 * parsing uses TypeScript directly; do not add new language features here.
 */

function normalizeBigIntLiteral(text) {
  const withoutSuffix = text.endsWith("n") ? text.slice(0, -1) : text;
  return BigInt(withoutSuffix.replace(/_/g, "")).toString(10);
}

const MULTI_OPS = ["<==>", "==>", "===", "!==", "==", "!=", ">=", "<=", "&&", "||"];
const BIGINT_LITERAL =
  /^(?:(?:0[xX][0-9a-fA-F](?:_?[0-9a-fA-F])*)|(?:0[bB][01](?:_?[01])*)|(?:0[oO][0-7](?:_?[0-7])*)|(?:[0-9](?:_?[0-9])*))n/;
const NUMBER_LITERAL =
  /^(?:(?:0[xX][0-9a-fA-F](?:_?[0-9a-fA-F])*)|(?:0[bB][01](?:_?[01])*)|(?:0[oO][0-7](?:_?[0-7])*)|(?:(?:[0-9](?:_?[0-9])*)(?:\.(?:[0-9](?:_?[0-9])*)?)?|\.(?:[0-9](?:_?[0-9])*))(?:[eE][+-]?(?:[0-9](?:_?[0-9])*))?)/;

function tokenize(input) {
  const tokens = [];
  let i = 0;
  while (i < input.length) {
    if (/\s/.test(input[i])) { i++; continue; }

    if (input[i] === "\\" && input.slice(i + 1, i + 7) === "result") {
      tokens.push({ type: "result" });
      i += 7;
      continue;
    }

    if (input[i] === '"' || input[i] === "'") {
      const quote = input[i++];
      let value = "";
      while (i < input.length && input[i] !== quote) {
        if (input[i] !== "\\") {
          value += input[i++];
          continue;
        }
        const escaped = input[i + 1];
        const mapped = escaped === "n" ? "\n" : escaped === "r" ? "\r" : escaped === "t" ? "\t"
          : escaped === "0" ? "\0" : escaped === "\\" || escaped === '"' || escaped === "'" ? escaped : null;
        if (mapped === null) throw new Error(`Unsupported string escape '\\${escaped}' at ${i}`);
        value += mapped;
        i += 2;
      }
      if (i >= input.length) throw new Error("Unterminated string literal");
      i++;
      tokens.push({ type: "str", value });
      continue;
    }

    if (/[0-9]/.test(input[i]) || (input[i] === "." && /[0-9]/.test(input[i + 1]))) {
      const rest = input.slice(i);
      const bigintMatch = rest.match(BIGINT_LITERAL);
      const match = bigintMatch ?? rest.match(NUMBER_LITERAL);
      if (!match) throw new Error(`Invalid numeric literal at ${i}`);
      const text = match[0];
      i += text.length;
      tokens.push(bigintMatch
        ? { type: "bigint", value: normalizeBigIntLiteral(text) }
        : { type: "num", value: Number(text.replace(/_/g, "")) });
      continue;
    }

    if (/[a-zA-Z_]/.test(input[i])) {
      let value = "";
      while (i < input.length && /[a-zA-Z_0-9]/.test(input[i])) value += input[i++];
      tokens.push({ type: "ident", value });
      continue;
    }

    let matched = false;
    for (const op of MULTI_OPS) {
      if (input.slice(i, i + op.length) !== op) continue;
      tokens.push({ type: "op", value: op });
      i += op.length;
      matched = true;
      break;
    }
    if (matched) continue;

    const value = input[i++];
    if ("+-*/%><!?".includes(value)) tokens.push({ type: "op", value });
    else if ("()[],:.{}".includes(value)) tokens.push({ type: "punc", value });
    else throw new Error(`Unexpected '${value}' at ${i - 1}`);
  }
  return tokens;
}

class Parser {
  constructor(tokens) {
    this.tokens = tokens;
    this.pos = 0;
  }

  peek() { return this.tokens[this.pos]; }
  advance() { return this.tokens[this.pos++]; }

  expect(type, value) {
    const token = this.advance();
    if (!token || token.type !== type || (value !== undefined && token.value !== value)) {
      throw new Error(`Expected ${type}${value ? ` '${value}'` : ""}, got ${token ? JSON.stringify(token) : "EOF"}`);
    }
    return token;
  }

  match(type, value) {
    const token = this.peek();
    if (!token || token.type !== type || (value !== undefined && token.value !== value)) return false;
    this.pos++;
    return true;
  }

  parse() {
    const result = this.parseIff();
    if (this.pos < this.tokens.length) throw new Error(`Unexpected ${JSON.stringify(this.peek())}`);
    return result;
  }

  parseIff() {
    const left = this.parseImplies();
    return this.match("op", "<==>")
      ? { kind: "binop", op: "<==>", left, right: this.parseIff() }
      : left;
  }

  parseImplies() {
    const left = this.parseTernary();
    return this.match("op", "==>")
      ? { kind: "binop", op: "==>", left, right: this.parseImplies() }
      : left;
  }

  parseTernary() {
    const cond = this.parseOr();
    if (!this.match("op", "?")) return cond;
    const then = this.parseIff();
    this.expect("punc", ":");
    return { kind: "conditional", cond, then, else: this.parseIff() };
  }

  parseOr() {
    let left = this.parseAnd();
    while (this.match("op", "||")) left = { kind: "binop", op: "||", left, right: this.parseAnd() };
    return left;
  }

  parseAnd() {
    let left = this.parseCmp();
    while (this.match("op", "&&")) left = { kind: "binop", op: "&&", left, right: this.parseCmp() };
    return left;
  }

  parseCmp() {
    const left = this.parseAdd();
    const token = this.peek();
    if (token?.type === "ident" && token.value === "in") {
      this.advance();
      return { kind: "binop", op: "in", left, right: this.parseAdd() };
    }
    if (token?.type === "op" && ["===", "!==", "==", "!=", ">=", "<=", ">", "<"].includes(token.value)) {
      this.advance();
      const op = token.value === "==" ? "===" : token.value === "!=" ? "!==" : token.value;
      return { kind: "binop", op, left, right: this.parseAdd() };
    }
    return left;
  }

  parseAdd() {
    let left = this.parseMul();
    while (this.peek()?.type === "op" && ["+", "-"].includes(this.peek().value)) {
      const op = this.advance().value;
      left = { kind: "binop", op, left, right: this.parseMul() };
    }
    return left;
  }

  parseMul() {
    let left = this.parseUnary();
    while (this.peek()?.type === "op" && ["*", "/", "%"].includes(this.peek().value)) {
      const op = this.advance().value;
      left = { kind: "binop", op, left, right: this.parseUnary() };
    }
    return left;
  }

  parseUnary() {
    if (this.match("op", "!")) return { kind: "unop", op: "!", expr: this.parseUnary() };
    if (this.match("op", "-")) return { kind: "unop", op: "-", expr: this.parseUnary() };
    return this.parsePostfix();
  }

  parsePostfix() {
    let expr = this.parseAtom();
    while (true) {
      if (this.match("punc", ".")) {
        expr = { kind: "field", obj: expr, field: this.expect("ident").value };
      } else if (this.match("punc", "[")) {
        const idx = this.parseIff();
        this.expect("punc", "]");
        expr = { kind: "index", obj: expr, idx };
      } else if (this.match("punc", "(")) {
        const args = [];
        if (!this.match("punc", ")")) {
          args.push(this.parseIff());
          while (this.match("punc", ",")) args.push(this.parseIff());
          this.expect("punc", ")");
        }
        expr = { kind: "call", fn: expr, args };
      } else {
        return expr;
      }
    }
  }

  parseAtom() {
    const token = this.peek();
    if (!token) throw new Error("Unexpected end of expression");
    if (token.type === "result") { this.advance(); return { kind: "result" }; }
    if (token.type === "num") { this.advance(); return { kind: "num", value: token.value }; }
    if (token.type === "bigint") { this.advance(); return { kind: "bigint", value: token.value }; }
    if (token.type === "str") { this.advance(); return { kind: "str", value: token.value }; }

    if (token.type === "ident") {
      if (token.value === "true" || token.value === "false") {
        this.advance();
        return { kind: "bool", value: token.value === "true" };
      }
      if (token.value === "null") {
        this.advance();
        return { kind: "var", name: "undefined" };
      }
      if (token.value === "new") return this.parseEmptyCollection();
      if (token.value === "forall" || token.value === "exists") return this.parseQuantifier();
      this.advance();
      return { kind: "var", name: token.value };
    }

    if (this.match("punc", "(")) {
      const expr = this.parseIff();
      this.expect("punc", ")");
      return expr;
    }
    if (this.match("punc", "[")) {
      const elems = [];
      if (!this.match("punc", "]")) {
        elems.push(this.parseIff());
        while (this.match("punc", ",")) elems.push(this.parseIff());
        this.expect("punc", "]");
      }
      return { kind: "arrayLiteral", elems };
    }
    if (this.match("punc", "{")) {
      const fields = [];
      if (!this.match("punc", "}")) {
        do {
          const name = this.expect("ident").value;
          this.expect("punc", ":");
          fields.push({ name, value: this.parseIff() });
        } while (this.match("punc", ","));
        this.expect("punc", "}");
      }
      return { kind: "record", spread: null, fields };
    }
    throw new Error(`Unexpected ${JSON.stringify(token)}`);
  }

  parseEmptyCollection() {
    this.expect("ident", "new");
    const name = this.expect("ident").value;
    if (name !== "Set" && name !== "Map") throw new Error(`Unsupported constructor: new ${name}`);
    let tsType = name;
    if (this.match("op", "<")) {
      let depth = 1;
      let typeArgs = "";
      while (depth > 0) {
        const token = this.advance();
        if (!token) throw new Error("Unterminated collection type arguments");
        if (token.value === "<") depth++;
        else if (token.value === ">") {
          depth--;
          if (depth === 0) break;
        }
        typeArgs += token.value;
      }
      tsType = `${name}<${typeArgs}>`;
    }
    this.expect("punc", "(");
    this.expect("punc", ")");
    return { kind: "emptyCollection", collectionType: name, tsType };
  }

  parseQuantifier() {
    const kind = this.expect("ident").value;
    this.expect("punc", "(");
    const variable = this.expect("ident").value;
    let varType = "int";
    if (this.match("punc", ":")) varType = this.expect("ident").value;
    this.expect("punc", ",");
    const body = this.parseIff();
    this.expect("punc", ")");
    return { kind, var: variable, varType, body };
  }
}

export function parseLegacyExpr(input) {
  return new Parser(tokenize(input)).parse();
}
