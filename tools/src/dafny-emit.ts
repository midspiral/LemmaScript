/**
 * Dafny emitter — translates Lean IR to Dafny syntax on the fly.
 *
 * No separate Dafny IR. The shared transform produces Lean IR,
 * and this emitter maps it to Dafny syntax.
 */

import type { LeanExpr, LeanStmt, LeanDecl, LeanFile } from "./ir.js";

// ── Lean type → Dafny type ──────────────────────────────────

function leanTypeToDafny(t: string): string {
  // Simple mappings
  const MAP: Record<string, string> = {
    "Int": "int", "Nat": "nat", "Bool": "bool",
    "String": "string", "Unit": "()", "_": "int",
  };
  if (MAP[t]) return MAP[t];
  // Array X → seq<X>
  const arrMatch = t.match(/^Array\s+(.+)$/);
  if (arrMatch) return `seq<${leanTypeToDafny(arrMatch[1])}>`;
  // Array (X) → seq<X>
  const arrParenMatch = t.match(/^Array\s+\((.+)\)$/);
  if (arrParenMatch) return `seq<${leanTypeToDafny(arrParenMatch[1])}>`;
  // User types pass through
  return t;
}

// ── Dafny keyword escaping ──────────────────────────────────

const DAFNY_KEYWORDS = new Set([
  "seq", "set", "map", "multiset", "iset", "imap",
  "var", "method", "function", "predicate", "lemma",
  "class", "trait", "module", "import", "export",
  "if", "then", "else", "while", "for", "in",
  "match", "case", "return", "break", "continue",
  "requires", "ensures", "invariant", "decreases",
  "forall", "exists", "old", "fresh", "allocated",
  "true", "false", "null", "this", "new",
  "datatype", "type", "const", "ghost", "static",
  "reads", "modifies", "assert", "assume", "print",
  "by", "calc", "reveal",
]);

function escapeName(name: string): string {
  if (DAFNY_KEYWORDS.has(name)) return `${name}_`;
  // Dafny doesn't allow identifiers starting with _
  if (name.startsWith("_")) return `i${name}`;
  return name;
}

/** Format a typed parameter list for Dafny: "x: int, y: seq<int>" */
function paramList(params: { name: string; type: string }[]): string {
  return params.map(p => `${escapeName(p.name)}: ${leanTypeToDafny(p.type)}`).join(", ");
}

// ── Lean op → Dafny op ─────────────────────────────────────

const OP_MAP: Record<string, string> = {
  "=": "==", "≠": "!=", "≥": ">=", "≤": "<=",
  "∧": "&&", "∨": "||", "¬": "!",
};

function mapOp(op: string): string { return OP_MAP[op] ?? op; }

// ── Expression emission ─────────────────────────────────────

function emitExpr(e: LeanExpr): string {
  switch (e.kind) {
    case "var": return escapeName(e.name);
    case "num": return `${e.value}`;
    case "bool": return e.value ? "true" : "false";
    case "str": return `"${e.value}"`;
    case "constructor": return e.name.replace(/^\./, "");

    case "arrayLiteral":
      if (e.elems.length === 0) return `[]`;
      return `[${e.elems.map(emitExpr).join(", ")}]`;

    case "dotCall": {
      const obj = emitExpr(e.obj);
      const args = e.args.map(emitExpr);
      // map/filter etc. — emit as function call for now
      return `${obj}.${e.method}(${args.join(", ")})`;
    }

    case "lambda": {
      const ps = paramList(e.params);
      if (e.body.length === 1 && e.body[0].kind === "return")
        return `(${ps}) => ${emitExpr(e.body[0].value)}`;
      const last = e.body[e.body.length - 1];
      if (last?.kind === "return") return `(${ps}) => ${emitExpr(last.value)}`;
      return `/* unsupported multi-statement lambda */`;
    }

    case "unop": {
      const op = mapOp(e.op);
      if (op === "!" && e.expr.kind !== "var" && e.expr.kind !== "bool")
        return `!(${emitExpr(e.expr)})`;
      if (e.op === "-" && e.expr.kind === "num") return `(-(${e.expr.value}))`;
      if (e.op === "-") return `(-(${emitExpr(e.expr)}))`;
      return `${op}(${emitExpr(e.expr)})`;
    }

    case "binop":
      return `(${emitExpr(e.left)} ${mapOp(e.op)} ${emitExpr(e.right)})`;

    case "implies": {
      const parts = [...e.premises.map(emitExpr), emitExpr(e.conclusion)];
      return `(${parts.join(" ==> ")})`;
    }

    case "app": {
      const args = e.args.map(emitExpr);
      return `${e.fn}(${args.join(", ")})`;
    }

    case "field": {
      const obj = emitExpr(e.obj);
      if (e.field === "size") return `|${obj}|`;
      if (e.field === "toNat") return obj; // Dafny doesn't need toNat
      return `${obj}.${escapeName(e.field)}`;
    }

    case "toNat":
      // Dafny doesn't need toNat — just emit the inner expression
      return emitExpr(e.expr);

    case "index":
      return `${emitExpr(e.arr)}[${emitExpr(e.idx)}]`;

    case "record": {
      const fields = e.fields.map(f => `${escapeName(f.name)} := ${emitExpr(f.value)}`);
      if (e.spread) return `${emitExpr(e.spread)}.(${fields.join(", ")})`;
      return `(${fields.join(", ")})`;
    }

    case "if":
      return `if ${emitExpr(e.cond)} then ${emitExpr(e.then)} else ${emitExpr(e.else)}`;

    case "match": {
      const arms = e.arms.map(a => `case ${a.pattern.replace(/^\./, "")} => ${emitExpr(a.body)}`);
      return `match ${e.scrutinee} { ${arms.join(" ")} }`;
    }

    case "forall": return `forall ${e.var}: ${leanTypeToDafny(e.type)} :: ${emitExpr(e.body)}`;
    case "exists": return `exists ${e.var}: ${leanTypeToDafny(e.type)} :: ${emitExpr(e.body)}`;

    case "let": return `var ${escapeName(e.name)} := ${emitExpr(e.value)}; ${emitExpr(e.body)}`;
  }
}

/** Emit a pure expression with indentation for if/match/let. */
function emitPureExpr(e: LeanExpr, indent: number): string {
  const pad = "  ".repeat(indent);
  switch (e.kind) {
    case "if":
      return `${pad}if ${emitExpr(e.cond)} then\n${emitPureExpr(e.then, indent + 1)}\n${pad}else\n${emitPureExpr(e.else, indent + 1)}`;
    case "match": {
      const lines = [`${pad}match ${e.scrutinee} {`];
      for (const arm of e.arms) {
        lines.push(`${pad}  case ${arm.pattern.replace(/^\./, "")} =>`);
        lines.push(emitPureExpr(arm.body, indent + 2));
      }
      lines.push(`${pad}}`);
      return lines.join("\n");
    }
    case "let":
      return `${pad}var ${escapeName(e.name)} := ${emitExpr(e.value)};\n${emitPureExpr(e.body, indent)}`;
    default:
      return `${pad}${emitExpr(e)}`;
  }
}

// ── Statement emission ──────────────────────────────────────

function emitStmts(stmts: LeanStmt[], indent: number): string {
  return stmts.map(s => emitStmt(s, indent)).join("\n");
}

function emitStmt(s: LeanStmt, indent: number): string {
  const pad = "  ".repeat(indent);
  switch (s.kind) {
    case "let":
      return `${pad}var ${escapeName(s.name)} := ${emitExpr(s.value)};`;
    case "assign":
      return `${pad}${escapeName(s.target)} := ${emitExpr(s.value)};`;
    case "bind":
      // Monadic bind shouldn't appear in Dafny mode, emit as regular assign
      return `${pad}${escapeName(s.target)} := ${emitExpr(s.value)};`;
    case "let-bind":
      // Monadic let-bind shouldn't appear in Dafny mode, emit as regular let
      return `${pad}var ${escapeName(s.name)} := ${emitExpr(s.value)};`;
    case "return":
      return `${pad}return ${emitExpr(s.value)};`;
    case "break":
      return `${pad}break;`;
    case "continue":
      return `${pad}// continue; (unsupported)`;

    case "if": {
      let out = `${pad}if ${emitExpr(s.cond)} {\n${emitStmts(s.then, indent + 1)}\n${pad}}`;
      if (s.else.length > 0) {
        if (s.else.length === 1 && s.else[0].kind === "if") {
          out += ` else ${emitStmt(s.else[0], indent).trimStart()}`;
        } else {
          out += ` else {\n${emitStmts(s.else, indent + 1)}\n${pad}}`;
        }
      }
      return out;
    }

    case "match": {
      const lines = [`${pad}match ${s.scrutinee} {`];
      for (const arm of s.arms) {
        lines.push(`${pad}  case ${arm.pattern.replace(/^\./, "")} =>`);
        lines.push(emitStmts(arm.body, indent + 2));
      }
      lines.push(`${pad}}`);
      return lines.join("\n");
    }

    case "while": {
      const lines = [`${pad}while ${emitExpr(s.cond)}`];
      for (const inv of s.invariants) lines.push(`${pad}  invariant ${emitExpr(inv)}`);
      if (s.decreasing) lines.push(`${pad}  decreases ${emitExpr(s.decreasing)}`);
      lines.push(`${pad}{`);
      lines.push(emitStmts(s.body, indent + 1));
      lines.push(`${pad}}`);
      return lines.join("\n");
    }

    case "forin": {
      // Lean for-in → Dafny while loop over index
      const idx = escapeName(s.idx);
      const lines = [
        `${pad}var ${idx} := 0;`,
        `${pad}while ${idx} < ${emitExpr(s.bound)}`,
      ];
      for (const inv of s.invariants) lines.push(`${pad}  invariant ${emitExpr(inv)}`);
      lines.push(`${pad}{`);
      lines.push(emitStmts(s.body, indent + 1));
      lines.push(`${pad}  ${idx} := ${idx} + 1;`);
      lines.push(`${pad}}`);
      return lines.join("\n");
    }
  }
}

// ── Declaration emission ────────────────────────────────────

function emitDecl(d: LeanDecl): string {
  switch (d.kind) {
    case "inductive": {
      const ctors = d.constructors.map(c => {
        if (c.fields.length === 0) return escapeName(c.name);
        return `${escapeName(c.name)}(${paramList(c.fields)})`;
      });
      return `datatype ${d.name} = ${ctors.join(" | ")}`;
    }

    case "structure": {
      return `datatype ${d.name} = ${d.name}(${paramList(d.fields)})`;
    }

    case "def": {
      return `function ${d.name}(${paramList(d.params)}): ${leanTypeToDafny(d.returnType)}\n{\n${emitPureExpr(d.body, 1)}\n}`;
    }

    case "method": {
      const lines = [`method ${d.name}(${paramList(d.params)}) returns (res: ${leanTypeToDafny(d.returnType)})`];
      for (const r of d.requires) lines.push(`  requires ${emitExpr(r)}`);
      for (const e of d.ensures) lines.push(`  ensures ${emitExpr(e)}`);
      lines.push(`{`);
      lines.push(emitStmts(d.body, 1));
      lines.push(`}`);
      return lines.join("\n");
    }

    case "namespace": {
      // Dafny doesn't need namespaces — flatten declarations
      return d.decls.map(emitDecl).join("\n\n");
    }
  }
}

// ── File emission ───────────────────────────────────────────

export function emitDafnyFile(file: LeanFile, tsFileName?: string): string {
  const lines: string[] = [];
  if (tsFileName) lines.push(`// Generated by lsc from ${tsFileName}`);
  for (const decl of file.decls) {
    lines.push("");
    lines.push(emitDecl(decl));
  }
  return lines.join("\n") + "\n";
}
