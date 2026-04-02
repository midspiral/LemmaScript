/**
 * Lean IR → text. Trivial pretty-printer.
 * No logic, no type decisions — just serialization.
 */

import type { LeanExpr, LeanStmt, LeanDecl, LeanFile, LeanMatchArm, LeanStmtMatchArm } from "./ir.js";

// ── Lean keyword escaping ────────────────────────────────────

const LEAN_KEYWORDS = new Set([
  "def", "theorem", "lemma", "example", "structure", "class", "instance",
  "inductive", "where", "match", "with", "if", "then", "else", "do",
  "let", "mut", "return", "for", "in", "while", "break", "continue",
  "import", "open", "section", "namespace", "end", "set_option",
  "variable", "axiom", "constant", "private", "protected", "noncomputable",
  "partial", "unsafe", "macro", "syntax", "by", "fun", "have", "show",
  "at", "from", "to", "deriving", "extends", "true", "false",
]);

function escapeName(name: string): string {
  return LEAN_KEYWORDS.has(name) ? `«${name}»` : name;
}

// ── Operator precedence (for parenthesization) ──────────────

const PREC: Record<string, number> = {
  "→": 1, "∨": 2, "∧": 3,
  "=": 4, "≠": 4, "≥": 4, "≤": 4, ">": 4, "<": 4,
  "+": 5, "-": 5, "*": 6, "/": 6, "%": 6,
};

function prec(op: string): number { return PREC[op] ?? 10; }

// ── Expression emission ─────────────────────────────────────

function emitExpr(e: LeanExpr, parentPrec?: number): string {
  switch (e.kind) {
    case "var": return escapeName(e.name);
    case "num": return `${e.value}`;
    case "bool": return e.value ? "true" : "false";
    case "str": return `"${e.value}"`;
    case "constructor": return `.${e.name}`;
    case "emptyArray": return `#[]`;

    case "dotCall": {
      const obj = emitExpr(e.obj);
      const wrap = e.obj.kind === "binop" || e.obj.kind === "app" || e.obj.kind === "dotCall";
      const receiver = wrap ? `(${obj})` : obj;
      const args = e.args.map(a =>
        (a.kind === "binop" || a.kind === "unop" || a.kind === "implies" || a.kind === "app") ? `(${emitExpr(a)})` : emitExpr(a)
      );
      return args.length > 0 ? `${receiver}.${e.method} ${args.join(" ")}` : `${receiver}.${e.method}`;
    }

    case "lambda": {
      const params = e.params.map(p => p.name).join(" ");
      // Single return statement → expression lambda
      if (e.body.length === 1 && e.body[0].kind === "return") {
        return `(fun ${params} => ${emitExpr(e.body[0].value)})`;
      }
      // Multi-statement → do block
      return `(fun ${params} => do\n${emitStmts(e.body, 2)})`;
    }

    case "unop":
      if (e.op === "¬") return `¬(${emitExpr(e.expr)})`;
      if (e.op === "-" && e.expr.kind === "num") return `-${e.expr.value}`;
      return `(-${emitExpr(e.expr)})`;

    case "binop": {
      const s = `${emitExpr(e.left, prec(e.op))} ${e.op} ${emitExpr(e.right, prec(e.op))}`;
      return (parentPrec !== undefined && prec(e.op) < parentPrec) ? `(${s})` : s;
    }

    case "implies": {
      const parts = [...e.premises.map(p => emitExpr(p)), emitExpr(e.conclusion)];
      const s = parts.join(" → ");
      return parentPrec !== undefined ? `(${s})` : s;
    }

    case "app": {
      const args = e.args.map(a =>
        (a.kind === "binop" || a.kind === "unop" || a.kind === "implies" || a.kind === "app") ? `(${emitExpr(a)})` : emitExpr(a)
      );
      return `${e.fn} ${args.join(" ")}`;
    }

    case "field": {
      const obj = emitExpr(e.obj);
      const wrap = e.obj.kind !== "var" && e.obj.kind !== "num" && e.obj.kind !== "bool";
      return wrap ? `(${obj}).${escapeName(e.field)}` : `${obj}.${escapeName(e.field)}`;
    }

    case "index": {
      const idx = emitExpr(e.idx);
      const needsParens = e.toNat && e.idx.kind !== "var" && e.idx.kind !== "num";
      const idxStr = e.toNat ? (needsParens ? `(${idx}).toNat` : `${idx}.toNat`) : idx;
      return `${emitExpr(e.arr)}[${idxStr}]!`;
    }

    case "record": {
      const fields = e.fields.map(f => `${escapeName(f.name)} := ${emitExpr(f.value)}`);
      return `{ ${fields.join(", ")} }`;
    }

    case "if":
      return `if ${emitExpr(e.cond)} then ${emitExpr(e.then)} else ${emitExpr(e.else)}`;

    case "match": {
      const arms = e.arms.map(a => `| ${a.pattern} => ${emitExpr(a.body)}`);
      return `match ${e.scrutinee} with ${arms.join(" ")}`;
    }

    case "forall": return `∀ ${e.var} : ${e.type}, ${emitExpr(e.body)}`;
    case "exists": return `∃ ${e.var} : ${e.type}, ${emitExpr(e.body)}`;

    case "let": return `let ${e.name} := ${emitExpr(e.value)}\n${emitExpr(e.body)}`;
  }
}

// ── Statement emission ──────────────────────────────────────

function emitStmts(stmts: LeanStmt[], indent: number): string {
  const pad = "  ".repeat(indent);
  return stmts.map(s => emitStmt(s, indent)).join("\n");
}

function emitStmt(s: LeanStmt, indent: number): string {
  const pad = "  ".repeat(indent);
  switch (s.kind) {
    case "let":
      return s.mutable
        ? `${pad}let mut ${escapeName(s.name)} : ${s.type} := ${emitExpr(s.value)}`
        : `${pad}let ${escapeName(s.name)} := ${emitExpr(s.value)}`;
    case "assign": return `${pad}${escapeName(s.target)} := ${emitExpr(s.value)}`;
    case "bind": return `${pad}${escapeName(s.target)} ← ${emitExpr(s.value)}`;
    case "let-bind": return `${pad}let ${s.name} ← ${emitExpr(s.value)}`;
    case "return": return `${pad}return ${emitExpr(s.value)}`;
    case "break": return `${pad}break`;
    case "continue": return `${pad}continue`;

    case "if": {
      let out = `${pad}if ${emitExpr(s.cond)} then\n${emitStmts(s.then, indent + 1)}`;
      if (s.else.length > 0) {
        if (s.else.length === 1 && s.else[0].kind === "if") {
          const ei = s.else[0];
          out += `\n${pad}else if ${emitExpr(ei.cond)} then\n${emitStmts(ei.then, indent + 1)}`;
          if (ei.else.length > 0) out += `\n${pad}else\n${emitStmts(ei.else, indent + 1)}`;
        } else {
          out += `\n${pad}else\n${emitStmts(s.else, indent + 1)}`;
        }
      }
      return out;
    }

    case "match": {
      const lines = [`${pad}match ${s.scrutinee} with`];
      for (const arm of s.arms) {
        lines.push(`${pad}| ${arm.pattern} =>`);
        lines.push(emitStmts(arm.body, indent + 1));
      }
      return lines.join("\n");
    }

    case "while": {
      const lines = [`${pad}while ${emitExpr(s.cond)}`];
      for (const inv of s.invariants) lines.push(`${pad}  invariant ${emitExpr(inv)}`);
      if (s.doneWith) lines.push(`${pad}  done_with ${emitExpr(s.doneWith)}`);
      if (s.decreasing) lines.push(`${pad}  decreasing ${emitExpr(s.decreasing)}`);
      lines.push(`${pad}do`);
      lines.push(emitStmts(s.body, indent + 1));
      return lines.join("\n");
    }

    case "forin": {
      const lines = [`${pad}for ${s.idx} in [:${emitExpr(s.bound)}]`];
      for (const inv of s.invariants) lines.push(`${pad}  invariant ${emitExpr(inv)}`);
      lines.push(`${pad}do`);
      lines.push(emitStmts(s.body, indent + 1));
      return lines.join("\n");
    }
  }
}

// ── Declaration emission ─────────────────────────────────────

function emitDecl(d: LeanDecl): string {
  switch (d.kind) {
    case "inductive": {
      const lines = [`inductive ${d.name} where`];
      for (const c of d.constructors) {
        if (c.fields.length === 0) {
          lines.push(`  | ${c.name} : ${d.name}`);
        } else {
          const params = c.fields.map(f => `(${escapeName(f.name)} : ${f.type})`).join(" ");
          lines.push(`  | ${c.name} ${params} : ${d.name}`);
        }
      }
      if (d.deriving.length > 0) lines.push(`deriving ${d.deriving.join(", ")}`);
      return lines.join("\n");
    }

    case "structure": {
      const lines = [`structure ${d.name} where`];
      for (const f of d.fields) lines.push(`  ${escapeName(f.name)} : ${f.type}`);
      if (d.deriving.length > 0) lines.push(`deriving ${d.deriving.join(", ")}`);
      return lines.join("\n");
    }

    case "def": {
      const params = d.params.map(p => `(${escapeName(p.name)} : ${p.type})`).join(" ");
      return `def ${d.name} ${params} : ${d.returnType} :=\n${emitPureExpr(d.body, 1)}`;
    }

    case "method": {
      const params = d.params.map(p => `(${escapeName(p.name)} : ${p.type})`).join(" ");
      const lines = [`method ${d.name} ${params} return (res : ${d.returnType})`];
      for (const r of d.requires) lines.push(`  require ${emitExpr(r)}`);
      for (const e of d.ensures) lines.push(`  ensures ${emitExpr(e)}`);
      lines.push("  do");
      lines.push(emitStmts(d.body, 2));
      return lines.join("\n");
    }

    case "namespace": {
      const lines = [`namespace ${d.name}`];
      for (const inner of d.decls) lines.push("", emitDecl(inner));
      lines.push("", `end ${d.name}`);
      return lines.join("\n");
    }
  }
}

/** Emit a pure expression with indented if/match blocks. */
function emitPureExpr(e: LeanExpr, indent: number): string {
  const pad = "  ".repeat(indent);
  switch (e.kind) {
    case "if":
      return `${pad}if ${emitExpr(e.cond)} then\n${emitPureExpr(e.then, indent + 1)}\n${pad}else\n${emitPureExpr(e.else, indent + 1)}`;
    case "match": {
      const lines = [`${pad}match ${e.scrutinee} with`];
      for (const arm of e.arms) {
        lines.push(`${pad}| ${arm.pattern} =>`);
        lines.push(emitPureExpr(arm.body, indent + 1));
      }
      return lines.join("\n");
    }
    case "let":
      return `${pad}let ${e.name} := ${emitExpr(e.value)}\n${emitPureExpr(e.body, indent)}`;
    default:
      return `${pad}${emitExpr(e)}`;
  }
}

// ── File emission ────────────────────────────────────────────

export function emitFile(file: LeanFile): string {
  const lines: string[] = [];
  if (file.comment) {
    lines.push("/-");
    lines.push(file.comment);
    lines.push("-/");
  }
  for (const imp of file.imports) lines.push(`import ${imp}`);
  if (file.options.length > 0) lines.push("");
  for (const opt of file.options) lines.push(`set_option ${opt.key} ${opt.value}`);
  for (const decl of file.decls) {
    lines.push("");
    lines.push(emitDecl(decl));
  }
  return lines.join("\n") + "\n";
}
