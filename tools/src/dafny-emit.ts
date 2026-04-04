/**
 * Dafny IR → text. Pretty-printer for Dafny syntax.
 */

import type { DafnyExpr, DafnyStmt, DafnyDecl, DafnyFile } from "./dafny-ir.js";

// ── Operator precedence ─────────────────────────────────────

const PREC: Record<string, number> = {
  "<==>": 1, "==>": 2, "||": 3, "&&": 4,
  "==": 5, "!=": 5, ">=": 5, "<=": 5, ">": 5, "<": 5, "in": 5,
  "+": 6, "-": 6, "*": 7, "/": 7, "%": 7,
};

function prec(op: string): number { return PREC[op] ?? 10; }

// ── Expression emission ─────────────────────────────────────

function emitExpr(e: DafnyExpr, parentPrec?: number): string {
  switch (e.kind) {
    case "var": return e.name;
    case "num": return `${e.value}`;
    case "bool": return e.value ? "true" : "false";
    case "str": return `"${e.value}"`;

    case "binop":
      return `(${emitExpr(e.left)} ${e.op} ${emitExpr(e.right)})`;

    case "unop":
      if (e.op === "!" && e.expr.kind !== "var" && e.expr.kind !== "bool")
        return `!(${emitExpr(e.expr)})`;
      if (e.op === "-" && e.expr.kind === "num") return `(-(${e.expr.value}))`;
      if (e.op === "-") return `(-(${emitExpr(e.expr)}))`;
      return `${e.op}${emitExpr(e.expr)}`;

    case "app": {
      const args = e.args.map(a => emitExpr(a));
      return `${e.fn}(${args.join(", ")})`;
    }

    case "field": return `${emitExpr(e.obj)}.${e.field}`;

    case "index": return `${emitExpr(e.seq)}[${emitExpr(e.idx)}]`;

    case "seqLength": return `|${emitExpr(e.seq)}|`;

    case "seqLiteral":
      if (e.elems.length === 0) return "[]";
      return `[${e.elems.map(el => emitExpr(el)).join(", ")}]`;

    case "seqSlice": {
      const from = e.from ? emitExpr(e.from) : "";
      const to = e.to ? emitExpr(e.to) : "";
      return `${emitExpr(e.seq)}[${from}..${to}]`;
    }

    case "seqUpdate":
      return `${emitExpr(e.seq)}[${emitExpr(e.idx)} := ${emitExpr(e.val)}]`;

    case "record": {
      const fields = e.fields.map(f => `${f.name} := ${emitExpr(f.value)}`);
      return `${e.fields[0]?.name ? "" : ""}(${fields.join(", ")})`;
    }

    case "constructor":
      if (e.args.length === 0) return e.name;
      return `${e.name}(${e.args.map(emitExpr).join(", ")})`;

    case "if":
      return `if ${emitExpr(e.cond)} then ${emitExpr(e.then)} else ${emitExpr(e.else)}`;

    case "match": {
      const arms = e.arms.map(a => `case ${a.pattern} => ${emitExpr(a.body)}`);
      return `match ${emitExpr(e.scrutinee)} { ${arms.join(" ")} }`;
    }

    case "let":
      return `var ${e.name} := ${emitExpr(e.value)}; ${emitExpr(e.body)}`;

    case "forall":
      return `forall ${e.vars.map(v => `${v.name}: ${v.type}`).join(", ")} :: ${emitExpr(e.body)}`;

    case "exists":
      return `exists ${e.vars.map(v => `${v.name}: ${v.type}`).join(", ")} :: ${emitExpr(e.body)}`;
  }
}

/** Emit a pure expression with proper indentation for if/match/let. */
function emitPureExpr(e: DafnyExpr, indent: number): string {
  const pad = "  ".repeat(indent);
  switch (e.kind) {
    case "if":
      return `${pad}if ${emitExpr(e.cond)} then\n${emitPureExpr(e.then, indent + 1)}\n${pad}else\n${emitPureExpr(e.else, indent + 1)}`;
    case "let":
      return `${pad}var ${e.name} := ${emitExpr(e.value)};\n${emitPureExpr(e.body, indent)}`;
    case "match": {
      const lines = [`${pad}match ${emitExpr(e.scrutinee)} {`];
      for (const arm of e.arms) {
        lines.push(`${pad}  case ${arm.pattern} =>`);
        lines.push(emitPureExpr(arm.body, indent + 2));
      }
      lines.push(`${pad}}`);
      return lines.join("\n");
    }
    default:
      return `${pad}${emitExpr(e)}`;
  }
}

// ── Statement emission ──────────────────────────────────────

function emitStmts(stmts: DafnyStmt[], indent: number): string {
  return stmts.map(s => emitStmt(s, indent)).join("\n");
}

function emitStmt(s: DafnyStmt, indent: number): string {
  const pad = "  ".repeat(indent);
  switch (s.kind) {
    case "var":
      return `${pad}var ${s.name}${s.mutable ? "" : ""} := ${emitExpr(s.value)};`;
    case "assign":
      return `${pad}${s.target} := ${emitExpr(s.value)};`;
    case "return":
      return `${pad}return ${emitExpr(s.value)};`;
    case "break":
      return `${pad}break;`;
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
      const lines = [`${pad}match ${emitExpr(s.scrutinee)} {`];
      for (const arm of s.arms) {
        lines.push(`${pad}  case ${arm.pattern} =>`);
        lines.push(emitStmts(arm.body, indent + 2));
      }
      lines.push(`${pad}}`);
      return lines.join("\n");
    }
    case "while": {
      const lines = [`${pad}while ${emitExpr(s.cond)}`];
      for (const inv of s.invariants) lines.push(`${pad}  invariant ${emitExpr(inv)}`);
      if (s.decreases) lines.push(`${pad}  decreases ${emitExpr(s.decreases)}`);
      lines.push(`${pad}{`);
      lines.push(emitStmts(s.body, indent + 1));
      lines.push(`${pad}}`);
      return lines.join("\n");
    }
  }
}

// ── Declaration emission ────────────────────────────────────

function emitDecl(d: DafnyDecl): string {
  switch (d.kind) {
    case "function": {
      const params = d.params.map(p => `${p.name}: ${p.type}`).join(", ");
      const lines = [`function ${d.name}(${params}): ${d.returnType}`];
      for (const r of d.requires) lines.push(`  requires ${emitExpr(r)}`);
      if (d.decreases) lines.push(`  decreases ${emitExpr(d.decreases)}`);
      lines.push(`{`);
      lines.push(emitPureExpr(d.body, 1));
      lines.push(`}`);
      return lines.join("\n");
    }

    case "method": {
      const params = d.params.map(p => `${p.name}: ${p.type}`).join(", ");
      const returns = d.returns.map(r => `${r.name}: ${r.type}`).join(", ");
      const lines = [`method ${d.name}(${params}) returns (${returns})`];
      for (const r of d.requires) lines.push(`  requires ${emitExpr(r)}`);
      for (const e of d.ensures) lines.push(`  ensures ${emitExpr(e)}`);
      if (d.decreases) lines.push(`  decreases ${emitExpr(d.decreases)}`);
      lines.push(`{`);
      lines.push(emitStmts(d.body, 1));
      lines.push(`}`);
      return lines.join("\n");
    }

    case "datatype": {
      const ctors = d.constructors.map(c => {
        if (c.fields.length === 0) return c.name;
        const fields = c.fields.map(f => `${f.name}: ${f.type}`).join(", ");
        return `${c.name}(${fields})`;
      });
      return `datatype ${d.name} = ${ctors.join(" | ")}`;
    }

    case "predicate": {
      const params = d.params.map(p => `${p.name}: ${p.type}`).join(", ");
      return `predicate ${d.name}(${params}) {\n${emitPureExpr(d.body, 1)}\n}`;
    }
  }
}

// ── File emission ───────────────────────────────────────────

export function emitDafnyFile(file: DafnyFile): string {
  const lines: string[] = [];
  lines.push(`// ${file.comment}`);
  for (const decl of file.decls) {
    lines.push("");
    lines.push(emitDecl(decl));
  }
  return lines.join("\n") + "\n";
}
