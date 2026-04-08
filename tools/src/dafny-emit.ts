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
  // Array (X Y) → seq<...>
  const arrParenMatch = t.match(/^Array\s+\((.+)\)$/);
  if (arrParenMatch) return `seq<${leanTypeToDafny(arrParenMatch[1])}>`;
  // Array X → seq<X>
  const arrMatch = t.match(/^Array\s+(.+)$/);
  if (arrMatch) return `seq<${leanTypeToDafny(arrMatch[1])}>`;
  // HashMap K V → map<K, V>  (with or without Std. prefix)
  const hmMatch = t.match(/^(?:Std\.)?HashMap\s+(\S+)\s+(.+)$/);
  if (hmMatch) return `map<${leanTypeToDafny(hmMatch[1])}, ${leanTypeToDafny(hmMatch[2])}>`;
  // HashSet T → set<T>
  const hsMatch = t.match(/^(?:Std\.)?HashSet\s+(.+)$/);
  if (hsMatch) return `set<${leanTypeToDafny(hsMatch[1])}>`;
  // Option T → Option<T>
  const optMatch = t.match(/^Option\s+(.+)$/);
  if (optMatch) { needsOptionType = true; return `Option<${leanTypeToDafny(optMatch[1])}>`; }
  // Strip parens: (X) → X
  const parenMatch = t.match(/^\((.+)\)$/);
  if (parenMatch) return leanTypeToDafny(parenMatch[1]);
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
    case "constructor": return qualifyCtor(e.name, e.type);

    case "arrayLiteral":
      if (e.elems.length === 0) return `[]`;
      return `[${e.elems.map(emitExpr).join(", ")}]`;

    case "emptyMap": return `map[]`;
    case "emptySet": return `{}`;

    case "dotCall": {
      const obj = emitExpr(e.obj);
      const args = e.args.map(emitExpr);
      if (e.method === "with" && args.length === 2)
        return `${obj}[${args[0]} := ${args[1]}]`;
      if (e.method === "includes" && args.length === 1) return `(${args[0]} in ${obj})`;
      // Map operations
      if (e.method === "mapGetDirect" && args.length === 1) return `${obj}[${args[0]}]`;
      if (e.method === "mapGet" && args.length === 1) {
        needsOptionType = true;
        return `(if ${args[0]} in ${obj} then Some(${obj}[${args[0]}]) else None)`;
      }
      if (e.method === "mapSet" && args.length === 2) return `${obj}[${args[0]} := ${args[1]}]`;
      if (e.method === "mapHas" && args.length === 1) return `(${args[0]} in ${obj})`;
      // Set operations
      if (e.method === "setHas" && args.length === 1) return `(${args[0]} in ${obj})`;
      if (e.method === "setAdd" && args.length === 1) return `(${obj} + {${args[0]}})`;
      if (e.method === "map" && args.length === 1) { needsStdCollections = true; return `Seq.Map(${args[0]}, ${obj})`; }
      if (e.method === "filter" && args.length === 1) { needsStdCollections = true; return `Seq.Filter(${args[0]}, ${obj})`; }
      if (e.method === "every" && args.length === 1) { needsStdCollections = true; return `Seq.All(${obj}, ${args[0]})`; }
      if (e.method === "some" && args.length === 1 && e.args[0].kind === "lambda" &&
          e.args[0].body.length === 1 && e.args[0].body[0].kind === "return") {
        const lam = e.args[0];
        const ret = lam.body[0];
        if (ret.kind !== "return") throw new Error("unreachable");
        const p = escapeName(lam.params[0]?.name ?? "x");
        const body = emitExpr(ret.value);
        return `(exists ${p} :: ${p} in ${obj} && ${body})`;
      }
      return `${obj}.${e.method}(${args.join(", ")})`;
    }

    case "lambda": {
      const ps = paramList(e.params);
      if (e.body.length === 1 && e.body[0].kind === "return")
        return `(${ps}) => ${emitExpr(e.body[0].value)}`;
      throw new Error("Unsupported: multi-statement lambda in Dafny");
    }

    case "unop": {
      const op = mapOp(e.op);
      if (op === "!" && e.expr.kind !== "var" && e.expr.kind !== "bool")
        return `!(${emitExpr(e.expr)})`;
      if (e.op === "-" && e.expr.kind === "num") return `(-(${e.expr.value}))`;
      if (e.op === "-") return `(-(${emitExpr(e.expr)}))`;
      return `${op}(${emitExpr(e.expr)})`;
    }

    case "binop": {
      // Discriminant check: x == .Ctor → x.Ctor?
      const op = mapOp(e.op);
      if ((op === "==" || op === "!=") && e.right.kind === "constructor") {
        const ctorName = escapeName(e.right.name.replace(/^\./, ""));
        const pred = `${emitExpr(e.left)}.${ctorName}?`;
        return op === "!=" ? `(!${pred})` : pred;
      }
      return `(${emitExpr(e.left)} ${op} ${emitExpr(e.right)})`;
    }

    case "implies": {
      const parts = [...e.premises.map(emitExpr), emitExpr(e.conclusion)];
      return `(${parts.join(" ==> ")})`;
    }

    case "app": {
      const args = e.args.map(emitExpr);
      // Dafny built-in translations
      if (e.fn === "StringIndexOf") {
        needsStringIndexOf = true;
        return `StringIndexOf(${args.join(", ")})`;
      }
      if (e.fn === "StringSlice")
        return `${args[0]}[${args[1]}..${args[2]}]`;
      if (e.fn === "SeqPush")
        return `(${args[0]} + [${args[1]}])`;
      if (e.fn === "SetToSeq") { needsSetToSeq = true; return `SetToSeq(${args.join(", ")})`; }
      if (e.fn === "JSFloorDiv") needsJSFloorDiv = true;
      return `${e.fn}(${args.join(", ")})`;
    }

    case "field": {
      const obj = emitExpr(e.obj);
      if (e.field === "size" || e.field === "length" || e.field === "collectionSize") return `|${obj}|`;
      if (e.field === "toNat") return obj;
      return `${obj}.${escapeName(e.field)}`;
    }

    case "toNat":
      // Dafny doesn't need toNat — just emit the inner expression
      return emitExpr(e.expr);

    case "index":
      return `${emitExpr(e.arr)}[${emitExpr(e.idx)}]`;

    case "record": {
      if (e.spread) {
        const updates = e.fields.map(f => `${escapeName(f.name)} := ${emitExpr(f.value)}`);
        return `${emitExpr(e.spread)}.(${updates.join(", ")})`;
      }
      const ctorName = e.fields.length > 0 ? _recordCtors.get(e.fields[0].name) : undefined;
      const vals = e.fields.map(f => emitExpr(f.value));
      if (ctorName) return `${ctorName}(${vals.join(", ")})`;
      return `(${vals.join(", ")})`;
    }

    case "if":
      return `if ${emitExpr(e.cond)} then ${emitExpr(e.then)} else ${emitExpr(e.else)}`;

    case "match": {
      const scrut = typeof e.scrutinee === "string" ? escapeName(e.scrutinee) : emitExpr(e.scrutinee);
      const arms = e.arms.map(a => `case ${translatePattern(a.pattern)} => ${emitExpr(a.body)}`);
      return `(match ${scrut} { ${arms.join(" ")} })`;
    }

    case "forall": {
      const dty = leanTypeToDafny(e.type);
      const ann = dty === "string" ? "" : `: ${dty}`;
      return `forall ${e.var}${ann} :: ${emitExpr(e.body)}`;
    }
    case "exists": {
      const dty = leanTypeToDafny(e.type);
      const ann = dty === "string" ? "" : `: ${dty}`;
      return `exists ${e.var}${ann} :: ${emitExpr(e.body)}`;
    }

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
      const scrut = typeof e.scrutinee === "string" ? escapeName(e.scrutinee) : emitExpr(e.scrutinee);
      const lines = [`${pad}match ${scrut} {`];
      for (const arm of e.arms) {
        lines.push(`${pad}  case ${translatePattern(arm.pattern)} =>`);
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
    case "ghostLet":
      return `${pad}ghost var ${escapeName(s.name)}: ${leanTypeToDafny(s.type)} := ${emitExpr(s.value)};`;
    case "ghostAssign":
      return `${pad}${escapeName(s.target)} := ${emitExpr(s.value)};`;
    case "assert":
      return `${pad}assert ${emitExpr(s.expr)};`;
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
      throw new Error("Unsupported Dafny construct: 'continue' statement");

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
      const scrut = typeof s.scrutinee === "string" ? escapeName(s.scrutinee) : emitExpr(s.scrutinee);
      const lines = [`${pad}match ${scrut} {`];
      for (const arm of s.arms) {
        lines.push(`${pad}  case ${translatePattern(arm.pattern)} =>`);
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
      const lines = [`function ${d.name}(${paramList(d.params)}): ${leanTypeToDafny(d.returnType)}`];
      for (const r of d.requires) lines.push(`  requires ${emitExpr(r)}`);
      lines.push(`{`);
      lines.push(emitPureExpr(d.body, 1));
      lines.push(`}`);
      // Companion lemma for ensures (proof target for LLM)
      if (d.ensures.length > 0) {
        lines.push("");
        lines.push(`lemma ${d.name}_ensures(${paramList(d.params)})`);
        for (const r of d.requires) lines.push(`  requires ${emitExpr(r)}`);
        for (const e of d.ensures) lines.push(`  ensures ${emitExpr(e)}`);
        lines.push(`{`);
        lines.push(`}`);
      }
      return lines.join("\n");
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

// ── Preamble helpers ────────────────────────────────────────

let needsStringIndexOf = false;
let needsJSFloorDiv = false;
let needsStdCollections = false;
let needsOptionType = false;
let needsSetToSeq = false;

const JS_FLOOR_DIV = `function JSFloorDiv(a: int, b: int): int
  requires b != 0
{
  if b > 0 then
    if a >= 0 then a / b
    else -((-a - 1) / b) - 1
  else
    if a <= 0 then (-a) / (-b)
    else -((a - 1) / (-b)) - 1
}`;

const STRING_INDEX_OF = `function StringIndexOf(s: string, sub: string): int
{
  StringIndexOfFrom(s, sub, 0)
}

function StringIndexOfFrom(s: string, sub: string, from: nat): int
  decreases |s| - from
{
  if from + |sub| > |s| then -1
  else if s[from..from + |sub|] == sub then from as int
  else StringIndexOfFrom(s, sub, from + 1)
}`;

// ── Constructor and record helpers ───────────────────────────

let _recordCtors = new Map<string, string>();

function buildRecordCtorMap(decls: LeanDecl[]) {
  _recordCtors = new Map();
  for (const d of decls) {
    if (d.kind === "structure" && d.fields.length > 0)
      _recordCtors.set(d.fields[0].name, d.name);
    if (d.kind === "namespace") for (const inner of d.decls) {
      if (inner.kind === "structure" && inner.fields.length > 0)
        _recordCtors.set(inner.fields[0].name, inner.name);
    }
  }
}

function qualifyCtor(name: string, type?: string): string {
  const rawName = name.replace(/^\./, "");
  if (type) return `${type}.${escapeName(rawName)}`;
  return escapeName(rawName);
}

/** Translate a Lean match pattern to Dafny syntax.
 *  ".ctorName field1 field2" → "ctorName(field1, field2)"
 *  ".ctorName" → "ctorName"
 *  "_" → "_"
 */
const CTOR_MAP: Record<string, string> = { "some": "Some", "none": "None" };

function translatePattern(pattern: string): string {
  if (pattern === "_") return "_";
  const m = pattern.match(/^\.(\w+)\s*(.*)$/);
  if (!m) return pattern;
  const ctorName = CTOR_MAP[m[1]] ?? escapeName(m[1]);
  const fields = m[2].trim();
  if (!fields) return ctorName;
  const fieldNames = fields.split(/\s+/).map(escapeName);
  return `${ctorName}(${fieldNames.join(", ")})`;
}

const PREAMBLES: Record<string, string> = {
  StringIndexOf: STRING_INDEX_OF,
};

export function emitDafnyFile(file: LeanFile, tsFileName?: string): string {
  buildRecordCtorMap(file.decls);
  needsStringIndexOf = false;
  needsJSFloorDiv = false;
  needsStdCollections = false;
  needsOptionType = false;
  needsSetToSeq = false;

  // Collect pure def names so we can skip their method wrappers
  const pureDefs = new Set<string>();
  for (const d of file.decls) {
    if (d.kind === "namespace") {
      for (const inner of d.decls) if (inner.kind === "def") pureDefs.add(inner.name);
    }
    if (d.kind === "def") pureDefs.add(d.name);
  }

  // Emit declarations
  const declLines: string[] = [];
  const skipped: string[] = [];
  for (const decl of file.decls) {
    if (decl.kind === "method" && pureDefs.has(decl.name)) continue;
    try {
      declLines.push("");
      declLines.push(emitDecl(decl));
    } catch (e) {
      const name = "name" in decl ? decl.name : "unknown";
      const msg = (e as Error).message;
      console.error(`WARNING: skipping '${name}': ${msg}`);
      declLines.push(`// LemmaScript: skipped ${name}`);
      skipped.push(name);
    }
  }
  if (skipped.length > 0) {
    console.error(`WARNING: ${skipped.length} declaration(s) skipped: ${skipped.join(", ")}`);
  }

  // Build output with needed preambles
  const lines: string[] = [];
  if (tsFileName) lines.push(`// Generated by lsc from ${tsFileName}`);
  if (needsStdCollections) lines.push("import Std.Collections.Seq");
  if (needsOptionType) { lines.push(""); lines.push("datatype Option<T> = None | Some(value: T)"); }
  if (needsSetToSeq) {
    lines.push("");
    lines.push(`method SetToSeq<T>(s: set<T>) returns (res: seq<T>)
  ensures forall x :: x in s <==> x in res
  ensures |res| == |s|
{
  var remaining := s;
  res := [];
  while remaining != {}
    decreases remaining
  {
    var x :| x in remaining;
    res := res + [x];
    remaining := remaining - {x};
  }
}`);
  }
  if (needsJSFloorDiv) { lines.push(""); lines.push(JS_FLOOR_DIV); }
  if (needsStringIndexOf) { lines.push(""); lines.push(PREAMBLES.StringIndexOf); }
  lines.push(...declLines);
  return lines.join("\n") + "\n";
}
