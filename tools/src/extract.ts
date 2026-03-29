/**
 * TS extractor — parses TypeScript with //@ annotations, produces IR.
 *
 * The IR is consumed by the code generator to produce .def.lean files.
 */

import { Project, SyntaxKind, Node, FunctionDeclaration, WhileStatement, SourceFile } from "ts-morph";

// ── IR types ─────────────────────────────────────────────────

export interface ParamSpec { name: string; type: string }
export interface LetSpec { kind: "let"; name: string; mutable: boolean; init: string; line: number }
export interface AssignSpec { kind: "assign"; target: string; value: string; line: number }
export interface ReturnSpec { kind: "return"; value: string; line: number }
export interface BreakSpec { kind: "break"; line: number }
export interface ExprStmtSpec { kind: "expr"; text: string; line: number }
export interface IfSpec { kind: "if"; condition: string; then: StmtSpec[]; else: StmtSpec[]; line: number }
export interface WhileSpec {
  kind: "while"; condition: string;
  invariants: string[]; decreases: string | null; doneWith: string | null;
  body: StmtSpec[]; line: number;
}
export type StmtSpec = LetSpec | AssignSpec | ReturnSpec | BreakSpec | ExprStmtSpec | IfSpec | WhileSpec;

export interface FunctionSpec {
  name: string;
  params: ParamSpec[];
  returnType: string;
  requires: string[];
  ensures: string[];
  typeAnnotations: { name: string; type: string }[];
  body: StmtSpec[];
  line: number;
}

export interface ModuleSpec {
  file: string;
  functions: FunctionSpec[];
}

// ── Annotation parsing ───────────────────────────────────────

const PREFIX = "//@ ";
const KEYWORDS = ["requires", "ensures", "invariant", "decreases", "done_with", "type"] as const;
type AnnotKind = (typeof KEYWORDS)[number];

interface Annotation { kind: AnnotKind; expr: string }

function parseAnnotations(node: Node): Annotation[] {
  const result: Annotation[] = [];
  for (const range of node.getLeadingCommentRanges()) {
    const text = range.getText().trim();
    if (!text.startsWith(PREFIX)) continue;
    const content = text.slice(PREFIX.length);
    const sp = content.indexOf(" ");
    if (sp === -1) continue;
    const kw = content.slice(0, sp);
    if (!(KEYWORDS as readonly string[]).includes(kw)) continue;
    result.push({ kind: kw as AnnotKind, expr: content.slice(sp + 1).trim() });
  }
  return result;
}

/** Collect annotations from a node and its first child statement. */
function collectAnnotations(node: Node, body?: Node[]): Annotation[] {
  const own = parseAnnotations(node);
  if (body && body.length > 0) return [...own, ...parseAnnotations(body[0])];
  return own;
}

// ── Statement extraction ─────────────────────────────────────

function extractStmts(stmts: Node[]): StmtSpec[] {
  const result: StmtSpec[] = [];
  for (const s of stmts) {
    const line = s.getStartLineNumber();

    if (Node.isVariableStatement(s)) {
      for (const d of s.getDeclarations()) {
        result.push({
          kind: "let", name: d.getName(), mutable: s.getDeclarationKind() === "let",
          init: d.getInitializer()?.getText() ?? "", line,
        });
      }
      continue;
    }

    if (Node.isWhileStatement(s)) {
      const bodyNode = s.getStatement();
      const bodyStmts = Node.isBlock(bodyNode) ? bodyNode.getStatements() : [];
      const annots = collectAnnotations(s, bodyStmts);
      result.push({
        kind: "while",
        condition: s.getExpression().getText(),
        invariants: annots.filter(a => a.kind === "invariant").map(a => a.expr),
        decreases: annots.find(a => a.kind === "decreases")?.expr ?? null,
        doneWith: annots.find(a => a.kind === "done_with")?.expr ?? null,
        body: extractStmts(bodyStmts),
        line,
      });
      continue;
    }

    if (Node.isIfStatement(s)) {
      const thenNode = s.getThenStatement();
      const elseNode = s.getElseStatement();
      result.push({
        kind: "if",
        condition: s.getExpression().getText(),
        then: Node.isBlock(thenNode) ? extractStmts(thenNode.getStatements()) : extractStmts([thenNode]),
        else: elseNode
          ? Node.isBlock(elseNode) ? extractStmts(elseNode.getStatements()) : extractStmts([elseNode])
          : [],
        line,
      });
      continue;
    }

    if (Node.isReturnStatement(s)) {
      result.push({ kind: "return", value: s.getExpression()?.getText() ?? "", line });
      continue;
    }

    if (Node.isBreakStatement(s)) {
      result.push({ kind: "break", line });
      continue;
    }

    if (Node.isExpressionStatement(s)) {
      const expr = s.getExpression();
      if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === "=") {
        result.push({ kind: "assign", target: expr.getLeft().getText(), value: expr.getRight().getText(), line });
      } else {
        result.push({ kind: "expr", text: expr.getText(), line });
      }
      continue;
    }

    result.push({ kind: "expr", text: s.getText(), line });
  }
  return result;
}

// ── Function extraction ──────────────────────────────────────

function extractFunction(fn: FunctionDeclaration): FunctionSpec {
  const bodyStmts = fn.getBody()?.getStatements() ?? [];
  const annots = collectAnnotations(fn, bodyStmts);

  const typeAnnotations: { name: string; type: string }[] = [];
  for (const a of annots) {
    if (a.kind === "type") {
      const parts = a.expr.split(/\s+/);
      if (parts.length === 2) typeAnnotations.push({ name: parts[0], type: parts[1] });
    }
  }

  return {
    name: fn.getName() ?? "<anonymous>",
    params: fn.getParameters().map(p => ({ name: p.getName(), type: p.getTypeNode()?.getText() ?? "unknown" })),
    returnType: fn.getReturnTypeNode()?.getText() ?? "unknown",
    requires: annots.filter(a => a.kind === "requires").map(a => a.expr),
    ensures: annots.filter(a => a.kind === "ensures").map(a => a.expr),
    typeAnnotations,
    body: extractStmts(bodyStmts),
    line: fn.getStartLineNumber(),
  };
}

// ── Module extraction ────────────────────────────────────────

export function extractModule(sourceFile: SourceFile): ModuleSpec {
  return {
    file: sourceFile.getFilePath(),
    functions: sourceFile.getFunctions().map(extractFunction),
  };
}

// ── Main ─────────────────────────────────────────────────────

if (process.argv[1]?.match(/extract\.(ts|js)$/)) {
  const file = process.argv[2];
  if (!file) { console.error("Usage: extract <file.ts>"); process.exit(1); }
  const proj = new Project({ compilerOptions: { strict: true } });
  console.log(JSON.stringify(extractModule(proj.addSourceFileAtPath(file)), null, 2));
}
