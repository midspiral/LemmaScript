/**
 * TS extractor — parses TypeScript with //@ annotations, produces IR.
 *
 * The IR is consumed by the code generator to produce .types.lean and .def.lean files.
 */

import { Project, Node, FunctionDeclaration, InterfaceDeclaration, SourceFile, TypeAliasDeclaration, Type, SyntaxKind } from "ts-morph";
import type { TypeDeclInfo, VariantInfo } from "./types.js";

// ── IR types ─────────────────────────────────────────────────

export interface ParamSpec { name: string; type: string }
export interface LetSpec { kind: "let"; name: string; mutable: boolean; type: string; init: string; line: number }
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
export interface SwitchSpec {
  kind: "switch"; expr: string; discriminant: string;
  cases: { label: string; body: StmtSpec[] }[];
  defaultBody: StmtSpec[];
  line: number;
}
export type StmtSpec = LetSpec | AssignSpec | ReturnSpec | BreakSpec | ExprStmtSpec | IfSpec | WhileSpec | SwitchSpec;

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
  typeDecls: TypeDeclInfo[];
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

function collectAnnotations(node: Node, body?: Node[]): Annotation[] {
  const own = parseAnnotations(node);
  if (body && body.length > 0) return [...own, ...parseAnnotations(body[0])];
  return own;
}

// ── Type declaration extraction ──────────────────────────────

function extractTypeDecl(decl: TypeAliasDeclaration): TypeDeclInfo | null {
  const name = decl.getName();
  const type = decl.getType();

  // String literal union: type State = "idle" | "connecting" | ...
  if (type.isUnion()) {
    const members = type.getUnionTypes();

    // All string literals → string union
    if (members.every(m => m.isStringLiteral())) {
      return {
        name,
        kind: "string-union",
        values: members.map(m => m.getLiteralValue() as string),
      };
    }

    // Object types with a common discriminant → discriminated union
    if (members.every(m => m.isObject())) {
      const discriminant = findDiscriminant(members);
      if (discriminant) {
        const variants: VariantInfo[] = members.map(m => {
          const tagProp = m.getProperty(discriminant);
          const tagType = tagProp?.getTypeAtLocation(decl);
          const tag = tagType?.getLiteralValue() as string;
          const fields: { name: string; tsType: string }[] = [];
          for (const prop of m.getProperties()) {
            if (prop.getName() === discriminant) continue;
            const propType = prop.getTypeAtLocation(decl);
            fields.push({ name: prop.getName(), tsType: typeToString(propType) });
          }
          return { name: tag, fields };
        });
        return { name, kind: "discriminated-union", discriminant, variants };
      }
    }
  }

  // Plain object type: type Foo = { x: number; y: boolean }
  if (type.isObject()) {
    return extractRecord(name, type, decl);
  }

  return null;
}

function extractInterface(decl: InterfaceDeclaration): TypeDeclInfo | null {
  return extractRecord(decl.getName(), decl.getType(), decl);
}

function extractRecord(name: string, type: Type, locationNode: Node): TypeDeclInfo | null {
  const props = type.getProperties();
  if (props.length === 0) return null;
  const fields: { name: string; tsType: string }[] = [];
  for (const prop of props) {
    const propType = prop.getTypeAtLocation(locationNode);
    fields.push({ name: prop.getName(), tsType: typeToString(propType) });
  }
  return { name, kind: "record", fields };
}

/** Find the discriminant field: a property present in all members with distinct string literal types. */
function findDiscriminant(members: Type[]): string | null {
  if (members.length === 0) return null;
  const firstProps = members[0].getProperties();
  for (const prop of firstProps) {
    const name = prop.getName();
    const allHave = members.every(m => {
      const p = m.getProperty(name);
      if (!p) return false;
      const t = p.getDeclarations()[0] ? p.getTypeAtLocation(p.getDeclarations()[0]) : null;
      return t?.isStringLiteral() ?? false;
    });
    if (allHave) return name;
  }
  return null;
}

function typeToString(type: Type): string {
  if (type.isNumber()) return "number";
  if (type.isString()) return "string";
  if (type.isBoolean()) return "boolean";
  // For named types, use the symbol name (avoids full import paths)
  const symbol = type.getSymbol() ?? type.getAliasSymbol();
  if (symbol) return symbol.getName();
  return type.getText();
}

// ── Statement extraction ────────────────────��────────────────

function extractStmts(stmts: Node[]): StmtSpec[] {
  const result: StmtSpec[] = [];
  for (const s of stmts) {
    const line = s.getStartLineNumber();

    if (Node.isVariableStatement(s)) {
      for (const d of s.getDeclarations()) {
        const declType = d.getType();
        result.push({
          kind: "let", name: d.getName(), mutable: s.getDeclarationKind() === "let",
          type: typeToString(declType), init: d.getInitializer()?.getText() ?? "", line,
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

    if (Node.isSwitchStatement(s)) {
      const exprText = s.getExpression().getText();
      // Check for discriminant pattern: switch (x.tag) or switch (x)
      const dotIdx = exprText.lastIndexOf(".");
      const varName = dotIdx >= 0 ? exprText.slice(0, dotIdx) : exprText;
      const field = dotIdx >= 0 ? exprText.slice(dotIdx + 1) : "";

      const cases: { label: string; body: StmtSpec[] }[] = [];
      let defaultBody: StmtSpec[] = [];

      for (const clause of s.getClauses()) {
        if (Node.isCaseClause(clause)) {
          const label = clause.getExpression().getText().replace(/^["']|["']$/g, "");
          // Filter out break statements from the body
          const bodyStmts = clause.getStatements().filter(s => !Node.isBreakStatement(s));
          cases.push({ label, body: extractStmts(bodyStmts) });
        } else {
          // default clause
          const bodyStmts = clause.getStatements().filter(s => !Node.isBreakStatement(s));
          defaultBody = extractStmts(bodyStmts);
        }
      }

      result.push({ kind: "switch", expr: varName, discriminant: field, cases, defaultBody, line });
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

// ── Function extraction ──────────────────���───────────────────

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

// ── Module extraction ────────���───────────────────────────────

export function extractModule(sourceFile: SourceFile): ModuleSpec {
  const typeDecls: TypeDeclInfo[] = [];
  for (const ta of sourceFile.getTypeAliases()) {
    const info = extractTypeDecl(ta);
    if (info) typeDecls.push(info);
  }
  for (const iface of sourceFile.getInterfaces()) {
    const info = extractInterface(iface);
    if (info) typeDecls.push(info);
  }

  return {
    file: sourceFile.getFilePath(),
    typeDecls,
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
