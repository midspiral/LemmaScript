/**
 * Extract — ts-morph → Raw IR.
 *
 * Produces structured AST nodes, not strings.
 * The only strings are //@ annotation expressions (parsed later by specparser).
 */

import { Project, Node, FunctionDeclaration, InterfaceDeclaration, SourceFile, TypeAliasDeclaration, Type, SyntaxKind, Expression } from "ts-morph";
import type { TypeDeclInfo, VariantInfo } from "./types.js";
import type { RawExpr, RawStmt, RawFunction, RawModule } from "./rawir.js";

// ── Expression extraction ────────────────────────────────────

function extractExpr(node: Expression): RawExpr {
  // Numeric literal
  if (Node.isNumericLiteral(node)) {
    return { kind: "num", value: Number(node.getLiteralValue()) };
  }

  // String literal
  if (Node.isStringLiteral(node)) {
    return { kind: "str", value: node.getLiteralValue() };
  }

  // Boolean literals: true, false
  if (Node.isTrueLiteral(node)) return { kind: "bool", value: true };
  if (Node.isFalseLiteral(node)) return { kind: "bool", value: false };

  // Identifier
  if (Node.isIdentifier(node)) {
    return { kind: "var", name: node.getText() };
  }

  // Property access: x.foo
  if (Node.isPropertyAccessExpression(node)) {
    return { kind: "field", obj: extractExpr(node.getExpression()), field: node.getName() };
  }

  // Element access: arr[i]
  if (Node.isElementAccessExpression(node)) {
    const arg = node.getArgumentExpression();
    if (!arg) throw new Error(`Missing index in element access: ${node.getText()}`);
    return { kind: "index", obj: extractExpr(node.getExpression()), idx: extractExpr(arg) };
  }

  // Call expression: f(a, b)
  if (Node.isCallExpression(node)) {
    return {
      kind: "call",
      fn: extractExpr(node.getExpression()),
      args: node.getArguments().map(a => extractExpr(a as Expression)),
    };
  }

  // Binary expression: a + b, a === b, etc.
  if (Node.isBinaryExpression(node)) {
    const op = node.getOperatorToken().getText();
    // Assignment: a = b → handled at statement level, but can appear in expressions
    if (op === "=") {
      // This is an assignment expression; extract as binop for now
      return { kind: "binop", op: "=", left: extractExpr(node.getLeft()), right: extractExpr(node.getRight()) };
    }
    return { kind: "binop", op, left: extractExpr(node.getLeft()), right: extractExpr(node.getRight()) };
  }

  // Prefix unary: !x, -x
  if (Node.isPrefixUnaryExpression(node)) {
    const opToken = node.getOperatorToken();
    let op: string;
    switch (opToken) {
      case SyntaxKind.ExclamationToken: op = "!"; break;
      case SyntaxKind.MinusToken: op = "-"; break;
      case SyntaxKind.PlusToken: op = "+"; break;
      default: op = String(opToken);
    }
    return { kind: "unop", op, expr: extractExpr(node.getOperand()) };
  }

  // Parenthesized: (x)
  if (Node.isParenthesizedExpression(node)) {
    return extractExpr(node.getExpression());
  }

  // Object literal: { res: true, done: false }
  if (Node.isObjectLiteralExpression(node)) {
    const fields: { name: string; value: RawExpr }[] = [];
    for (const prop of node.getProperties()) {
      if (Node.isPropertyAssignment(prop)) {
        const init = prop.getInitializer();
        if (init) fields.push({ name: prop.getName(), value: extractExpr(init) });
      }
    }
    return { kind: "record", fields };
  }

  throw new Error(`Unsupported expression: ${node.getText()}`);
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

  if (type.isUnion()) {
    const members = type.getUnionTypes();
    if (members.every(m => m.isStringLiteral())) {
      return { name, kind: "string-union", values: members.map(m => m.getLiteralValue() as string) };
    }
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
            fields.push({ name: prop.getName(), tsType: typeToString(prop.getTypeAtLocation(decl)) });
          }
          return { name: tag, fields };
        });
        return { name, kind: "discriminated-union", discriminant, variants };
      }
    }
  }

  if (type.isObject()) return extractRecord(name, type, decl);
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
    fields.push({ name: prop.getName(), tsType: typeToString(prop.getTypeAtLocation(locationNode)) });
  }
  return { name, kind: "record", fields };
}

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
  if (type.isArray()) {
    const elem = type.getArrayElementTypeOrThrow();
    return `${typeToString(elem)}[]`;
  }
  const symbol = type.getSymbol() ?? type.getAliasSymbol();
  if (symbol) return symbol.getName();
  return type.getText();
}

// ── Statement extraction ─────────────────────────────────────

function extractStmts(stmts: Node[]): RawStmt[] {
  const result: RawStmt[] = [];
  for (const s of stmts) {
    const line = s.getStartLineNumber();

    if (Node.isVariableStatement(s)) {
      for (const d of s.getDeclarations()) {
        const declType = d.getType();
        const init = d.getInitializer();
        result.push({
          kind: "let",
          name: d.getName(),
          mutable: s.getDeclarationKind() === "let",
          tsType: typeToString(declType),
          init: init ? extractExpr(init) : { kind: "var", name: "default" },
          line,
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
        cond: extractExpr(s.getExpression()),
        invariants: annots.filter(a => a.kind === "invariant").map(a => a.expr),
        decreases: annots.find(a => a.kind === "decreases")?.expr ?? null,
        doneWith: annots.find(a => a.kind === "done_with")?.expr ?? null,
        body: extractStmts(bodyStmts),
        line,
      });
      continue;
    }

    if (Node.isForOfStatement(s)) {
      const init = s.getInitializer();
      const varName = Node.isVariableDeclarationList(init) ? init.getDeclarations()[0]?.getName() ?? "_" : "_";
      const bodyNode = s.getStatement();
      const bodyStmts = Node.isBlock(bodyNode) ? bodyNode.getStatements() : [bodyNode];
      const annots = collectAnnotations(s, bodyStmts);
      result.push({
        kind: "forof",
        varName,
        iterable: extractExpr(s.getExpression()),
        invariants: annots.filter(a => a.kind === "invariant").map(a => a.expr),
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
        cond: extractExpr(s.getExpression()),
        then: Node.isBlock(thenNode) ? extractStmts(thenNode.getStatements()) : extractStmts([thenNode]),
        else: elseNode
          ? Node.isBlock(elseNode) ? extractStmts(elseNode.getStatements()) : extractStmts([elseNode])
          : [],
        line,
      });
      continue;
    }

    if (Node.isSwitchStatement(s)) {
      const exprNode = s.getExpression();
      const exprAst = extractExpr(exprNode);
      const discriminant = exprAst.kind === "field" ? exprAst.field : "";
      const switchExpr = exprAst.kind === "field" ? exprAst.obj : exprAst;

      const cases: { label: string; body: RawStmt[] }[] = [];
      let defaultBody: RawStmt[] = [];
      for (const clause of s.getClauses()) {
        if (Node.isCaseClause(clause)) {
          const label = clause.getExpression().getText().replace(/^["']|["']$/g, "");
          const bodyStmts = clause.getStatements().filter(st => !Node.isBreakStatement(st));
          cases.push({ label, body: extractStmts(bodyStmts) });
        } else {
          const bodyStmts = clause.getStatements().filter(st => !Node.isBreakStatement(st));
          defaultBody = extractStmts(bodyStmts);
        }
      }
      result.push({ kind: "switch", expr: switchExpr, discriminant, cases, defaultBody, line });
      continue;
    }

    if (Node.isReturnStatement(s)) {
      const expr = s.getExpression();
      result.push({ kind: "return", value: expr ? extractExpr(expr) : { kind: "var", name: "()" }, line });
      continue;
    }

    if (Node.isBreakStatement(s)) {
      result.push({ kind: "break", line });
      continue;
    }

    if (Node.isContinueStatement(s)) {
      result.push({ kind: "continue", line });
      continue;
    }

    if (Node.isExpressionStatement(s)) {
      const expr = s.getExpression();
      if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === "=") {
        result.push({ kind: "assign", target: expr.getLeft().getText(), value: extractExpr(expr.getRight()), line });
      } else {
        result.push({ kind: "expr", expr: extractExpr(expr), line });
      }
      continue;
    }

    throw new Error(`Unsupported statement at line ${line}: ${s.getText().slice(0, 80)}`);
  }
  return result;
}

// ── Function extraction ──────────────────────────────────────

function extractFunction(fn: FunctionDeclaration): RawFunction {
  const body = fn.getBody();
  if (!body || !Node.isBlock(body)) throw new Error(`${fn.getName()}: function body is not a block`);
  const bodyStmts = body.getStatements();
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
    params: fn.getParameters().map(p => ({ name: p.getName(), tsType: p.getTypeNode()?.getText() ?? "unknown" })),
    returnType: fn.getReturnTypeNode()?.getText() ?? "unknown",
    requires: annots.filter(a => a.kind === "requires").map(a => a.expr),
    ensures: annots.filter(a => a.kind === "ensures").map(a => a.expr),
    typeAnnotations,
    body: extractStmts(bodyStmts),
    line: fn.getStartLineNumber(),
  };
}

// ── Module extraction ────────────────────────────────────────

export function extractModule(sourceFile: SourceFile): RawModule {
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
