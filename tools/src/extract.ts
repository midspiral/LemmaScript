/**
 * Extract — ts-morph → Raw IR.
 *
 * Produces structured AST nodes, not strings.
 * The only strings are //@ annotation expressions (parsed later by specparser).
 */

import { Project, Node, FunctionDeclaration, InterfaceDeclaration, SourceFile, TypeAliasDeclaration, Type, SyntaxKind, Expression, ElementAccessExpression, ScriptTarget } from "ts-morph";
import type { TypeDeclInfo, VariantInfo } from "./types.js";
import type { RawExpr, RawStmt, RawFunction, RawModule, RawClass, RawGhostLet, RawGhostAssign } from "./rawir.js";

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

  // this
  if (node.getKind() === SyntaxKind.ThisKeyword) {
    return { kind: "var", name: "this" };
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

  // Arrow function: (x) => expr or (x) => { stmts }
  if (Node.isArrowFunction(node)) {
    const params = node.getParameters().map(p => {
      const typeNode = p.getTypeNode();
      return { name: p.getName(), tsType: typeNode ? typeNode.getText() : undefined };
    });
    const body = node.getBody();
    if (Node.isExpression(body)) {
      return { kind: "lambda", params, body: extractExpr(body) };
    }
    if (Node.isBlock(body)) {
      return { kind: "lambda", params, body: extractStmts(body.getStatements()) };
    }
    throw new Error(`Unsupported arrow function body: ${node.getText().slice(0, 80)}`);
  }

  // Array literal: [a, b, c] → arrayLiteral, [...arr, elem] → push(arr, elem)
  if (Node.isArrayLiteralExpression(node)) {
    const elems = node.getElements();
    // [...arr, elem] → push(arr, elem)
    if (elems.length === 2 && Node.isSpreadElement(elems[0])) {
      return { kind: "call", fn: { kind: "field", obj: extractExpr(elems[0].getExpression()), field: "push" }, args: [extractExpr(elems[1])] };
    }
    // [a, b, c] or [] → arrayLiteral
    return { kind: "arrayLiteral", elems: elems.map(e => extractExpr(e as Expression)) };
  }

  // Object literal: { res: true, done: false } or { ...obj, res: true }
  if (Node.isObjectLiteralExpression(node)) {
    let spread: RawExpr | null = null;
    const fields: { name: string; value: RawExpr }[] = [];
    for (const prop of node.getProperties()) {
      if (Node.isSpreadAssignment(prop)) {
        spread = extractExpr(prop.getExpression());
      } else if (Node.isPropertyAssignment(prop)) {
        const init = prop.getInitializer();
        if (init) fields.push({ name: prop.getName(), value: extractExpr(init) });
      }
    }
    return { kind: "record", spread, fields };
  }

  // Ternary: cond ? then : else
  if (Node.isConditionalExpression(node)) {
    return { kind: "conditional", cond: extractExpr(node.getCondition()), then: extractExpr(node.getWhenTrue()), else: extractExpr(node.getWhenFalse()) };
  }

  // Non-null assertion: expr!
  if (Node.isNonNullExpression(node)) {
    return { kind: "nonNull", expr: extractExpr(node.getExpression()) };
  }

  // new Map<K,V>() / new Set<T>() — with or without initializer
  if (Node.isNewExpression(node)) {
    const name = node.getExpression().getText();
    if (name === "Map" || name === "Set") {
      const typeArgs = node.getTypeArguments();
      const tsType = typeArgs && typeArgs.length > 0
        ? `${name}<${typeArgs.map(t => t.getText()).join(", ")}>`
        : name;
      const args = node.getArguments();
      // new Map(arr.map(fn)) — map-from-array constructor
      if (name === "Map" && args && args.length === 1) {
        return { kind: "call", fn: { kind: "var", name: "__mapFromArray" }, args: [extractExpr(args[0] as Expression)] };
      }
      return { kind: "emptyCollection", collectionType: name as "Map" | "Set", tsType };
    }
  }

  // As-expression: expr as T — strip the type assertion
  if (Node.isAsExpression(node)) {
    return extractExpr(node.getExpression());
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
  // Collect field type overrides from trailing //@ type annotations
  const overrides = new Map<string, string>();
  for (const member of decl.getMembers()) {
    if (Node.isPropertySignature(member)) {
      const text = member.getTrailingCommentRanges().map(r => r.getText()).join(" ");
      const match = text.match(/\/\/@ type (\w+)/);
      if (match) overrides.set(member.getName(), match[1]);
    }
  }
  return extractRecord(decl.getName(), decl.getType(), decl, overrides);
}

function extractRecord(name: string, type: Type, locationNode: Node, overrides?: Map<string, string>): TypeDeclInfo | null {
  const props = type.getProperties();
  if (props.length === 0) return null;
  const fields: { name: string; tsType: string }[] = [];
  for (const prop of props) {
    const override = overrides?.get(prop.getName());
    const tsType = override ?? typeToString(prop.getTypeAtLocation(locationNode));
    fields.push({ name: prop.getName(), tsType });
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
  if (type.isUndefined()) return "undefined";
  if (type.isNumber()) return "number";
  if (type.isString()) return "string";
  if (type.isBoolean()) return "boolean";
  // Named type alias (e.g. Priority = "low" | "medium" | "high") — use the alias name
  if (type.getAliasSymbol()) {
    const name = type.getAliasSymbol()!.getName();
    const args = type.getAliasTypeArguments();
    if (args.length > 0) return `${name}<${args.map(t => typeToString(t)).join(", ")}>`;
    return name;
  }
  if (type.isUnion()) {
    return type.getUnionTypes().map(typeToString).join(" | ");
  }
  if (type.isArray()) {
    const elem = type.getArrayElementTypeOrThrow();
    return `${typeToString(elem)}[]`;
  }
  const symbol = type.getSymbol() ?? type.getAliasSymbol();
  if (symbol) {
    const name = symbol.getName();
    const typeArgs = type.getTypeArguments();
    if (typeArgs.length > 0) {
      return `${name}<${typeArgs.map(t => typeToString(t)).join(", ")}>`;
    }
    return name;
  }
  return type.getText();
}

const COMPOUND_OPS: Record<string, string> = {
  "+=": "+", "-=": "-", "*=": "*", "/=": "/", "%=": "%",
};

// ── Statement extraction ─────────────────────────────────────

/** Parse ghost and assert annotations from comment ranges. */
function parseSpecComments(ranges: ReturnType<Node["getLeadingCommentRanges"]>, line: number): (RawGhostLet | RawGhostAssign | import("./rawir.js").RawAssert)[] {
  const result: (RawGhostLet | RawGhostAssign | import("./rawir.js").RawAssert)[] = [];
  for (const range of ranges) {
    const text = range.getText().trim();
    if (!text.startsWith(PREFIX)) continue;
    const content = text.slice(PREFIX.length);
    // assert expr
    if (content.startsWith("assert ")) {
      result.push({ kind: "assert", expr: content.slice(7).trim(), line });
      continue;
    }
    if (!content.startsWith("ghost ")) continue;
    const ghostBody = content.slice(6).trim();
    // ghost let varName: type = expr  OR  ghost let varName = expr
    const letMatch = ghostBody.match(/^let\s+(\w+)(?:\s*:\s*(\w+))?\s*=\s*(.+)$/);
    if (letMatch) {
      result.push({ kind: "ghostLet", name: letMatch[1], tsType: letMatch[2] ?? null, init: letMatch[3].trim(), line });
      continue;
    }
    // ghost varName = expr
    const assignMatch = ghostBody.match(/^(\w+)\s*=\s*(.+)$/);
    if (assignMatch) {
      result.push({ kind: "ghostAssign", target: assignMatch[1], value: assignMatch[2].trim(), line });
    }
  }
  return result;
}

function extractStmts(stmts: Node[]): RawStmt[] {
  const result: RawStmt[] = [];
  for (const s of stmts) {
    const line = s.getStartLineNumber();

    // Ghost annotations from leading comments → inject before this statement
    result.push(...parseSpecComments(s.getLeadingCommentRanges(), line));

    if (Node.isVariableStatement(s)) {
      const isHavoc = s.getLeadingCommentRanges().some(r => r.getText().trim() === '//@ havoc');
      for (const d of s.getDeclarations()) {
        const declType = d.getType();
        const init = isHavoc
          ? { kind: "havoc" as const }
          : (d.getInitializer() ? extractExpr(d.getInitializer()!) : { kind: "var" as const, name: "default" });
        result.push({
          kind: "let",
          name: d.getName(),
          mutable: s.getDeclarationKind() === "let",
          tsType: typeToString(declType),
          init,
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
      const names: string[] = [];
      if (Node.isVariableDeclarationList(init)) {
        const decl = init.getDeclarations()[0];
        const nameNode = decl?.getNameNode();
        if (nameNode && Node.isArrayBindingPattern(nameNode)) {
          for (const elem of nameNode.getElements()) {
            if (Node.isBindingElement(elem)) names.push(elem.getNameNode().getText());
          }
        } else {
          names.push(decl?.getName() ?? "_");
        }
      } else {
        names.push("_");
      }
      const bodyNode = s.getStatement();
      const bodyStmts = Node.isBlock(bodyNode) ? bodyNode.getStatements() : [bodyNode];
      const annots = collectAnnotations(s, bodyStmts);
      result.push({
        kind: "forof",
        names,
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
      // arr[i] = v → arr = arr.with(i, v)
      if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === "=" && Node.isElementAccessExpression(expr.getLeft())) {
        const left = expr.getLeft() as ElementAccessExpression;
        const obj = extractExpr(left.getExpression());
        const idx = extractExpr(left.getArgumentExpression()!);
        const val = extractExpr(expr.getRight());
        const target = left.getExpression().getText();
        const withCall: RawExpr = { kind: "call", fn: { kind: "field", obj, field: "with" }, args: [idx, val] };
        result.push({ kind: "assign", target, value: withCall, line });
      // x = e
      } else if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === "=") {
        result.push({ kind: "assign", target: expr.getLeft().getText(), value: extractExpr(expr.getRight()), line });
      // x += e, x -= e, etc.
      } else if (Node.isBinaryExpression(expr) && COMPOUND_OPS[expr.getOperatorToken().getText()]) {
        const op = COMPOUND_OPS[expr.getOperatorToken().getText()];
        const target = expr.getLeft().getText();
        result.push({ kind: "assign", target, value: { kind: "binop", op, left: { kind: "var", name: target }, right: extractExpr(expr.getRight()) }, line });
      // i++, i--
      } else if (Node.isPostfixUnaryExpression(expr)) {
        const target = expr.getOperand().getText();
        const op = expr.getOperatorToken() === SyntaxKind.PlusPlusToken ? "+" : "-";
        result.push({ kind: "assign", target, value: { kind: "binop", op, left: { kind: "var", name: target }, right: { kind: "num", value: 1 } }, line });
      // ++i, --i
      } else if (Node.isPrefixUnaryExpression(expr) && (expr.getOperatorToken() === SyntaxKind.PlusPlusToken || expr.getOperatorToken() === SyntaxKind.MinusMinusToken)) {
        const target = expr.getOperand().getText();
        const op = expr.getOperatorToken() === SyntaxKind.PlusPlusToken ? "+" : "-";
        result.push({ kind: "assign", target, value: { kind: "binop", op, left: { kind: "var", name: target }, right: { kind: "num", value: 1 } }, line });
      } else {
        result.push({ kind: "expr", expr: extractExpr(expr), line });
      }
      continue;
    }

    if (Node.isThrowStatement(s)) {
      result.push({ kind: "throw", line });
      continue;
    }

    throw new Error(`Unsupported statement at line ${line}: ${s.getText().slice(0, 80)}`);
  }
  // Ghost comments after the last statement (before closing brace) appear as sibling trivia nodes
  if (stmts.length > 0) {
    const last = stmts[stmts.length - 1];
    const line = last.getStartLineNumber();
    for (const sib of last.getNextSiblings()) {
      const text = sib.getText().trim();
      if (!text.startsWith(PREFIX)) continue;
      const content = text.slice(PREFIX.length);
      // assert expr
      if (content.startsWith("assert ")) {
        result.push({ kind: "assert", expr: content.slice(7).trim(), line });
        continue;
      }
      if (!content.startsWith("ghost ")) continue;
      const ghostBody = content.slice(6).trim();
      const letMatch = ghostBody.match(/^let\s+(\w+)(?:\s*:\s*(\w+))?\s*=\s*(.+)$/);
      if (letMatch) {
        result.push({ kind: "ghostLet", name: letMatch[1], tsType: letMatch[2] ?? null, init: letMatch[3].trim(), line });
        continue;
      }
      const assignMatch = ghostBody.match(/^(\w+)\s*=\s*(.+)$/);
      if (assignMatch) {
        result.push({ kind: "ghostAssign", target: assignMatch[1], value: assignMatch[2].trim(), line });
      }
    }
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
  // Extract type declarations in source order to respect dependencies
  for (const stmt of sourceFile.getStatements()) {
    if (Node.isTypeAliasDeclaration(stmt)) {
      const info = extractTypeDecl(stmt);
      if (info) typeDecls.push(info);
    } else if (Node.isInterfaceDeclaration(stmt)) {
      const info = extractInterface(stmt);
      if (info) typeDecls.push(info);
    }
  }

  // If any function has //@ verify, only extract those (brownfield mode).
  // Otherwise extract all functions (backwards-compatible with existing examples).
  const allFns = sourceFile.getFunctions();
  const hasVerifyDirective = allFns.some(fn => fn.getFullText().includes('//@ verify'));
  const fnsToExtract = hasVerifyDirective
    ? allFns.filter(fn => fn.getFullText().includes('//@ verify'))
    : allFns;

  const functions = fnsToExtract.map(extractFunction);

  // Resolve imported types: extract types referenced in function signatures but not in this file
  const knownTypes = new Set(typeDecls.map(d => d.name));
  const builtins = new Set(["Map", "Set", "Array", "String", "Number", "Boolean", "Promise", "Date", "RegExp", "Error"]);
  function resolveType(t: Type, locationNode: Node) {
    // Unwrap arrays and generics to find user-defined types
    if (t.isArray()) { resolveType(t.getArrayElementTypeOrThrow(), locationNode); return; }
    for (const arg of t.getTypeArguments()) resolveType(arg, locationNode);
    const sym = t.getSymbol() ?? t.getAliasSymbol();
    const name = sym?.getName();
    if (name && !knownTypes.has(name) && !builtins.has(name) && t.isObject()) {
      const info = extractRecord(name, t, locationNode);
      if (info) { typeDecls.push(info); knownTypes.add(name); }
    }
  }
  for (const fn of fnsToExtract) {
    for (const p of fn.getParameters()) resolveType(p.getType(), p);
  }

  // Extract classes with //@ verify methods
  const classes: RawClass[] = [];
  for (const cls of sourceFile.getClasses()) {
    const methods: RawFunction[] = [];
    for (const method of cls.getMethods()) {
      if (!method.getFullText().includes('//@ verify')) continue;
      methods.push(extractFunction(method as any));
    }
    if (methods.length === 0) continue;
    const fields: { name: string; tsType: string }[] = [];
    for (const prop of cls.getProperties()) {
      fields.push({ name: prop.getName(), tsType: typeToString(prop.getType()) });
    }
    classes.push({ name: cls.getName() ?? "Anonymous", fields, methods });
  }

  return {
    file: sourceFile.getFilePath(),
    typeDecls,
    functions,
    classes,
  };
}

// ── Main ─────────────────────────────────────────────────────

if (process.argv[1]?.match(/extract\.(ts|js)$/)) {
  const file = process.argv[2];
  if (!file) { console.error("Usage: extract <file.ts>"); process.exit(1); }
  const proj = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"] } });
  console.log(JSON.stringify(extractModule(proj.addSourceFileAtPath(file)), null, 2));
}
