/**
 * Extract — ts-morph → Raw IR.
 *
 * Produces structured AST nodes, not strings.
 * The only strings are //@ annotation expressions (parsed later by specparser).
 */

import { Project, Node, FunctionDeclaration, InterfaceDeclaration, SourceFile, TypeAliasDeclaration, Type, SyntaxKind, Expression, ElementAccessExpression, ScriptTarget } from "ts-morph";
import type { TypeDeclInfo, VariantInfo } from "./types.js";
import type { RawExpr, RawStmt, RawFunction, RawModule, RawClass, RawConst, RawGhostLet, RawGhostAssign } from "./rawir.js";

// ── Expression extraction ────────────────────────────────────

/** When set, calls whose function/method name matches this key are replaced with havoc. */
let _havocKey: string | null = null;

function extractExpr(node: Expression): RawExpr {
  // Havoc key matching: replace matching calls with havoc expression
  if (_havocKey && Node.isCallExpression(node)) {
    const fnExpr = node.getExpression();
    const name = Node.isPropertyAccessExpression(fnExpr) ? fnExpr.getName()
      : Node.isIdentifier(fnExpr) ? fnExpr.getText()
      : null;
    if (name === _havocKey) {
      return { kind: "havoc", tsType: typeToString(node.getType()) };
    }
  }

  // Numeric literal
  if (Node.isNumericLiteral(node)) {
    return { kind: "num", value: Number(node.getLiteralValue()) };
  }

  // BigInt literal (e.g. 32n, 0xffffn) — treat as integer
  if (Node.isBigIntLiteral(node)) {
    const text = node.getText().replace(/n$/, '');
    return { kind: "num", value: Number(text) };
  }

  // Template literal: `foo${x}bar` → "foo" + x + "bar"
  if (Node.isTemplateExpression(node)) {
    const parts: RawExpr[] = [];
    const head = node.getHead().getLiteralText();
    if (head) parts.push({ kind: "str", value: head });
    for (const span of node.getTemplateSpans()) {
      parts.push(extractExpr(span.getExpression()));
      const text = span.getLiteral().getLiteralText();
      if (text) parts.push({ kind: "str", value: text });
    }
    return parts.reduce((left, right) => ({ kind: "binop", op: "+", left, right }));
  }

  // No-substitution template literal: `hello` → "hello"
  if (Node.isNoSubstitutionTemplateLiteral(node)) {
    return { kind: "str", value: node.getLiteralText() };
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
      } else if (Node.isShorthandPropertyAssignment(prop)) {
        const name = prop.getName();
        fields.push({ name, value: { kind: "var", name } });
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

function extractTypeDecl(decl: TypeAliasDeclaration, extraDecls?: TypeDeclInfo[]): TypeDeclInfo | null {
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

  if (type.isObject() || type.isIntersection()) return extractRecord(name, type, decl, undefined, extraDecls);
  return null;
}

function extractInterface(decl: InterfaceDeclaration, extraDecls?: TypeDeclInfo[]): TypeDeclInfo | null {
  // Collect field type overrides from trailing //@ type annotations
  const overrides = new Map<string, string>();
  for (const member of decl.getMembers()) {
    if (Node.isPropertySignature(member)) {
      const text = member.getTrailingCommentRanges().map(r => r.getText()).join(" ");
      const match = text.match(/\/\/@ type (\w+)/);
      if (match) overrides.set(member.getName(), match[1]);
    }
  }
  return extractRecord(decl.getName(), decl.getType(), decl, overrides, extraDecls);
}

function extractRecord(name: string, type: Type, locationNode: Node, overrides?: Map<string, string>, extraDecls?: TypeDeclInfo[]): TypeDeclInfo | null {
  const props = type.getProperties();
  if (props.length === 0) return null;
  const fields: { name: string; tsType: string }[] = [];
  for (const prop of props) {
    const override = overrides?.get(prop.getName());
    if (override) { fields.push({ name: prop.getName(), tsType: override }); continue; }

    const propType = prop.getTypeAtLocation(locationNode);
    let tsType = typeToString(propType);

    // Inline anonymous object types: ts-morph names them __type.
    // Generate a synthetic named record and reference it by name instead.
    if (extraDecls && tsType.includes("__type")) {
      let innerType = propType;
      let isOptional = false;
      if (propType.isUnion()) {
        const uTypes = propType.getUnionTypes();
        const nonUndef = uTypes.filter(t => !t.isUndefined());
        if (uTypes.some(t => t.isUndefined()) && nonUndef.length === 1) {
          innerType = nonUndef[0];
          isOptional = true;
        }
      }
      if (innerType.isObject() && !innerType.isArray()) {
        const fName = prop.getName();
        const synName = name + fName.charAt(0).toUpperCase() + fName.slice(1);
        const extracted = extractRecord(synName, innerType, locationNode, undefined, extraDecls);
        if (extracted) {
          extraDecls.push(extracted);
          tsType = isOptional ? `${synName} | undefined` : synName;
        }
      }
    }

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
  if (type.isNumber() || type.isNumberLiteral()) return "number";
  if (type.isBigInt() || type.isBigIntLiteral()) return "bigint";
  if (type.isString() || type.isStringLiteral()) return "string";
  if (type.isBoolean()) return "boolean";
  // Named type alias (e.g. Priority = "low" | "medium" | "high") — use the alias name
  if (type.getAliasSymbol()) {
    const name = type.getAliasSymbol()!.getName();
    const args = type.getAliasTypeArguments();
    if (args.length > 0) return `${name}<${args.map(t => typeToString(t)).join(", ")}>`;
    return name;
  }
  if (type.isUnion()) {
    const parts = [...new Set(type.getUnionTypes().map(typeToString))];
    return parts.join(" | ");
  }
  if (type.isTuple()) {
    return `[${type.getTupleElements().map(t => typeToString(t)).join(", ")}]`;
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
      const havocMatch = s.getLeadingCommentRanges()
        .map(r => r.getText().trim().match(/^\/\/@ havoc(?:\s+(\S+))?$/))
        .find(m => m !== null);
      const havocKey = havocMatch?.[1] ?? null;
      const isHavoc = !!havocMatch;
      for (const d of s.getDeclarations()) {
        const declType = d.getType();
        let init: RawExpr;
        if (isHavoc && !havocKey) {
          init = { kind: "havoc", tsType: typeToString(declType) };
        } else {
          const initializer = d.getInitializer();
          _havocKey = havocKey;
          init = initializer ? extractExpr(initializer) : { kind: "var" as const, name: "default" };
          _havocKey = null;
        }
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

function extractFunction(fn: FunctionDeclaration, parentAnnotations?: Annotation[]): RawFunction {
  const body = fn.getBody();

  // Expression-body arrow: wrap in implicit return
  let extractedBody: RawStmt[];
  let annots: Annotation[];
  if (body && !Node.isBlock(body)) {
    const expr = extractExpr(body as Expression);
    extractedBody = [{ kind: "return", value: expr, line: body.getStartLineNumber() }];
    annots = parentAnnotations ?? collectAnnotations(fn);
  } else if (body && Node.isBlock(body)) {
    const bodyStmts = body.getStatements();
    extractedBody = extractStmts(bodyStmts);
    annots = collectAnnotations(fn, bodyStmts);
  } else {
    throw new Error(`${(fn as any).getName?.() ?? "arrow"}: function has no body`);
  }

  const typeAnnotations: { name: string; type: string }[] = [];
  for (const a of annots) {
    if (a.kind === "type") {
      const parts = a.expr.split(/\s+/);
      if (parts.length === 2) typeAnnotations.push({ name: parts[0], type: parts[1] });
    }
  }

  return {
    name: (fn as any).getName?.() ?? "<anonymous>",
    params: fn.getParameters().flatMap(p => {
      // Flatten destructured object params into individual params
      const nameNode = p.getNameNode();
      if (Node.isObjectBindingPattern(nameNode)) {
        const type = p.getType();
        return nameNode.getElements().map(el => {
          const name = el.getName();
          const propType = type.getProperty(name)?.getTypeAtLocation(p);
          return { name, tsType: propType ? typeToString(propType) : "unknown" };
        });
      }
      return [{ name: p.getName(), tsType: p.getTypeNode()?.getText() ?? "unknown" }];
    }),
    returnType: fn.getReturnTypeNode()?.getText() ?? "unknown",
    requires: annots.filter(a => a.kind === "requires").map(a => a.expr),
    ensures: annots.filter(a => a.kind === "ensures").map(a => a.expr),
    typeAnnotations,
    body: extractedBody,
    line: fn.getStartLineNumber(),
  };
}

// ── Module extraction ────────────────────────────────────────

export function extractModule(sourceFile: SourceFile): RawModule {
  const typeDecls: TypeDeclInfo[] = [];
  // Extract type declarations in source order to respect dependencies
  for (const stmt of sourceFile.getStatements()) {
    if (Node.isTypeAliasDeclaration(stmt)) {
      const extra: TypeDeclInfo[] = [];
      const info = extractTypeDecl(stmt, extra);
      typeDecls.push(...extra);
      if (info) typeDecls.push(info);
    } else if (Node.isInterfaceDeclaration(stmt)) {
      const extra: TypeDeclInfo[] = [];
      const info = extractInterface(stmt, extra);
      // Synthetic types from inline objects must precede the parent type
      typeDecls.push(...extra);
      if (info) typeDecls.push(info);
    }
  }

  // Extract module-level const declarations
  const constants: RawConst[] = [];
  for (const stmt of sourceFile.getStatements()) {
    if (Node.isVariableStatement(stmt)) {
      for (const decl of stmt.getDeclarationList().getDeclarations()) {
        if (stmt.getDeclarationList().getFlags() & 2 /* const */) {
          const init = decl.getInitializer();
          // Skip huge string constants — they crash the verifier and have no verification value
          const initType = decl.getType();
          const isHugeString = (initType.isString() || initType.isStringLiteral()) && (init as Expression).getText().length > 200;
          if (init && !isHugeString && !Node.isArrowFunction(init)) {
            try {
              constants.push({
                name: decl.getName(),
                tsType: typeToString(decl.getType()),
                value: extractExpr(init as Expression),
              });
            } catch (e) {
              console.error(`WARNING: skipping const '${decl.getName()}': ${(e as Error).message}`);
            }
          }
        }
      }
    }
  }

  // Collect all function-like declarations: function declarations + const arrow functions
  const allFns: { name: string; node: FunctionDeclaration; parentStmt?: Node }[] = [];
  for (const fn of sourceFile.getFunctions()) {
    allFns.push({ name: fn.getName() ?? "<anonymous>", node: fn });
  }
  // const f = (...) => expr  OR  const f = (...) => { ... }
  for (const stmt of sourceFile.getStatements()) {
    if (Node.isVariableStatement(stmt)) {
      for (const decl of stmt.getDeclarationList().getDeclarations()) {
        const init = decl.getInitializer();
        if (init && Node.isArrowFunction(init)) {
          allFns.push({ name: decl.getName(), node: init as unknown as FunctionDeclaration, parentStmt: stmt });
        }
      }
    }
  }

  // If any function has //@ verify, only extract those (brownfield mode).
  // For expression-body arrows, //@ verify may be on the parent variable statement.
  function hasVerify(f: { node: FunctionDeclaration; parentStmt?: Node }) {
    if (f.node.getFullText().includes('//@ verify')) return true;
    if (f.parentStmt) {
      for (const r of f.parentStmt.getLeadingCommentRanges()) {
        if (r.getText().includes('//@ verify')) return true;
      }
    }
    return false;
  }
  const hasVerifyDirective = allFns.some(hasVerify);
  const fnsToExtract = hasVerifyDirective ? allFns.filter(hasVerify) : allFns;

  const functions = fnsToExtract.map(f => {
    // For expression-body arrows, annotations come from the parent variable statement
    const parentAnnots = f.parentStmt ? parseAnnotations(f.parentStmt) : undefined;
    const raw = extractFunction(f.node, parentAnnots);
    raw.name = f.name;  // use the const name, not "<anonymous>"
    return raw;
  });

  // In brownfield mode, filter consts to only those referenced by verified functions.
  // Types are NOT filtered — they may be needed transitively (e.g. Option from T | undefined).
  if (hasVerifyDirective) {
    const referencedNames = new Set<string>();
    function collectNames(stmts: RawStmt[]) {
      for (const s of stmts) {
        if (s.kind === "let") { collectNamesExpr(s.init); }
        if (s.kind === "assign") { collectNamesExpr(s.value); }
        if (s.kind === "return") { collectNamesExpr(s.value); }
        if (s.kind === "if") { collectNamesExpr(s.cond); collectNames(s.then); collectNames(s.else); }
        if (s.kind === "while") { collectNamesExpr(s.cond); collectNames(s.body); }
        if (s.kind === "forof") { collectNamesExpr(s.iterable); collectNames(s.body); }
        if (s.kind === "expr") { collectNamesExpr(s.expr); }
      }
    }
    function collectNamesExpr(e: RawExpr) {
      if (e.kind === "var") referencedNames.add(e.name);
      if (e.kind === "binop") { collectNamesExpr(e.left); collectNamesExpr(e.right); }
      if (e.kind === "unop") { collectNamesExpr(e.expr); }
      if (e.kind === "call") { collectNamesExpr(e.fn); e.args.forEach(collectNamesExpr); }
      if (e.kind === "field") { collectNamesExpr(e.obj); }
      if (e.kind === "index") { collectNamesExpr(e.obj); collectNamesExpr(e.idx); }
      if (e.kind === "record") { if (e.spread) collectNamesExpr(e.spread); e.fields.forEach(f => collectNamesExpr(f.value)); }
      if (e.kind === "arrayLiteral") { e.elems.forEach(collectNamesExpr); }
      if (e.kind === "conditional") { collectNamesExpr(e.cond); collectNamesExpr(e.then); collectNamesExpr(e.else); }
    }
    for (const fn of functions) {
      for (const p of fn.params) referencedNames.add(p.tsType);
      referencedNames.add(fn.returnType);
      collectNames(fn.body);
      // Also scan spec annotations for identifier references
      for (const spec of [...fn.requires, ...fn.ensures]) {
        for (const m of spec.matchAll(/\b([a-zA-Z_]\w*)\b/g)) {
          referencedNames.add(m[1]);
        }
      }
    }
    constants.splice(0, constants.length, ...constants.filter(c => referencedNames.has(c.name)));
    // Filter types to only those referenced by verified functions (transitive)
    const neededTypes = new Set<string>();
    function markType(name: string) {
      if (neededTypes.has(name)) return;
      const d = typeDecls.find(t => t.name === name);
      if (!d) return;
      neededTypes.add(name);
      for (const f of d.fields ?? [])
        for (const m of f.tsType.matchAll(/\b([A-Z]\w*)\b/g)) markType(m[1]);
      for (const v of d.variants ?? [])
        for (const f of v.fields)
          for (const m of f.tsType.matchAll(/\b([A-Z]\w*)\b/g)) markType(m[1]);
    }
    for (const name of referencedNames) markType(name);
    typeDecls.splice(0, typeDecls.length, ...typeDecls.filter(d => neededTypes.has(d.name)));
  }

  // Resolve imported types: extract types referenced in function signatures but not in this file
  const knownTypes = new Set(typeDecls.map(d => d.name));
  const builtins = new Set(["Map", "Set", "Array", "String", "Number", "Boolean", "Promise", "Date", "RegExp", "Error"]);
  function resolveType(t: Type, locationNode: Node) {
    // Unwrap arrays and generics to find user-defined types
    if (t.isArray()) { resolveType(t.getArrayElementTypeOrThrow(), locationNode); return; }
    // Resolve type aliases (e.g. string unions imported from other files)
    const alias = t.getAliasSymbol();
    if (alias) {
      const aliasName = alias.getName();
      if (!knownTypes.has(aliasName) && !builtins.has(aliasName) && !aliasName.startsWith("__")) {
        const decls = alias.getDeclarations();
        if (decls.length > 0 && Node.isTypeAliasDeclaration(decls[0])) {
          const extra: TypeDeclInfo[] = [];
          const info = extractTypeDecl(decls[0], extra);
          if (info) { typeDecls.push(...extra); typeDecls.push(info); knownTypes.add(aliasName); }
        } else if (t.getProperties().length > 0) {
          // Alias declaration not available (e.g. intersection type) — extract from properties
          const extra: TypeDeclInfo[] = [];
          const info = extractRecord(aliasName, t, locationNode, undefined, extra);
          if (info) { typeDecls.push(...extra); typeDecls.push(info); knownTypes.add(aliasName); }
        }
      }
    }
    if (t.isUnion()) { for (const u of t.getUnionTypes()) resolveType(u, locationNode); return; }
    for (const arg of t.getTypeArguments()) resolveType(arg, locationNode);
    const sym = t.getSymbol() ?? t.getAliasSymbol();
    const name = sym?.getName();
    if (name && !name.startsWith("__") && !knownTypes.has(name) && !builtins.has(name) && (t.isObject() || t.isIntersection())) {
      const extra: TypeDeclInfo[] = [];
      const info = extractRecord(name, t, locationNode, undefined, extra);
      if (info) {
        typeDecls.push(...extra); typeDecls.push(info); knownTypes.add(name);
        // Recursively resolve types referenced in this type's fields
        for (const prop of t.getProperties()) {
          resolveType(prop.getTypeAtLocation(locationNode), locationNode);
        }
      }
    }
  }
  for (const f of fnsToExtract) {
    for (const p of f.node.getParameters()) resolveType(p.getType(), p);
  }
  // Resolve anonymous object return types into synthetic named types
  for (let i = 0; i < fnsToExtract.length; i++) {
    const f = fnsToExtract[i];
    const fn = functions[i];
    const retType = f.node.getReturnType();
    // Prefer alias symbol (named type aliases) over underlying object symbol (__type)
    const aliasSym = retType.getAliasSymbol();
    if (aliasSym && !aliasSym.getName().startsWith("__")) {
      // Named type alias — resolve it instead of generating a synthetic name
      resolveType(retType, f.node);
      const aliasName = aliasSym.getName();
      if (knownTypes.has(aliasName)) fn.returnType = aliasName;
      continue;
    }
    const sym = retType.getSymbol();
    if (sym?.getName() === "__type" && retType.isObject() && !retType.isArray()) {
      const synName = fn.name.charAt(0).toUpperCase() + fn.name.slice(1) + "Result";
      if (!knownTypes.has(synName)) {
        const extra: TypeDeclInfo[] = [];
        const info = extractRecord(synName, retType, f.node, undefined, extra);
        if (info) { typeDecls.push(...extra); typeDecls.push(info); knownTypes.add(synName); }
      }
      fn.returnType = synName;
      // Also resolve imported types referenced in the return type's fields
      for (const prop of retType.getProperties()) {
        resolveType(prop.getTypeAtLocation(f.node), f.node);
      }
    }
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
    constants,
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
