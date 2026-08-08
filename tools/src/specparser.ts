/**
 * Parse a supported TypeScript-like expression from a `//@` annotation and
 * convert it to Raw IR. TypeScript parses the expression structure; the only
 * lexical extensions are the logical operators `==>` and `<==>`.
 */

import { ts } from "ts-morph";
import type { RawExpr } from "./rawir.js";
import { normalizeBigIntLiteral } from "./rawir.js";

export type Expr = RawExpr;

const BINARY_OPERATORS = new Set([
  "+", "-", "*", "/", "%",
  ">", "<", ">=", "<=",
  "===", "!==", "==", "!=",
  "&&", "||", "in",
]);

const SPINE_PRECEDENCE: Readonly<Record<string, number>> = {
  "<==>": 1,
  "==>": 2,
  "||": 4,
};
const CONDITIONAL_PRECEDENCE = 3;
const RIGHT_ASSOCIATIVE = new Set(["==>", "<==>"]);

type LogicalOperator = "==>" | "<==>";

interface ConvertContext {
  sourceFile: ts.SourceFile;
  input: string;
  sourceOffset: number;
  logicalOperators: ReadonlyMap<number, LogicalOperator>;
  usedLogicalOperators: Set<number>;
}

type SpineToken =
  | { kind: "expr"; node: ts.Expression }
  | { kind: "binary"; op: string }
  | { kind: "question" }
  | { kind: "colon" };

function fail(input: string, message: string): never {
  throw new Error(`Invalid spec expression: ${message}\n  in spec: ${input}`);
}

function textOf(node: ts.Node, ctx: ConvertContext): string {
  return node.getText(ctx.sourceFile);
}

function convertQuantifier(
  call: ts.CallExpression,
  kind: "forall" | "exists",
  ctx: ConvertContext,
): RawExpr {
  if (call.typeArguments?.length || call.arguments.length !== 1) {
    return fail(ctx.input, `${kind} expects one arrow function`);
  }

  const arrow = call.arguments[0];
  if (!ts.isArrowFunction(arrow) || arrow.modifiers?.length || arrow.parameters.length !== 1) {
    return fail(ctx.input, `${kind} expects one arrow parameter, for example ${kind}(k => predicate)`);
  }

  const parameter = arrow.parameters[0];
  if (!ts.isIdentifier(parameter.name) || parameter.dotDotDotToken || parameter.questionToken || parameter.initializer) {
    return fail(ctx.input, `${kind}'s parameter must be a single identifier`);
  }
  if (ts.isBlock(arrow.body)) {
    return fail(ctx.input, `${kind}'s arrow body must be an expression`);
  }

  return {
    kind,
    var: parameter.name.text,
    varType: parameter.type ? textOf(parameter.type, ctx) : "int",
    body: convertExpr(arrow.body, ctx),
  };
}

function convertCall(call: ts.CallExpression, ctx: ConvertContext): RawExpr {
  if (call.questionDotToken) return fail(ctx.input, "optional calls are not supported in specs");
  if (call.arguments.some(ts.isSpreadElement)) return fail(ctx.input, "spread arguments are not supported in specs");

  if (ts.isIdentifier(call.expression)) {
    const name = call.expression.text;
    if (name === "forall" || name === "exists") {
      return convertQuantifier(call, name, ctx);
    }
  }

  if (call.typeArguments?.length) return fail(ctx.input, "generic calls are not supported in specs");
  return {
    kind: "call",
    fn: convertExpr(call.expression, ctx),
    args: call.arguments.map(argument => convertExpr(argument, ctx)),
  };
}

function flattenOperatorSpine(node: ts.Expression, ctx: ConvertContext, tokens: SpineToken[]): void {
  if (ts.isParenthesizedExpression(node)) {
    tokens.push({ kind: "expr", node });
    return;
  }

  if (ts.isBinaryExpression(node)) {
    const operatorText = node.operatorToken.getText(ctx.sourceFile);
    const sourcePosition = node.operatorToken.getStart(ctx.sourceFile) - ctx.sourceOffset;
    const logical = ctx.logicalOperators.get(sourcePosition);
    if (!logical && operatorText !== "||") {
      tokens.push({ kind: "expr", node });
      return;
    }
    flattenOperatorSpine(node.left, ctx, tokens);
    if (logical) ctx.usedLogicalOperators.add(sourcePosition);
    tokens.push({ kind: "binary", op: logical ?? operatorText });
    flattenOperatorSpine(node.right, ctx, tokens);
    return;
  }

  if (ts.isConditionalExpression(node)) {
    flattenOperatorSpine(node.condition, ctx, tokens);
    tokens.push({ kind: "question" });
    flattenOperatorSpine(node.whenTrue, ctx, tokens);
    tokens.push({ kind: "colon" });
    flattenOperatorSpine(node.whenFalse, ctx, tokens);
    return;
  }

  tokens.push({ kind: "expr", node });
}

// Masking the extensions as `||` lets TypeScript parse every surrounding
// construct, but gives them `||`'s precedence. Rebuild only the affected
// low-precedence spine (`<==>`, `==>`, `?:`, and real `||`); TypeScript's AST
// remains authoritative for all tighter operators. Parentheses stay atoms and
// therefore remain hard grouping boundaries.
function convertOperatorExpression(node: ts.Expression, ctx: ConvertContext): RawExpr {
  const tokens: SpineToken[] = [];
  flattenOperatorSpine(node, ctx, tokens);
  let position = 0;

  const parse = (minimumPrecedence: number): RawExpr => {
    const first = tokens[position++];
    if (!first || first.kind !== "expr") return fail(ctx.input, "expression expected");
    let left = convertAtomicExpr(first.node, ctx);

    while (position < tokens.length) {
      const token = tokens[position];
      if (token.kind === "colon") break;

      if (token.kind === "question") {
        if (CONDITIONAL_PRECEDENCE < minimumPrecedence) break;
        position++;
        const thenExpr = parse(0);
        if (tokens[position]?.kind !== "colon") return fail(ctx.input, "':' expected in conditional expression");
        position++;
        const elseExpr = parse(0);
        left = { kind: "conditional", cond: left, then: thenExpr, else: elseExpr };
        continue;
      }

      if (token.kind !== "binary") return fail(ctx.input, "operator expected");
      const precedence = SPINE_PRECEDENCE[token.op];
      if (precedence === undefined) return fail(ctx.input, `operator '${token.op}' is not supported in specs`);
      if (precedence < minimumPrecedence) break;
      position++;
      const right = parse(RIGHT_ASSOCIATIVE.has(token.op) ? precedence : precedence + 1);
      left = { kind: "binop", op: token.op, left, right };
    }

    return left;
  };

  const result = parse(0);
  if (position !== tokens.length) return fail(ctx.input, "unexpected operator syntax");
  return result;
}

function convertAtomicExpr(node: ts.Expression, ctx: ConvertContext): RawExpr {
  if (ts.isParenthesizedExpression(node)) return convertExpr(node.expression, ctx);

  if (ts.isNumericLiteral(node)) return { kind: "num", value: Number(node.text.replace(/_/g, "")) };
  if (ts.isBigIntLiteral(node)) return { kind: "bigint", value: normalizeBigIntLiteral(node.getText(ctx.sourceFile)) };
  if (ts.isStringLiteral(node) || ts.isNoSubstitutionTemplateLiteral(node)) {
    return { kind: "str", value: node.text };
  }
  if (node.kind === ts.SyntaxKind.TrueKeyword) return { kind: "bool", value: true };
  if (node.kind === ts.SyntaxKind.FalseKeyword) return { kind: "bool", value: false };
  if (node.kind === ts.SyntaxKind.NullKeyword) return { kind: "var", name: "undefined" };
  if (node.kind === ts.SyntaxKind.ThisKeyword) return { kind: "var", name: "this" };

  if (ts.isIdentifier(node)) {
    return node.text === "$result" ? { kind: "result" } : { kind: "var", name: node.text };
  }

  if (ts.isPropertyAccessExpression(node)) {
    if (node.questionDotToken) return fail(ctx.input, "optional property access is not supported in specs");
    return { kind: "field", obj: convertExpr(node.expression, ctx), field: node.name.text };
  }

  if (ts.isElementAccessExpression(node)) {
    if (node.questionDotToken) return fail(ctx.input, "optional element access is not supported in specs");
    if (!node.argumentExpression) return fail(ctx.input, "element access requires an index");
    return {
      kind: "index",
      obj: convertExpr(node.expression, ctx),
      idx: convertExpr(node.argumentExpression, ctx),
    };
  }

  if (ts.isCallExpression(node)) return convertCall(node, ctx);

  if (ts.isBinaryExpression(node)) {
    const op = node.operatorToken.getText(ctx.sourceFile);
    if (!BINARY_OPERATORS.has(op)) return fail(ctx.input, `operator '${op}' is not supported in specs`);
    return {
      kind: "binop",
      op: op === "==" ? "===" : op === "!=" ? "!==" : op,
      left: convertExpr(node.left, ctx),
      right: convertExpr(node.right, ctx),
    };
  }

  if (ts.isPrefixUnaryExpression(node)) {
    const op = node.operator === ts.SyntaxKind.ExclamationToken ? "!"
      : node.operator === ts.SyntaxKind.MinusToken ? "-"
      : null;
    if (!op) return fail(ctx.input, `unary operator in '${textOf(node, ctx)}' is not supported in specs`);
    return { kind: "unop", op, expr: convertExpr(node.operand, ctx) };
  }

  if (ts.isArrayLiteralExpression(node)) {
    if (node.elements.some(element => ts.isOmittedExpression(element) || ts.isSpreadElement(element))) {
      return fail(ctx.input, "array holes and spreads are not supported in specs");
    }
    return { kind: "arrayLiteral", elems: node.elements.map(element => convertExpr(element, ctx)) };
  }

  if (ts.isObjectLiteralExpression(node)) {
    const fields = node.properties.map(property => {
      if (!ts.isPropertyAssignment(property) || !ts.isIdentifier(property.name)) {
        return fail(ctx.input, "spec object literals require identifier property assignments");
      }
      return { name: property.name.text, value: convertExpr(property.initializer, ctx) };
    });
    return { kind: "record", spread: null, fields };
  }

  if (ts.isNewExpression(node)) {
    if (!ts.isIdentifier(node.expression) || (node.expression.text !== "Set" && node.expression.text !== "Map")) {
      return fail(ctx.input, `unsupported constructor '${textOf(node.expression, ctx)}'`);
    }
    if ((node.arguments?.length ?? 0) !== 0) return fail(ctx.input, `new ${node.expression.text} expects no arguments in specs`);
    const name = node.expression.text;
    const typeArgs = node.typeArguments?.map(type => textOf(type, ctx)) ?? [];
    return {
      kind: "emptyCollection",
      collectionType: name,
      tsType: typeArgs.length ? `${name}<${typeArgs.join(", ")}>` : name,
    };
  }

  if (ts.isArrowFunction(node)) return fail(ctx.input, "arrow functions are only supported as forall/exists arguments");
  return fail(ctx.input, `unsupported syntax '${textOf(node, ctx)}'`);
}

function convertExpr(node: ts.Expression, ctx: ConvertContext): RawExpr {
  if (ts.isBinaryExpression(node) || ts.isConditionalExpression(node)) {
    return convertOperatorExpression(node, ctx);
  }
  return convertAtomicExpr(node, ctx);
}

function maskLogicalOperators(input: string): { text: string; operators: Map<number, LogicalOperator> } {
  const scanner = ts.createScanner(ts.ScriptTarget.Latest, false, ts.LanguageVariant.Standard, input);
  const tokens: { kind: ts.SyntaxKind; start: number; end: number }[] = [];
  while (true) {
    const kind = scanner.scan();
    if (kind === ts.SyntaxKind.EndOfFileToken) break;
    tokens.push({ kind, start: scanner.getTokenPos(), end: scanner.getTextPos() });
  }

  const operators = new Map<number, LogicalOperator>();
  // Scanner positions are UTF-16 offsets, so retain code units rather than
  // expanding astral characters into one array element.
  const characters = input.split("");
  for (let i = 0; i + 1 < tokens.length; i++) {
    const left = tokens[i];
    const right = tokens[i + 1];
    if (left.end !== right.start) continue;

    let operator: LogicalOperator | null = null;
    if (left.kind === ts.SyntaxKind.EqualsEqualsToken && right.kind === ts.SyntaxKind.GreaterThanToken) {
      operator = "==>";
    } else if (left.kind === ts.SyntaxKind.LessThanEqualsToken && right.kind === ts.SyntaxKind.EqualsGreaterThanToken) {
      operator = "<==>";
    }
    if (!operator) continue;

    operators.set(left.start, operator);
    characters[left.start] = "|";
    characters[left.start + 1] = "|";
    for (let position = left.start + 2; position < right.end; position++) characters[position] = " ";
    i++;
  }
  return { text: characters.join(""), operators };
}

export function parseExpr(input: string): Expr {
  const prefix = "const __spec = (";
  const masked = maskLogicalOperators(input);
  const sourceFile = ts.createSourceFile(
    "spec.ts",
    `${prefix}${masked.text});`,
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.TS,
  );
  const diagnostics = (sourceFile as ts.SourceFile & { parseDiagnostics: readonly ts.Diagnostic[] }).parseDiagnostics;
  if (diagnostics.length > 0) {
    return fail(input, ts.flattenDiagnosticMessageText(diagnostics[0].messageText, " "));
  }

  const statement = sourceFile.statements[0];
  if (sourceFile.statements.length !== 1 || !statement || !ts.isVariableStatement(statement)) {
    return fail(input, "expected exactly one expression");
  }
  const initializer = statement.declarationList.declarations[0]?.initializer;
  if (!initializer || !ts.isParenthesizedExpression(initializer)) return fail(input, "expression expected");
  if (initializer.end !== sourceFile.end - 1) return fail(input, "unexpected syntax after the expression");
  const ctx: ConvertContext = {
    sourceFile,
    input,
    sourceOffset: prefix.length,
    logicalOperators: masked.operators,
    usedLogicalOperators: new Set(),
  };
  const result = convertExpr(initializer.expression, ctx);
  if (ctx.usedLogicalOperators.size !== masked.operators.size) {
    return fail(input, "logical operator could not be parsed");
  }
  return result;
}
