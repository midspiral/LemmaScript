/**
 * Parse a supported TypeScript expression from a `//@` annotation and convert
 * it to Raw IR. Quantifiers and logical connectives are ordinary, valid-TS
 * calls whose argument shapes are recognized here.
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

function fail(input: string, message: string): never {
  throw new Error(`Invalid spec expression: ${message}\n  in spec: ${input}`);
}

function textOf(node: ts.Node, sourceFile: ts.SourceFile): string {
  return node.getText(sourceFile);
}

function convertQuantifier(
  call: ts.CallExpression,
  kind: "forall" | "exists",
  sourceFile: ts.SourceFile,
  input: string,
): RawExpr {
  if (call.typeArguments?.length || call.arguments.length !== 1) {
    return fail(input, `${kind} expects one arrow function`);
  }

  const arrow = call.arguments[0];
  if (!ts.isArrowFunction(arrow) || arrow.modifiers?.length || arrow.parameters.length !== 1) {
    return fail(input, `${kind} expects one arrow parameter, for example ${kind}(k => predicate)`);
  }

  const parameter = arrow.parameters[0];
  if (!ts.isIdentifier(parameter.name) || parameter.dotDotDotToken || parameter.questionToken || parameter.initializer) {
    return fail(input, `${kind}'s parameter must be a single identifier`);
  }
  if (ts.isBlock(arrow.body)) {
    return fail(input, `${kind}'s arrow body must be an expression`);
  }

  return {
    kind,
    var: parameter.name.text,
    varType: parameter.type ? textOf(parameter.type, sourceFile) : "int",
    body: convertExpr(arrow.body, sourceFile, input),
  };
}

function convertCall(call: ts.CallExpression, sourceFile: ts.SourceFile, input: string): RawExpr {
  if (call.questionDotToken) return fail(input, "optional calls are not supported in specs");
  if (call.arguments.some(ts.isSpreadElement)) return fail(input, "spread arguments are not supported in specs");

  if (ts.isIdentifier(call.expression)) {
    const name = call.expression.text;
    if (name === "forall" || name === "exists") {
      return convertQuantifier(call, name, sourceFile, input);
    }
    if (name === "implies" || name === "iff") {
      if (call.typeArguments?.length || call.arguments.length !== 2) {
        return fail(input, `${name} expects exactly two arguments`);
      }
      return {
        kind: "binop",
        op: name === "implies" ? "==>" : "<==>",
        left: convertExpr(call.arguments[0], sourceFile, input),
        right: convertExpr(call.arguments[1], sourceFile, input),
      };
    }
  }

  if (call.typeArguments?.length) return fail(input, "generic calls are not supported in specs");
  return {
    kind: "call",
    fn: convertExpr(call.expression, sourceFile, input),
    args: call.arguments.map(argument => convertExpr(argument, sourceFile, input)),
  };
}

function convertExpr(node: ts.Expression, sourceFile: ts.SourceFile, input: string): RawExpr {
  if (ts.isParenthesizedExpression(node)) return convertExpr(node.expression, sourceFile, input);

  if (ts.isNumericLiteral(node)) return { kind: "num", value: Number(node.text.replace(/_/g, "")) };
  if (ts.isBigIntLiteral(node)) return { kind: "bigint", value: normalizeBigIntLiteral(node.getText(sourceFile)) };
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
    if (node.questionDotToken) return fail(input, "optional property access is not supported in specs");
    return { kind: "field", obj: convertExpr(node.expression, sourceFile, input), field: node.name.text };
  }

  if (ts.isElementAccessExpression(node)) {
    if (node.questionDotToken) return fail(input, "optional element access is not supported in specs");
    if (!node.argumentExpression) return fail(input, "element access requires an index");
    return {
      kind: "index",
      obj: convertExpr(node.expression, sourceFile, input),
      idx: convertExpr(node.argumentExpression, sourceFile, input),
    };
  }

  if (ts.isCallExpression(node)) return convertCall(node, sourceFile, input);

  if (ts.isBinaryExpression(node)) {
    const op = node.operatorToken.getText(sourceFile);
    if (!BINARY_OPERATORS.has(op)) return fail(input, `operator '${op}' is not supported in specs`);
    return {
      kind: "binop",
      op: op === "==" ? "===" : op === "!=" ? "!==" : op,
      left: convertExpr(node.left, sourceFile, input),
      right: convertExpr(node.right, sourceFile, input),
    };
  }

  if (ts.isPrefixUnaryExpression(node)) {
    const op = node.operator === ts.SyntaxKind.ExclamationToken ? "!"
      : node.operator === ts.SyntaxKind.MinusToken ? "-"
      : null;
    if (!op) return fail(input, `unary operator in '${textOf(node, sourceFile)}' is not supported in specs`);
    return { kind: "unop", op, expr: convertExpr(node.operand, sourceFile, input) };
  }

  if (ts.isConditionalExpression(node)) {
    return {
      kind: "conditional",
      cond: convertExpr(node.condition, sourceFile, input),
      then: convertExpr(node.whenTrue, sourceFile, input),
      else: convertExpr(node.whenFalse, sourceFile, input),
    };
  }

  if (ts.isArrayLiteralExpression(node)) {
    if (node.elements.some(element => ts.isOmittedExpression(element) || ts.isSpreadElement(element))) {
      return fail(input, "array holes and spreads are not supported in specs");
    }
    return { kind: "arrayLiteral", elems: node.elements.map(element => convertExpr(element, sourceFile, input)) };
  }

  if (ts.isObjectLiteralExpression(node)) {
    const fields = node.properties.map(property => {
      if (!ts.isPropertyAssignment(property) || !ts.isIdentifier(property.name)) {
        return fail(input, "spec object literals require identifier property assignments");
      }
      return { name: property.name.text, value: convertExpr(property.initializer, sourceFile, input) };
    });
    return { kind: "record", spread: null, fields };
  }

  if (ts.isNewExpression(node)) {
    if (!ts.isIdentifier(node.expression) || (node.expression.text !== "Set" && node.expression.text !== "Map")) {
      return fail(input, `unsupported constructor '${textOf(node.expression, sourceFile)}'`);
    }
    if ((node.arguments?.length ?? 0) !== 0) return fail(input, `new ${node.expression.text} expects no arguments in specs`);
    const name = node.expression.text;
    const typeArgs = node.typeArguments?.map(type => textOf(type, sourceFile)) ?? [];
    return {
      kind: "emptyCollection",
      collectionType: name,
      tsType: typeArgs.length ? `${name}<${typeArgs.join(", ")}>` : name,
    };
  }

  if (ts.isArrowFunction(node)) return fail(input, "arrow functions are only supported as forall/exists arguments");
  return fail(input, `unsupported syntax '${textOf(node, sourceFile)}'`);
}

export function parseExpr(input: string): Expr {
  const prefix = "const __spec = (";
  const sourceFile = ts.createSourceFile(
    "spec.ts",
    `${prefix}${input});`,
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
  return convertExpr(initializer.expression, sourceFile, input);
}
