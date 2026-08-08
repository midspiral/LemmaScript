/**
 * Spec expression parser backed by TypeScript's expression parser.
 *
 * LemmaScript's four non-TypeScript forms are masked with same-width valid TS
 * before parsing.  The converter restores their RawExpr nodes from the original
 * source; every ordinary expression construct gets its grouping from TS.
 */

import { ts } from "ts-morph";
import type { RawExpr } from "./rawir.js";
import { normalizeBigIntLiteral } from "./rawir.js";

interface ScanToken {
  kind: ts.SyntaxKind;
  text: string;
  pos: number;
}

function scan(source: string): ScanToken[] {
  const scanner = ts.createScanner(
    ts.ScriptTarget.Latest,
    true,
    ts.LanguageVariant.Standard,
    source,
  );
  const tokens: ScanToken[] = [];
  for (let kind = scanner.scan(); kind !== ts.SyntaxKind.EndOfFileToken; kind = scanner.scan()) {
    tokens.push({ kind, text: scanner.getTokenText(), pos: scanner.getTokenPos() });
  }
  return tokens;
}

function overwrite(chars: string[], pos: number, replacement: string): void {
  for (let i = 0; i < replacement.length; i++) chars[pos + i] = replacement[i];
}

/** Make the extensions syntactically valid without moving any source offsets.
 *
 *   \result                 -> $result
 *   forall(k: nat, p)      -> forall(k, nat, p)
 *   p ==> q                -> p >>  q
 *   p <==> q               -> p >>>  q
 *
 * Shifts are only parse markers: the original source is consulted before any
 * TS AST node is converted, and a marker reaching the converter is an internal
 * error.  The current spec grammar has no shift operators, so there is no
 * collision with accepted input.
 */
function maskExtensions(source: string): string {
  // TypeScript offsets count UTF-16 code units; split the same way so an emoji
  // before an extension does not shift every replacement that follows it.
  const chars = source.split("");
  const tokens = scan(source);

  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    if (source.startsWith("<==>", token.pos)) overwrite(chars, token.pos, ">>> ");
    else if (source.startsWith("==>", token.pos)) overwrite(chars, token.pos, ">> ");
    else if (source.startsWith("\\result", token.pos)) overwrite(chars, token.pos, "$result");

    // The existing grammar permits exactly one identifier for both binder and
    // type. Mask those tokens into a valid three-argument TypeScript call.
    const binder = tokens[i + 2];
    const varType = tokens[i + 4];
    if ((token.text === "forall" || token.text === "exists") &&
        tokens[i + 1]?.kind === ts.SyntaxKind.OpenParenToken &&
        binder && /^[a-zA-Z_][a-zA-Z_0-9]*$/.test(binder.text) &&
        tokens[i + 3]?.kind === ts.SyntaxKind.ColonToken &&
        varType && /^[a-zA-Z_][a-zA-Z_0-9]*$/.test(varType.text) &&
        tokens[i + 5]?.kind === ts.SyntaxKind.CommaToken) {
      overwrite(chars, tokens[i + 3].pos, ",");
      // Primitive type names such as `string` and `boolean` are TS keywords,
      // not expressions. Give the temporary binder and type same-width safe
      // identifiers; the converter recovers their original source text.
      overwrite(chars, binder.pos, "_".repeat(binder.text.length));
      overwrite(chars, varType.pos, "_".repeat(varType.text.length));
    }
  }
  return chars.join("");
}

interface ExtensionSplit {
  op: "==>" | "<==>";
  pos: number;
}

/** Find an extension operator at the current expression level. Parenthesized,
 * indexed, call-argument, array, and object expressions are left to TS and
 * revisited when their child AST nodes are converted. A top-level ternary owns
 * everything after its `?` as a branch, matching the existing spec grammar. */
function findExtensionSplit(source: string): ExtensionSplit | null {
  let parens = 0;
  let brackets = 0;
  let braces = 0;
  let firstImplies: number | null = null;
  let firstIff: number | null = null;

  for (const token of scan(source)) {
    const atTop = parens === 0 && brackets === 0 && braces === 0;
    if (atTop && token.kind === ts.SyntaxKind.QuestionToken) break;
    if (atTop && firstIff === null && source.startsWith("<==>", token.pos)) firstIff = token.pos;
    else if (atTop && firstImplies === null && source.startsWith("==>", token.pos)) firstImplies = token.pos;

    if (token.kind === ts.SyntaxKind.OpenParenToken) parens++;
    else if (token.kind === ts.SyntaxKind.CloseParenToken) parens--;
    else if (token.kind === ts.SyntaxKind.OpenBracketToken) brackets++;
    else if (token.kind === ts.SyntaxKind.CloseBracketToken) brackets--;
    else if (token.kind === ts.SyntaxKind.OpenBraceToken) braces++;
    else if (token.kind === ts.SyntaxKind.CloseBraceToken) braces--;
  }

  // Iff binds more loosely than implication. Both split at their first token,
  // producing the existing parser's right-associative tree.
  if (firstIff !== null) return { op: "<==>", pos: firstIff };
  if (firstImplies !== null) return { op: "==>", pos: firstImplies };
  return null;
}

const PREFIX = "const __spec = (";
const ALLOWED_BINARY_OPS = new Set([
  "+", "-", "*", "/", "%", ">", "<", ">=", "<=",
  "===", "!==", "==", "!=", "&&", "||", "in",
]);

interface ConvertCtx {
  source: string;
  sourceFile: ts.SourceFile;
}

function nodeSource(node: ts.Node, ctx: ConvertCtx): string {
  const start = node.getStart(ctx.sourceFile) - PREFIX.length;
  const end = node.getEnd() - PREFIX.length;
  return ctx.source.slice(start, end);
}

function convertChild(node: ts.Expression, ctx: ConvertCtx): RawExpr {
  return parseExprInner(nodeSource(node, ctx));
}

function convertExpr(node: ts.Expression, ctx: ConvertCtx): RawExpr {
  if (ts.isNumericLiteral(node)) return { kind: "num", value: Number(node.text.replace(/_/g, "")) };
  if (ts.isBigIntLiteral(node)) return { kind: "bigint", value: normalizeBigIntLiteral(node.getText(ctx.sourceFile)) };
  if (ts.isStringLiteral(node)) return { kind: "str", value: node.text };
  if (node.kind === ts.SyntaxKind.TrueKeyword) return { kind: "bool", value: true };
  if (node.kind === ts.SyntaxKind.FalseKeyword) return { kind: "bool", value: false };
  if (node.kind === ts.SyntaxKind.NullKeyword) return { kind: "var", name: "undefined" };
  if (node.kind === ts.SyntaxKind.ThisKeyword) return { kind: "var", name: "this" };

  if (ts.isIdentifier(node)) {
    if (node.text === "$result") return { kind: "result" };
    return { kind: "var", name: node.text };
  }

  if (ts.isParenthesizedExpression(node)) return convertChild(node.expression, ctx);

  if (ts.isPropertyAccessExpression(node) && !node.questionDotToken) {
    return { kind: "field", obj: convertChild(node.expression, ctx), field: node.name.text };
  }

  if (ts.isElementAccessExpression(node) && !node.questionDotToken) {
    if (!node.argumentExpression) throw new Error(`Missing index in spec expression: ${ctx.source}`);
    return {
      kind: "index",
      obj: convertChild(node.expression, ctx),
      idx: convertChild(node.argumentExpression, ctx),
    };
  }

  if (ts.isCallExpression(node) && !node.questionDotToken) {
    if (ts.isIdentifier(node.expression) && (node.expression.text === "forall" || node.expression.text === "exists")) {
      const kind = node.expression.text;
      const typed = node.arguments.length === 3;
      if ((!typed && node.arguments.length !== 2) || !ts.isIdentifier(node.arguments[0])) {
        throw new Error(`Expected ${kind}(variable[: type], expression)`);
      }
      const varTypeNode = typed ? node.arguments[1] : null;
      if (varTypeNode && !ts.isIdentifier(varTypeNode)) {
        throw new Error(`Expected identifier type in ${kind}: ${nodeSource(varTypeNode, ctx)}`);
      }
      return {
        kind,
        var: nodeSource(node.arguments[0], ctx),
        varType: varTypeNode ? nodeSource(varTypeNode, ctx) : "int",
        body: convertChild(node.arguments[typed ? 2 : 1], ctx),
      };
    }
    return {
      kind: "call",
      fn: convertChild(node.expression, ctx),
      args: node.arguments.map(arg => convertChild(arg, ctx)),
    };
  }

  if (ts.isBinaryExpression(node)) {
    const rawOp = node.operatorToken.getText(ctx.sourceFile);
    if (rawOp === ">>" || rawOp === ">>>") {
      throw new Error(`Internal error: unconsumed spec extension in ${ctx.source}`);
    }
    if (!ALLOWED_BINARY_OPS.has(rawOp)) throw new Error(`Unsupported spec operator: ${rawOp}`);
    const op = rawOp === "==" ? "===" : rawOp === "!=" ? "!==" : rawOp;
    return { kind: "binop", op, left: convertChild(node.left, ctx), right: convertChild(node.right, ctx) };
  }

  if (ts.isPrefixUnaryExpression(node)) {
    const op = node.operator === ts.SyntaxKind.ExclamationToken ? "!"
      : node.operator === ts.SyntaxKind.MinusToken ? "-" : null;
    if (!op) throw new Error(`Unsupported spec unary operator: ${node.operator}`);
    return { kind: "unop", op, expr: convertChild(node.operand, ctx) };
  }

  if (ts.isConditionalExpression(node)) {
    return {
      kind: "conditional",
      cond: convertChild(node.condition, ctx),
      then: convertChild(node.whenTrue, ctx),
      else: convertChild(node.whenFalse, ctx),
    };
  }

  if (ts.isArrayLiteralExpression(node)) {
    const elems = node.elements.map(elem => {
      if (ts.isOmittedExpression(elem) || ts.isSpreadElement(elem)) {
        throw new Error(`Unsupported element in spec array: ${nodeSource(elem, ctx)}`);
      }
      return convertChild(elem, ctx);
    });
    return { kind: "arrayLiteral", elems };
  }

  if (ts.isObjectLiteralExpression(node)) {
    const fields = node.properties.map(prop => {
      if (!ts.isPropertyAssignment(prop) || !ts.isIdentifier(prop.name)) {
        throw new Error(`Unsupported property in spec object: ${nodeSource(prop, ctx)}`);
      }
      return { name: prop.name.text, value: convertChild(prop.initializer, ctx) };
    });
    return { kind: "record", spread: null, fields };
  }

  if (ts.isNewExpression(node) && ts.isIdentifier(node.expression) &&
      (node.expression.text === "Set" || node.expression.text === "Map")) {
    if ((node.arguments?.length ?? 0) !== 0) {
      throw new Error(`Spec collection constructor must be empty: ${nodeSource(node, ctx)}`);
    }
    const name = node.expression.text;
    const typeArgs = node.typeArguments?.map(arg => arg.getText(ctx.sourceFile).replace(/\s+/g, "")) ?? [];
    const tsType = typeArgs.length === 0 ? name : `${name}<${typeArgs.join(",")}>`;
    return { kind: "emptyCollection", collectionType: name, tsType };
  }

  throw new Error(`Unsupported spec expression: ${nodeSource(node, ctx)}`);
}

function parseOrdinary(source: string): RawExpr {
  const masked = maskExtensions(source);
  const sourceFile = ts.createSourceFile(
    "spec-expression.ts",
    `${PREFIX}${masked});`,
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.TS,
  );
  const diagnostics = (sourceFile as ts.SourceFile & { parseDiagnostics?: readonly ts.Diagnostic[] }).parseDiagnostics ?? [];
  if (diagnostics.length > 0) {
    throw new Error(`Invalid spec expression: ${ts.flattenDiagnosticMessageText(diagnostics[0].messageText, "\n")}`);
  }
  const statement = sourceFile.statements[0];
  if (!statement || !ts.isVariableStatement(statement)) throw new Error(`Invalid spec expression: ${source}`);
  const initializer = statement.declarationList.declarations[0]?.initializer;
  if (!initializer || !ts.isParenthesizedExpression(initializer)) throw new Error(`Invalid spec expression: ${source}`);
  return convertExpr(initializer.expression, { source, sourceFile });
}

function parseExprInner(input: string): RawExpr {
  const source = input.trim();
  const split = findExtensionSplit(source);
  if (split) {
    return {
      kind: "binop",
      op: split.op,
      left: parseExprInner(source.slice(0, split.pos)),
      right: parseExprInner(source.slice(split.pos + split.op.length)),
    };
  }
  return parseOrdinary(source);
}

export function parseExpr(input: string): RawExpr {
  try {
    return parseExprInner(input);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`${message}\n  in spec: ${input.trim()}`);
  }
}
