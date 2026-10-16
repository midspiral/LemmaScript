/** Source constructs whose semantics have already been erased by extraction. */
import { Node, SyntaxKind, type SourceFile, type Type } from "ts-morph";
import type { RawModule } from "./rawir.js";
import { sourceFunctions } from "./source-functions.js";

function isFunctionScope(n: Node): boolean {
  return Node.isArrowFunction(n) || Node.isFunctionExpression(n)
    || Node.isFunctionDeclaration(n) || Node.isMethodDeclaration(n);
}

function mayHaveReferenceIdentity(t: Type): boolean {
  if (t.isUnion()) return t.getUnionTypes().some(mayHaveReferenceIdentity);
  if (t.isIntersection()) return t.getIntersectionTypes().every(mayHaveReferenceIdentity);
  if (t.isTypeParameter()) {
    const constraint = t.getConstraint();
    return !constraint || mayHaveReferenceIdentity(constraint);
  }
  return t.isObject() || t.isAny() || t.isUnknown();
}

function unwrapExpression(target: Node): Node {
  if (Node.isParenthesizedExpression(target) || Node.isAsExpression(target)
    || Node.isTypeAssertion(target) || Node.isNonNullExpression(target)) {
    return unwrapExpression(target.getExpression());
  }
  return target;
}

function mutationRoot(target: Node): Node {
  target = unwrapExpression(target);
  if (Node.isPropertyAccessExpression(target) || Node.isElementAccessExpression(target)) {
    return mutationRoot(target.getExpression());
  }
  return target;
}

/** Bindings read across a function boundary must stay immutable. F* closures
 * capture values, whereas JS closures observe later writes to their bindings.
 * Deliberately conservative: this does not infer callback lifetimes or aliases.
 */
function capturedBindings(root: Node): Set<Node> {
  const captured = new Set<Node>();
  root.forEachDescendant(n => {
    const closure = n.getFirstAncestor(isFunctionScope);
    if (!closure) return;
    if (Node.isIdentifier(n)) {
      const parent = n.getParent();
      const symbol = parent && Node.isShorthandPropertyAssignment(parent) ? parent.getValueSymbol() : n.getSymbol();
      const declaration = symbol?.getDeclarations()[0];
      if (declaration && (Node.isVariableDeclaration(declaration) || Node.isParameterDeclaration(declaration)
        || Node.isBindingElement(declaration)) && !declaration.getAncestors().includes(closure)) {
        captured.add(declaration);
      }
    }
    if (n.getKind() === SyntaxKind.ThisKeyword && Node.isArrowFunction(closure)) {
      const owner = n.getFirstAncestor(a => isFunctionScope(a) && !Node.isArrowFunction(a));
      if (owner) captured.add(owner);
    }
  });
  return captured;
}

export function checkFstarSource(source: SourceFile, raw: RawModule): void {
  const functions = sourceFunctions(source);
  for (const stmt of source.getStatements()) {
    if (!(Node.isFunctionDeclaration(stmt) || Node.isVariableStatement(stmt)
      || Node.isTypeAliasDeclaration(stmt) || Node.isInterfaceDeclaration(stmt)
      || Node.isImportDeclaration(stmt) || Node.isExportDeclaration(stmt)
      || Node.isEmptyStatement(stmt) || Node.isClassDeclaration(stmt) || Node.isEnumDeclaration(stmt)
      || Node.isModuleDeclaration(stmt)
      || stmt.getLeadingCommentRanges().some(c => /^\/\/@\s+skip\b/.test(c.getText().trim()))
      || (Node.isExpressionStatement(stmt) && /\/\/@\s+verify\b/.test(stmt.getFullText())))) {
      throw new Error("F*: unsupported module-level statement; only functions, constants, types, and imports/exports are supported");
    }
  }
  const selected = new Set(raw.functions.map(f => f.name));
  const roots: Node[] = functions.filter(f => selected.has(f.getName() ?? ""));
  if (raw.functions.some(f => f.contract.length)) throw new Error("F*: contract annotations are not supported; use requires/ensures");
  for (const v of source.getVariableDeclarations()) {
    const init = v.getInitializer();
    if (v.getType().isArray()) throw new Error("F*: only scalar module constants are supported; module array state is not modeled");
    if (init && Node.isArrowFunction(init) && selected.has(v.getName())) roots.push(init);
  }
  // Class methods and explicitly selected inline handlers need the same checks.
  for (const cls of source.getClasses()) roots.push(...cls.getMethods());
  for (const arrow of source.getDescendantsOfKind(SyntaxKind.ArrowFunction)) {
    if (!roots.some(r => r === arrow || r.getDescendants().includes(arrow)) && /\/\/@\s+verify\b/.test(arrow.getFullText())) roots.push(arrow);
  }
  for (const root of [...roots, ...source.getTypeAliases()]) {
    const captured = capturedBindings(root);
    function check(n: Node): void {
      if (Node.isBinaryExpression(n) && ["===", "!==", "==", "!="].includes(n.getOperatorToken().getText())) {
        const types = [n.getLeft().getType(), n.getRight().getType()];
        if (types.every(mayHaveReferenceIdentity)) {
          throw new Error("F*: reference equality is not modeled; compare values explicitly");
        }
      }
      let target: Node | undefined;
      if (Node.isBinaryExpression(n) && ["=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", ">>>=", "&&=", "||=", "??="].includes(n.getOperatorToken().getText())) target = n.getLeft();
      if ((Node.isPrefixUnaryExpression(n) || Node.isPostfixUnaryExpression(n)) && [SyntaxKind.PlusPlusToken, SyntaxKind.MinusMinusToken].includes(n.getOperatorToken())) target = n.getOperand();
      if (Node.isCallExpression(n)) {
        const callee = unwrapExpression(n.getExpression());
        if (Node.isPropertyAccessExpression(callee) && ["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "set", "add", "delete", "clear"].includes(callee.getName())) target = callee.getExpression();
      }
      if (target) {
        target = mutationRoot(target);
        const closure = n.getFirstAncestor(isFunctionScope);
        const declaration = target.getKind() === SyntaxKind.ThisKeyword
          ? target.getFirstAncestor(a => isFunctionScope(a) && !Node.isArrowFunction(a))
          : target.getSymbol()?.getDeclarations()[0];
        if (closure && declaration && (captured.has(declaration)
          || (declaration !== closure && !declaration.getAncestors().includes(closure)))) {
          throw new Error(`F*: mutation of captured variable '${target.getText()}' is not modeled`);
        }
      }
      if (Node.isParameterDeclaration(n) && (n.isRestParameter() || n.getInitializer())) {
        throw new Error(`F*: defaulted and rest parameters are not supported (${n.getText()})`);
      }
      if (Node.isParameterDeclaration(n) && !Node.isIdentifier(n.getNameNode()) && !Node.isArrowFunction(n.getParent())) {
        throw new Error("F*: destructured parameters on named functions are not supported by extraction");
      }
      if ((Node.isFunctionDeclaration(n) || Node.isArrowFunction(n)) && n.isAsync() && n.getDescendants().some(x=>Node.isAwaitExpression(x))) {
        throw new Error("F*: async functions are not supported by the pure backend");
      }
      if (Node.isArrowFunction(n) && n !== root && /\/\/@\s+(?:requires|ensures|contract|decreases)\b/.test(n.getFullText())) {
        throw new Error("F*: nested lambda contracts are not supported; specify the enclosing function or a named helper");
      }
      if (Node.isTypeParameterDeclaration(n)) {
        const constraint = n.getConstraint();
        // Primitive constraints restrict TS callers. The generated generic
        // signature still proves the body for every admitted F* type.
        if (n.getDefault() || (constraint && mayHaveReferenceIdentity(constraint.getType()))) {
          throw new Error("F*: non-primitive constrained/defaulted type parameters are not supported");
        }
      }
      if (Node.isFunctionDeclaration(n) && n.isGenerator()) throw new Error("F*: generators are not supported");
      if (n.getLeadingCommentRanges().some(c => /^\/\/@\s+skip\b/.test(c.getText().trim()))) {
        throw new Error("F*: statement-level skip is not supported inside verified functions");
      }
    }
    check(root);
    root.forEachDescendant(check);
  }
}
