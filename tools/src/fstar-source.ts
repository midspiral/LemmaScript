/** Source constructs whose semantics have already been erased by extraction. */
import { Node, SyntaxKind, type SourceFile } from "ts-morph";
import type { RawModule } from "./rawir.js";

export function checkFstarSource(source: SourceFile, raw: RawModule): void {
  for (const stmt of source.getStatements()) {
    if (!(Node.isFunctionDeclaration(stmt) || Node.isVariableStatement(stmt)
      || Node.isTypeAliasDeclaration(stmt) || Node.isInterfaceDeclaration(stmt)
      || Node.isImportDeclaration(stmt) || Node.isExportDeclaration(stmt)
      || Node.isEmptyStatement(stmt) || Node.isClassDeclaration(stmt) || Node.isEnumDeclaration(stmt)
      || stmt.getLeadingCommentRanges().some(c => /^\/\/@\s+skip\b/.test(c.getText().trim()))
      || (Node.isExpressionStatement(stmt) && /\/\/@\s+verify\b/.test(stmt.getFullText())))) {
      throw new Error("F*: unsupported module-level statement; only functions, constants, types, and imports/exports are supported");
    }
  }
  const selected = new Set(raw.functions.map(f => f.name));
  const roots: Node[] = source.getFunctions().filter(f => selected.has(f.getName() ?? ""));
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
    function check(n: Node): void {
      if (Node.isBinaryExpression(n) && ["===", "!==", "==", "!="].includes(n.getOperatorToken().getText())) {
        const types = [n.getLeft().getType(), n.getRight().getType()];
        if (types.every(t => t.isArray() || t.getCallSignatures().length > 0)) {
          throw new Error("F*: reference equality is not modeled; compare values explicitly");
        }
      }
      let target: Node | undefined;
      if (Node.isBinaryExpression(n) && ["=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", ">>>=", "&&=", "||=", "??="].includes(n.getOperatorToken().getText())) target = n.getLeft();
      if ((Node.isPrefixUnaryExpression(n) || Node.isPostfixUnaryExpression(n)) && [SyntaxKind.PlusPlusToken, SyntaxKind.MinusMinusToken].includes(n.getOperatorToken())) target = n.getOperand();
      if (Node.isCallExpression(n)) {
        const callee = n.getExpression();
        if (Node.isPropertyAccessExpression(callee) && ["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "set", "add", "delete", "clear"].includes(callee.getName())) target = callee.getExpression();
      }
      if (target) {
        while (Node.isPropertyAccessExpression(target) || Node.isElementAccessExpression(target)) target = target.getExpression();
        const closure = n.getFirstAncestor(a => Node.isArrowFunction(a) || Node.isFunctionExpression(a) || Node.isFunctionDeclaration(a) || Node.isMethodDeclaration(a));
        const declaration = target.getSymbol()?.getDeclarations()[0];
        if (closure && declaration && !(target.getKind() === SyntaxKind.ThisKeyword && Node.isMethodDeclaration(closure)) && !declaration.getAncestors().includes(closure)) {
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
      if (Node.isTypeParameterDeclaration(n) && (n.getConstraint() || n.getDefault())) {
        throw new Error("F*: constrained/defaulted type parameters are not supported");
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
