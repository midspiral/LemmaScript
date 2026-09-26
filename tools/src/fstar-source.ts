/** Source constructs whose semantics have already been erased by extraction. */
import { Node, type SourceFile } from "ts-morph";
import type { RawModule } from "./rawir.js";

export function checkFstarSource(source: SourceFile, raw: RawModule): void {
  for (const stmt of source.getStatements()) {
    if (!(Node.isFunctionDeclaration(stmt) || Node.isVariableStatement(stmt)
      || Node.isTypeAliasDeclaration(stmt) || Node.isInterfaceDeclaration(stmt)
      || Node.isImportDeclaration(stmt) || Node.isExportDeclaration(stmt)
      || Node.isEmptyStatement(stmt))) {
      throw new Error("F*: unsupported module-level statement; only functions, constants, types, and imports/exports are supported");
    }
  }
  const selected = new Set(raw.functions.map(f => f.name));
  const roots: Node[] = source.getFunctions().filter(f => selected.has(f.getName() ?? ""));
  if (raw.functions.some(f => f.contract.length)) throw new Error("F*: contract annotations are not supported; use requires/ensures");
  for (const v of source.getVariableDeclarations()) {
    const init = v.getInitializer();
    if (init && Node.isArrowFunction(init) && selected.has(v.getName())) roots.push(init);
  }
  for (const root of [...roots, ...source.getTypeAliases()]) {
    function check(n: Node): void {
      if (Node.isParameterDeclaration(n) && (n.isRestParameter() || n.hasQuestionToken() || n.getInitializer())) {
        throw new Error(`F*: optional, defaulted, and rest parameters are not supported (${n.getText()})`);
      }
      if (Node.isParameterDeclaration(n) && !Node.isIdentifier(n.getNameNode())) {
        throw new Error("F*: destructured parameters are not supported");
      }
      if (Node.isVariableStatement(n) && n.getDeclarationKind() !== "const") {
        throw new Error("F*: mutable local declarations are not supported; use const");
      }
      // Extraction flattens standalone blocks, losing their lexical scope.
      if (Node.isBlock(n) && Node.isBlock(n.getParentOrThrow())) {
        throw new Error("F*: standalone lexical blocks are not supported");
      }
      if ((Node.isFunctionDeclaration(n) || Node.isArrowFunction(n)) && n.isAsync()) {
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
