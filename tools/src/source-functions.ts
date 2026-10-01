import { Node, type FunctionDeclaration, type SourceFile } from "ts-morph";

/** Type-only namespaces have no runtime initialization to model. Ambient
 * value/function declarations are deliberately not included in this case. */
function typeOnlyNamespace(node: Node): boolean {
  if (Node.isModuleDeclaration(node)) {
    const body = node.getBody();
    return !!body && typeOnlyNamespace(body);
  }
  return Node.isModuleBlock(node) && node.getStatements().every(stmt =>
    Node.isTypeAliasDeclaration(stmt) || Node.isInterfaceDeclaration(stmt)
    || Node.isEmptyStatement(stmt) || (Node.isModuleDeclaration(stmt) && typeOnlyNamespace(stmt)));
}

/** Function-only namespaces are flattened to unambiguous declaration names.
 * Keep the original nodes: symbol resolution and source safety checks must see
 * the original scopes. Namespace state and colliding names need a richer IR.
 */
export function sourceFunctions(source: SourceFile): FunctionDeclaration[] {
  const functions = [...source.getFunctions()];
  const namespaces = source.getModules();
  if (!namespaces.length) return functions;
  const names = new Set([
    ...functions.map(f => f.getName()),
    ...source.getVariableDeclarations().map(d => d.getName()),
    ...source.getClasses().map(d => d.getName()),
    ...source.getEnums().map(d => d.getName()),
    ...source.getTypeAliases().map(d => d.getName()),
    ...source.getInterfaces().map(d => d.getName()),
    ...source.getImportDeclarations().flatMap(d => [
      d.getDefaultImport()?.getText(), d.getNamespaceImport()?.getText(),
      ...d.getNamedImports().map(i => i.getAliasNode()?.getText() ?? i.getName()),
    ]),
  ]);
  function visit(node: Node): void {
    if (Node.isModuleDeclaration(node)) {
      if (node.getLeadingCommentRanges().some(c => /^\/\/@\s+skip\b/.test(c.getText().trim()))) return;
      if (typeOnlyNamespace(node)) return;
      if (!Node.isIdentifier(node.getNameNode()) || node.hasDeclareKeyword()) {
        throw new Error("Only non-ambient function-only namespaces are supported");
      }
      const body = node.getBody();
      if (!body) throw new Error("Namespace requires a body");
      visit(body);
    } else if (Node.isModuleBlock(node)) {
      for (const fn of node.getFunctions()) {
        const name = fn.getName();
        if (!name || names.has(name)) throw new Error(`Namespace function name collision: ${name}`);
        names.add(name);
        functions.push(fn);
      }
      for (const stmt of node.getStatements()) {
        if (Node.isModuleDeclaration(stmt)) visit(stmt);
        else if (!Node.isFunctionDeclaration(stmt) && !Node.isEmptyStatement(stmt)) {
          throw new Error("Only function declarations and nested namespaces are supported inside a namespace");
        }
      }
    }
  }
  for (const namespace of namespaces) visit(namespace);
  return functions;
}

/** An object typed `typeof N` can contain replacement functions. Only a static
 * namespace path may be erased when flattening a qualified function reference.
 */
export function isNamespaceReference(node: Node): boolean {
  if (Node.isParenthesizedExpression(node)) return isNamespaceReference(node.getExpression());
  if (!Node.isIdentifier(node) && !Node.isPropertyAccessExpression(node)) return false;
  if (!node.getSymbol()?.getDeclarations().some(Node.isModuleDeclaration)) return false;
  return Node.isIdentifier(node) || isNamespaceReference(node.getExpression());
}
