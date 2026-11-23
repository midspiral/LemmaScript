import { Node, SyntaxKind, ts, type Identifier, type Symbol } from "ts-morph";
import { reserveName } from "./names.js";
import { renameSpecVariables } from "./specparser.js";

function functionLike(node: Node) {
  return Node.isFunctionDeclaration(node) || Node.isMethodDeclaration(node)
    || Node.isArrowFunction(node) || Node.isFunctionExpression(node);
}

function scopeOf(node: Node): Node {
  return node.getFirstAncestor(n => Node.isBlock(n) || Node.isCaseBlock(n)
    || Node.isForStatement(n) || Node.isForOfStatement(n) || Node.isForInStatement(n)
    || functionLike(n)) ?? node.getSourceFile();
}

function bindings(node: Node): Identifier[] {
  if (Node.isIdentifier(node)) return [node];
  if (Node.isObjectBindingPattern(node) || Node.isArrayBindingPattern(node)) {
    return node.getElements().flatMap(e => Node.isBindingElement(e) ? bindings(e.getNameNode()) : []);
  }
  return [];
}

function valueSymbol(node: Identifier): Symbol | undefined {
  const parent = node.getParent();
  return Node.isShorthandPropertyAssignment(parent) ? parent.getValueSymbol() : node.getSymbol();
}

/** Bare blocks and counting-for initializers lose their braces in extraction.
 *  Branch blocks keep separate arms but can absorb their parent's continuation.
 *  Loop and lambda scopes remain barriers; sibling scopes there need no rename. */
function loweredScope(decl: Node): { scope: Node; mayCapture: boolean } {
  let scope = scopeOf(decl);
  let mayCapture = Node.isForStatement(scope) || Node.isCaseBlock(scope);
  if (Node.isForStatement(scope)) scope = scopeOf(scope);
  while (Node.isBlock(scope) && Node.isBlock(scope.getParent())) {
    mayCapture = true;
    scope = scope.getParentOrThrow();
  }
  const parent = scope.getParent();
  if (parent && (Node.isIfStatement(parent) || Node.isCaseClause(parent) || Node.isDefaultClause(parent))) mayCapture = true;
  return { scope, mayCapture };
}

/** Source binding identity survives block flattening and continuation splicing.
 *  Allocate before extracting any expressions, without mutating the TS tree.
 *  Unambiguous locals and public parameter names keep their existing spelling. */
export class LexicalNames {
  private readonly renamed = new Map<ts.Symbol, string>();
  private readonly used = new Set<string>();
  private readonly sourceNames: Set<string>;
  private readonly taken: Set<string>;
  private ghosts = new Map<string, { name: string; scope: Node; pos: number }>();
  private readonly aliases = new Map<string, string[]>();

  constructor(root: Node) {
    this.sourceNames = new Set(root.getDescendantsOfKind(SyntaxKind.Identifier).map(i => i.getText()));
    // Include spec-only identifiers, including quantifier and ghost binders.
    // A fresh source name must not capture one when annotations are rewritten.
    const specNames = (root.getFullText().match(/\/\/@[^\r\n]*/g) ?? [])
      .flatMap(comment => comment.match(/[A-Za-z_]\w*/g) ?? []);
    this.taken = new Set([...this.sourceNames, ...specNames]);
    const outer = new Set<string>();
    for (const symbol of root.getSymbolsInScope(ts.SymbolFlags.Value)) {
      if (!symbol.getDeclarations().some(d => d.getAncestors().includes(root))) outer.add(symbol.getName());
    }
    const locals: { name: string; scope: Node }[] = [];
    // Prefer enclosing locals even if they occur later in source order. This
    // also preserves the existing names of counters hoisted out of for-loops.
    const declarations = root.getDescendantsOfKind(SyntaxKind.VariableDeclaration).sort((a, b) =>
      scopeOf(a).getAncestors().length - scopeOf(b).getAncestors().length || a.getStart() - b.getStart());
    for (const decl of declarations) {
      for (const id of bindings(decl.getNameNode())) {
        const name = id.getText();
        const { scope, mayCapture } = loweredScope(decl);
        const parameterClash = decl.getAncestors().some(a => functionLike(a)
          && a.getChildrenOfKind(SyntaxKind.Parameter).some(p => bindings(p.getNameNode()).some(b => b.getText() === name)));
        const symbol = id.getSymbol();
        const localClash = locals.some(l => l.name === name && (l.scope === scope || scope.getAncestors().includes(l.scope)));
        let emitted = name;
        if (symbol && mayCapture && (outer.has(name) || parameterClash || localClash)) {
          const fresh = this.fresh(name);
          emitted = fresh;
          this.renamed.set(symbol.compilerSymbol, fresh);
          this.aliases.set(name, [...this.aliases.get(name) ?? [], fresh]);
        }
        locals.push({ name: emitted, scope });
        this.used.add(name);
      }
    }
  }

  private fresh(base: string): string {
    let suffix = 2;
    while (this.taken.has(`${base}_${suffix}`)) suffix++;
    const name = `${base}_${suffix}`;
    this.taken.add(name);
    reserveName(name);
    return name;
  }

  name(node: Node): string {
    if (Node.isIdentifier(node)) {
      const symbol = valueSymbol(node);
      return symbol && this.renamed.get(symbol.compilerSymbol) || node.getText();
    }
    // Assignment targets are still strings in Raw IR; rename their root only.
    if (Node.isPropertyAccessExpression(node)) return `${this.name(node.getExpression())}.${node.getName()}`;
    return node.getText();
  }

  /** A local type override follows every renamed binding of that source name. */
  typeNames(name: string): string[] {
    return [name, ...this.aliases.get(name) ?? []];
  }

  withScope<T>(action: () => T): T {
    const outer = this.ghosts;
    this.ghosts = new Map(outer);
    try { return action(); } finally { this.ghosts = outer; }
  }

  ghost(name: string, location: Node, pos: number): string {
    const emitted = this.used.has(name) || this.sourceNames.has(name) ? this.fresh(name) : name;
    this.used.add(name);
    reserveName(emitted);
    this.ghosts.set(name, { name: emitted, scope: scopeOf(location), pos });
    return emitted;
  }

  specName(name: string, location: Node, pos = location.getStart()): string {
    // Leading comments belong to the statement's enclosing scope, including
    // when the statement itself is a block or another loop.
    const symbol = location.getProject().getTypeChecker().resolveName(name, location.getParent(), ts.SymbolFlags.Value, false);
    const ghost = this.ghosts.get(name);
    if (ghost) {
      // A nested source binding shadows an outer ghost in specs. In the same
      // scope, the most recent declaration wins. Runtime reads always use the
      // TS symbol, never this separate ghost environment.
      const shadowed = symbol?.getDeclarations().some(d => {
        const scope = scopeOf(d);
        return scope === ghost.scope ? d.getStart() > ghost.pos && d.getStart() < pos
          : scope.getAncestors().includes(ghost.scope);
      });
      if (!shadowed) return ghost.name;
    }
    return symbol && this.renamed.get(symbol.compilerSymbol) || name;
  }

  spec(text: string, location: Node, pos?: number): string {
    if (this.renamed.size === 0 && this.ghosts.size === 0) return text;
    return renameSpecVariables(text, name => this.specName(name, location, pos));
  }
}

/** Backend lambdas cannot capture a local that is declared later. Checking
 *  symbols here avoids silently binding the closure to an outer namesake.
 *  Callback parameter defaults have their own initialization model in resolve. */
export function rejectForwardLocalCaptures(arrow: import("ts-morph").ArrowFunction): void {
  const body = arrow.getBody();
  const identifiers = Node.isIdentifier(body) ? [body] : body.getDescendantsOfKind(SyntaxKind.Identifier);
  for (const id of identifiers) {
    if (id.getAncestors().some(n => ts.isTypeNode(n.compilerNode))) continue;
    for (const binding of valueSymbol(id)?.getDeclarations() ?? []) {
      const decl = Node.isVariableDeclaration(binding) ? binding
        : Node.isBindingElement(binding) ? binding.getFirstAncestorByKind(SyntaxKind.VariableDeclaration) : undefined;
      if (!decl || decl.getStart() <= arrow.getStart() || decl.getAncestors().includes(arrow)) continue;
      const list = decl.getParent();
      if (!Node.isVariableDeclarationList(list) || list.getDeclarationKind() === "var") continue;
      if (Node.isSourceFile(scopeOf(decl))) continue;
      throw new Error(`Unsupported forward capture '${id.getText()}' at line ${arrow.getStartLineNumber()}: `
        + `closure captures a local declared later at line ${decl.getStartLineNumber()}`);
    }
  }
}
