import { Node, SyntaxKind, ts, type ArrowFunction, type Expression, type Identifier, type Symbol, type Type } from "ts-morph";
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

/** `recv.method(callback)`: backends may emit the receiver inside the scope
 *  of the callback's parameter (a comprehension), so the parameter must not
 *  share a name with anything the receiver mentions, library globals included. */
function receiverMentions(callback: Node, name: string): boolean {
  const call = callback.getParent();
  if (!Node.isCallExpression(call) || !call.getArguments().includes(callback)) return false;
  const callee = call.getExpression();
  if (!Node.isPropertyAccessExpression(callee)) return false;
  const receiver = callee.getExpression();
  return [receiver, ...receiver.getDescendantsOfKind(SyntaxKind.Identifier)]
    .some(n => Node.isIdentifier(n) && n.getText() === name);
}

function valueSymbol(node: Identifier): Symbol | undefined {
  const parent = node.getParent();
  return Node.isShorthandPropertyAssignment(parent) ? parent.getValueSymbol() : node.getSymbol();
}

/** Bare blocks and counting-for initializers lose their braces in extraction.
 *  Branch blocks keep separate arms but can absorb their parent's continuation.
 *  `mayCapture` marks a scope that can therefore reach names outside the
 *  function. Loop and lambda scopes remain barriers; siblings there need no
 *  rename, but a binding that shadows an enclosing one always gets one. */
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

/** After extraction no binding in a function shadows another: a local, loop
 *  variable, or callback parameter that reuses an enclosing name is renamed.
 *  Later passes may therefore identify a variable by its name alone.
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
    // Names bound outside the function. A scope that keeps its braces cannot
    // capture a library global, so only this file's own declarations count there.
    const outer = new Set<string>(), moduleNames = new Set<string>();
    const file = root.getSourceFile();
    for (const symbol of root.getSymbolsInScope(ts.SymbolFlags.Value)) {
      const declarations = symbol.getDeclarations();
      if (declarations.some(d => d.getAncestors().includes(root))) continue;
      outer.add(symbol.getName());
      if (declarations.some(d => d.getSourceFile() === file)) moduleNames.add(symbol.getName());
    }
    const locals: { name: string; scope: Node }[] = [];
    // Prefer enclosing locals even if they occur later in source order. This
    // also preserves the existing names of counters hoisted out of for-loops.
    // Callback parameters are bindings too; the function's own stay public.
    const declarations = [...root.getDescendantsOfKind(SyntaxKind.VariableDeclaration),
      ...root.getDescendantsOfKind(SyntaxKind.Parameter).filter(p => {
        const owner = p.getParent();
        return owner !== root && functionLike(owner);
      })].sort((a, b) =>
      scopeOf(a).getAncestors().length - scopeOf(b).getAncestors().length || a.getStart() - b.getStart());
    for (const decl of declarations) {
      const owner = Node.isParameterDeclaration(decl) ? decl.getParent() : undefined;
      for (const id of bindings(decl.getNameNode())) {
        const name = id.getText();
        const { scope, mayCapture } = loweredScope(decl);
        const parameterClash = decl.getAncestors().some(a => a !== owner && functionLike(a)
          && a.getChildrenOfKind(SyntaxKind.Parameter).some(p => bindings(p.getNameNode()).some(b => b.getText() === name)));
        const symbol = id.getSymbol();
        const localClash = locals.some(l => l.name === name && (l.scope === scope || scope.getAncestors().includes(l.scope)));
        let emitted = name;
        if (symbol && ((mayCapture ? outer : moduleNames).has(name) || parameterClash || localClash
            || (owner && receiverMentions(owner, name)))) {
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
    // `_x_idx` is the position of for-of variable `x`; it follows x's rename.
    const index = /^_(.+)_idx$/.exec(name);
    if (index && !this.sourceNames.has(name)) return `_${this.specName(index[1], location, pos)}_idx`;
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

const MUTATING_METHODS = new Set([
  "push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin",
  "set", "add", "delete", "clear",
]);

const IMMEDIATE_ARRAY_CALLBACK_METHODS = new Set([
  "map", "filter", "every", "some", "reduce", "reduceRight",
  "find", "findLast", "findIndex", "findLastIndex", "flatMap", "sort",
]);

const PURE_METHODS = new Set([
  "slice", "concat", "map", "filter", "every", "some", "find", "findLast",
  "findIndex", "findLastIndex", "reduce", "reduceRight", "includes", "indexOf",
  "lastIndexOf", "join", "flat", "flatMap", "at", "with", "toSorted",
  "toReversed", "toSpliced", "entries", "keys", "values", "get", "has",
  "toString", "toLocaleString", "valueOf", "hasOwnProperty",
  "charAt", "charCodeAt", "codePointAt", "startsWith", "endsWith",
  "substring", "substr", "trim", "trimStart", "trimEnd", "toLowerCase",
  "toUpperCase", "split", "replace", "replaceAll", "repeat", "padStart",
  "padEnd", "match", "search", "localeCompare", "normalize",
  "toFixed", "toPrecision", "toExponential", "test", "exec",
]);

const SHALLOW_COPY_ARRAY_METHODS = new Set([
  "slice", "concat", "map", "filter", "flat", "flatMap",
  "toSorted", "toReversed", "toSpliced", "with", "split", "keys", "values", "entries",
]);

const PURE_GLOBAL_OBJECTS = new Set(["Math", "Number", "String", "Boolean", "JSON", "console", "Date"]);
const PURE_GLOBAL_FNS = new Set([
  "BigInt", "Number", "String", "Boolean", "parseInt", "parseFloat",
  "isNaN", "isFinite", "encodeURI", "decodeURI", "encodeURIComponent",
  "decodeURIComponent", "structuredClone",
]);
const PURE_STATIC_METHODS = new Set([
  "Object.keys", "Object.values", "Object.entries", "Object.freeze", "Object.is", "Object.hasOwn",
  "Array.isArray", "Array.from", "Array.of",
]);

const ASSIGNMENT_OPS = new Set<SyntaxKind>([
  SyntaxKind.EqualsToken,
  SyntaxKind.PlusEqualsToken,
  SyntaxKind.MinusEqualsToken,
  SyntaxKind.AsteriskEqualsToken,
  SyntaxKind.SlashEqualsToken,
  SyntaxKind.PercentEqualsToken,
  SyntaxKind.AsteriskAsteriskEqualsToken,
  SyntaxKind.LessThanLessThanEqualsToken,
  SyntaxKind.GreaterThanGreaterThanEqualsToken,
  SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken,
  SyntaxKind.AmpersandEqualsToken,
  SyntaxKind.BarEqualsToken,
  SyntaxKind.CaretEqualsToken,
  SyntaxKind.AmpersandAmpersandEqualsToken,
  SyntaxKind.BarBarEqualsToken,
  SyntaxKind.QuestionQuestionEqualsToken,
]);

type AliasTarget = ts.Symbol | "this";

interface MutationSummary {
  reassigned: Set<ts.Symbol>;
  mutated: Set<ts.Symbol>;
  mutatedThis: boolean;
  aliases: Map<ts.Symbol, Set<ts.Symbol>>;
  thisAliases: Set<ts.Symbol>;
}

function isPrimitiveType(type: Type): boolean {
  if (type.isUnion()) return type.getUnionTypes().every(isPrimitiveType);
  if (type.isIntersection()) return type.getIntersectionTypes().some(isPrimitiveType);
  return type.isNumber() || type.isNumberLiteral()
    || type.isBigInt() || type.isBigIntLiteral()
    || type.isBoolean() || type.isBooleanLiteral()
    || type.isString() || type.isStringLiteral()
    || type.isUndefined() || type.isNull() || type.isVoid() || type.isNever()
    || type.isEnum() || type.isEnumLiteral() || type.isTemplateLiteral();
}

function isArrayOrTupleType(type: Type): boolean {
  if (type.isUnion()) return type.getUnionTypes().every(isArrayOrTupleType);
  return type.isArray() || type.isTuple() || type.getSymbol()?.getName() === "ReadonlyArray";
}

function hasPrimitiveElements(type: Type): boolean {
  if (type.isUnion()) return type.getUnionTypes().every(hasPrimitiveElements);
  if (type.isTuple()) return type.getTupleElements().every(isPrimitiveType);
  const elem = type.getArrayElementType();
  return elem !== undefined && isPrimitiveType(elem);
}

function hasPrimitiveProperties(type: Type): boolean {
  const props = type.getProperties();
  if (props.length === 0) return false;
  return props.every(p => {
    const decl = p.getValueDeclaration() ?? p.getDeclarations()[0];
    return decl ? isPrimitiveType(p.getTypeAtLocation(decl)) : false;
  });
}

function unwrapExpr(expr: Expression): Expression {
  let cur: Expression = expr;
  while (true) {
    if (Node.isParenthesizedExpression(cur)) cur = cur.getExpression();
    else if (Node.isAsExpression(cur)) cur = cur.getExpression();
    else if (Node.isTypeAssertion(cur)) cur = cur.getExpression();
    else if (Node.isNonNullExpression(cur)) cur = cur.getExpression();
    else if (Node.isSatisfiesExpression(cur)) cur = cur.getExpression();
    else return cur;
  }
}

function isValueReference(id: Identifier): boolean {
  if (id.getAncestors().some(n => ts.isTypeNode(n.compilerNode) || Node.isTypeParameterDeclaration(n))) {
    return false;
  }
  const parent = id.getParent();
  if (!parent) return false;
  if (Node.isPropertyAccessExpression(parent) && parent.getNameNode() === id) return false;
  if (Node.isPropertyAssignment(parent) && parent.getNameNode() === id) return false;
  if (Node.isBindingElement(parent) && parent.getPropertyNameNode() === id) return false;
  if (Node.isLabeledStatement(parent) || Node.isBreakStatement(parent) || Node.isContinueStatement(parent)) return false;
  if ((Node.isVariableDeclaration(parent) || Node.isParameterDeclaration(parent) || Node.isBindingElement(parent)
      || Node.isFunctionDeclaration(parent) || Node.isMethodDeclaration(parent) || Node.isGetAccessorDeclaration(parent)
      || Node.isSetAccessorDeclaration(parent) || Node.isPropertyDeclaration(parent) || Node.isPropertySignature(parent)
      || Node.isMethodSignature(parent) || Node.isEnumMember(parent) || Node.isInterfaceDeclaration(parent)
      || Node.isTypeAliasDeclaration(parent) || Node.isClassDeclaration(parent) || Node.isEnumDeclaration(parent))
      && parent.getNameNode() === id) {
    return false;
  }
  if (Node.isImportSpecifier(parent) || Node.isImportClause(parent) || Node.isNamespaceImport(parent)
      || Node.isExportSpecifier(parent)) {
    return false;
  }
  return true;
}

function rootTargets(expr: Expression): { target: AliasTarget; direct: boolean }[] {
  const cur = unwrapExpr(expr);
  if (Node.isIdentifier(cur)) {
    const sym = valueSymbol(cur)?.compilerSymbol;
    return sym ? [{ target: sym, direct: true }] : [];
  }
  if (cur.getKind() === SyntaxKind.ThisKeyword) {
    return [{ target: "this", direct: true }];
  }
  if (Node.isPropertyAccessExpression(cur) || Node.isElementAccessExpression(cur)) {
    return rootTargets(cur.getExpression()).map(t => ({ target: t.target, direct: false }));
  }
  if (Node.isArrayLiteralExpression(cur)) {
    return cur.getElements().flatMap(el => {
      if (Node.isOmittedExpression(el)) return [];
      const inner = Node.isSpreadElement(el) ? el.getExpression()
        : Node.isBinaryExpression(el) && el.getOperatorToken().getKind() === SyntaxKind.EqualsToken ? el.getLeft()
        : el;
      return rootTargets(inner);
    });
  }
  if (Node.isObjectLiteralExpression(cur)) {
    return cur.getProperties().flatMap(prop => {
      if (Node.isShorthandPropertyAssignment(prop)) {
        const sym = prop.getValueSymbol()?.compilerSymbol;
        return sym ? [{ target: sym, direct: true }] : [];
      }
      if (Node.isPropertyAssignment(prop)) {
        const init = prop.getInitializer();
        if (!init) return [];
        const inner = Node.isBinaryExpression(init) && init.getOperatorToken().getKind() === SyntaxKind.EqualsToken
          ? init.getLeft() : init;
        return rootTargets(inner);
      }
      if (Node.isSpreadAssignment(prop)) return rootTargets(prop.getExpression());
      return [];
    });
  }
  return [];
}

function extractAliasedRefs(expr: Expression): AliasTarget[] {
  const cur = unwrapExpr(expr);
  if (Node.isIdentifier(cur)) {
    if (isPrimitiveType(cur.getType())) return [];
    const sym = valueSymbol(cur)?.compilerSymbol;
    return sym ? [sym] : [];
  }
  if (cur.getKind() === SyntaxKind.ThisKeyword) return ["this"];
  if (Node.isPropertyAccessExpression(cur) || Node.isElementAccessExpression(cur)) {
    if (isPrimitiveType(cur.getType())) return [];
    return extractAliasedRefs(cur.getExpression());
  }
  if (Node.isConditionalExpression(cur)) {
    return [...extractAliasedRefs(cur.getWhenTrue()), ...extractAliasedRefs(cur.getWhenFalse())];
  }
  if (Node.isBinaryExpression(cur)) {
    const op = cur.getOperatorToken().getKind();
    if (op === SyntaxKind.BarBarToken || op === SyntaxKind.AmpersandAmpersandToken || op === SyntaxKind.QuestionQuestionToken) {
      return [...extractAliasedRefs(cur.getLeft()), ...extractAliasedRefs(cur.getRight())];
    }
    return [];
  }
  if (Node.isArrayLiteralExpression(cur)) {
    return cur.getElements().flatMap(el => {
      if (Node.isOmittedExpression(el)) return [];
      if (Node.isSpreadElement(el)) {
        const inner = el.getExpression();
        return hasPrimitiveElements(inner.getType()) ? [] : extractAliasedRefs(inner);
      }
      return isPrimitiveType(el.getType()) ? [] : extractAliasedRefs(el);
    });
  }
  if (Node.isObjectLiteralExpression(cur)) {
    return cur.getProperties().flatMap(prop => {
      if (Node.isShorthandPropertyAssignment(prop)) {
        const nameNode = prop.getNameNode();
        if (isPrimitiveType(nameNode.getType())) return [];
        const sym = prop.getValueSymbol()?.compilerSymbol;
        return sym ? [sym] : [];
      }
      if (Node.isPropertyAssignment(prop)) {
        const init = prop.getInitializer();
        return init && !isPrimitiveType(init.getType()) ? extractAliasedRefs(init) : [];
      }
      if (Node.isSpreadAssignment(prop)) {
        const inner = prop.getExpression();
        return hasPrimitiveProperties(inner.getType()) ? [] : extractAliasedRefs(inner);
      }
      return [];
    });
  }
  if (Node.isArrowFunction(cur) || Node.isFunctionExpression(cur)) {
    const refs: AliasTarget[] = [];
    const body = cur.getBody();
    for (const n of [body, ...body.getDescendants()]) {
      if (n.getKind() === SyntaxKind.ThisKeyword) refs.push("this");
      else if (Node.isIdentifier(n) && isValueReference(n) && !isPrimitiveType(n.getType())) {
        const sym = valueSymbol(n)?.compilerSymbol;
        if (sym) refs.push(sym);
      }
    }
    return refs;
  }
  if (Node.isNewExpression(cur)) {
    const refs: AliasTarget[] = [];
    for (const arg of cur.getArguments()) {
      if (Node.isExpression(arg) && !isPrimitiveType(arg.getType())) refs.push(...extractAliasedRefs(arg));
    }
    return refs;
  }
  if (Node.isCallExpression(cur)) {
    const callee = cur.getExpression();
    if (Node.isPropertyAccessExpression(callee)) {
      const recv = callee.getExpression();
      const method = callee.getName();
      const staticName = Node.isIdentifier(recv) ? `${recv.getText()}.${method}` : "";
      if (PURE_STATIC_METHODS.has(staticName)) {
        if (staticName === "Array.from" && cur.getArguments().length >= 1) {
          const arg0 = cur.getArguments()[0];
          if (Node.isExpression(arg0) && !hasPrimitiveElements(cur.getType())) return extractAliasedRefs(arg0);
        }
        if (staticName === "Array.of" && !hasPrimitiveElements(cur.getType())) {
          return cur.getArguments().flatMap(a =>
            Node.isExpression(a) && !isPrimitiveType(a.getType()) ? extractAliasedRefs(a) : []);
        }
        if ((staticName === "Object.values" || staticName === "Object.entries") && cur.getArguments().length >= 1) {
          const arg0 = cur.getArguments()[0];
          if (Node.isExpression(arg0) && !hasPrimitiveProperties(arg0.getType())) return extractAliasedRefs(arg0);
        }
        return [];
      }
      if (SHALLOW_COPY_ARRAY_METHODS.has(method) && hasPrimitiveElements(cur.getType())) return [];
      if (method === "get" && !isPrimitiveType(cur.getType())) return extractAliasedRefs(recv);
      const refs: AliasTarget[] = [];
      if (!isPrimitiveType(recv.getType())) refs.push(...extractAliasedRefs(recv));
      for (const arg of cur.getArguments()) {
        if (Node.isExpression(arg) && !isPrimitiveType(arg.getType())) refs.push(...extractAliasedRefs(arg));
      }
      return refs;
    }
    if (Node.isIdentifier(callee) && PURE_GLOBAL_FNS.has(callee.getText())) return [];
    const refs: AliasTarget[] = [];
    for (const arg of cur.getArguments()) {
      if (Node.isExpression(arg) && !isPrimitiveType(arg.getType())) refs.push(...extractAliasedRefs(arg));
    }
    return refs;
  }
  return [];
}

function addAliasEdge(summary: MutationSummary, a: AliasTarget, b: AliasTarget): void {
  if (a === b) return;
  if (a === "this" && b !== "this") { summary.thisAliases.add(b); return; }
  if (b === "this" && a !== "this") { summary.thisAliases.add(a); return; }
  if (a === "this" || b === "this") return;
  let sa = summary.aliases.get(a);
  if (!sa) { sa = new Set(); summary.aliases.set(a, sa); }
  sa.add(b);
  let sb = summary.aliases.get(b);
  if (!sb) { sb = new Set(); summary.aliases.set(b, sb); }
  sb.add(a);
}

function hasPureAnnotation(decl: Node): boolean {
  if (decl.getLeadingCommentRanges().some(r => r.getText().trim() === "//@ pure")) return true;
  const parent = decl.getParent();
  if (parent && Node.isVariableDeclarationList(parent)) {
    const stmt = parent.getParent();
    if (stmt && stmt.getLeadingCommentRanges().some(r => r.getText().trim() === "//@ pure")) return true;
  }
  return false;
}

function resolveCallableBody(callee: Expression): { params: Node[]; body: Node; owner: Node } | null {
  const sym = callee.getSymbol();
  const resolved = sym?.getAliasedSymbol() ?? sym;
  for (const decl of resolved?.getDeclarations() ?? []) {
    if (Node.isFunctionDeclaration(decl) || Node.isMethodDeclaration(decl)) {
      const body = decl.getBody();
      if (body) return { params: decl.getParameters(), body, owner: decl };
    }
    if (Node.isVariableDeclaration(decl)) {
      const init = decl.getInitializer();
      if (init && (Node.isArrowFunction(init) || Node.isFunctionExpression(init))) {
        return { params: init.getParameters(), body: init.getBody(), owner: init };
      }
    }
  }
  return null;
}

function resolveCallableIsPureExtern(callee: Expression): boolean {
  const sym = callee.getSymbol();
  const resolved = sym?.getAliasedSymbol() ?? sym;
  return (resolved?.getDeclarations() ?? []).some(hasPureAnnotation);
}

function propagateAliases(summary: MutationSummary): { mutated: Set<ts.Symbol>; mutatedThis: boolean } {
  const mutated = new Set(summary.mutated);
  let mutatedThis = summary.mutatedThis;
  const queue: ts.Symbol[] = [...mutated];
  if (mutatedThis) {
    for (const sym of summary.thisAliases) {
      if (!mutated.has(sym)) { mutated.add(sym); queue.push(sym); }
    }
  }
  while (queue.length > 0) {
    const cur = queue.pop()!;
    if (summary.thisAliases.has(cur)) mutatedThis = true;
    for (const next of summary.aliases.get(cur) ?? []) {
      if (!mutated.has(next)) { mutated.add(next); queue.push(next); }
    }
  }
  if (mutatedThis) {
    for (const sym of summary.thisAliases) {
      if (!mutated.has(sym)) {
        mutated.add(sym);
        const sub = [sym];
        while (sub.length > 0) {
          const c = sub.pop()!;
          for (const n of summary.aliases.get(c) ?? []) {
            if (!mutated.has(n)) { mutated.add(n); sub.push(n); }
          }
        }
      }
    }
  }
  return { mutated, mutatedThis };
}

function analyzeCallableEffects(
  callable: { params: Node[]; body: Node; owner: Node },
  visited: Set<Node>,
): { mutatedParams: Set<number>; mutatesThis: boolean } {
  if (visited.has(callable.owner)) return { mutatedParams: new Set(), mutatesThis: false };
  visited.add(callable.owner);
  const summary = analyzeMutations(callable.body, visited);
  const { mutated, mutatedThis } = propagateAliases(summary);
  const mutatedParams = new Set<number>();
  callable.params.forEach((p, idx) => {
    if (!Node.isParameterDeclaration(p)) return;
    for (const id of bindings(p.getNameNode())) {
      const sym = id.getSymbol()?.compilerSymbol;
      if (sym && mutated.has(sym)) mutatedParams.add(idx);
    }
  });
  return { mutatedParams, mutatesThis: mutatedThis };
}

function markTargetsMutated(summary: MutationSummary, expr: Expression): void {
  for (const { target } of rootTargets(expr)) {
    if (target === "this") summary.mutatedThis = true;
    else summary.mutated.add(target);
  }
}

function analyzeMutations(root: Node, visited: Set<Node> = new Set()): MutationSummary {
  const summary: MutationSummary = {
    reassigned: new Set(),
    mutated: new Set(),
    mutatedThis: false,
    aliases: new Map(),
    thisAliases: new Set(),
  };

  const nodes = [root, ...root.getDescendants()];
  for (const node of nodes) {
    if (Node.isBinaryExpression(node) && ASSIGNMENT_OPS.has(node.getOperatorToken().getKind())) {
      const left = node.getLeft();
      for (const { target, direct } of rootTargets(left)) {
        if (target === "this") summary.mutatedThis = true;
        else if (direct) summary.reassigned.add(target);
        else summary.mutated.add(target);
      }
      if (node.getOperatorToken().getKind() === SyntaxKind.EqualsToken && !isPrimitiveType(left.getType())) {
        const rhsRefs = extractAliasedRefs(node.getRight());
        for (const { target } of rootTargets(left)) {
          for (const ref of rhsRefs) addAliasEdge(summary, target, ref);
        }
      }
      continue;
    }

    if (Node.isPrefixUnaryExpression(node) || Node.isPostfixUnaryExpression(node)) {
      const op = node.getOperatorToken();
      if (op === SyntaxKind.PlusPlusToken || op === SyntaxKind.MinusMinusToken) {
        for (const { target, direct } of rootTargets(node.getOperand())) {
          if (target === "this") summary.mutatedThis = true;
          else if (direct) summary.reassigned.add(target);
          else summary.mutated.add(target);
        }
      }
      continue;
    }

    if (Node.isDeleteExpression(node)) {
      markTargetsMutated(summary, node.getExpression());
      continue;
    }

    if ((Node.isForOfStatement(node) || Node.isForInStatement(node)) && Node.isExpression(node.getInitializer())) {
      const init = node.getInitializer() as Expression;
      for (const { target, direct } of rootTargets(init)) {
        if (target === "this") summary.mutatedThis = true;
        else if (direct) summary.reassigned.add(target);
        else summary.mutated.add(target);
      }
      continue;
    }

    if (Node.isVariableDeclaration(node)) {
      const init = node.getInitializer();
      if (!init) continue;
      const rhsRefs = extractAliasedRefs(init);
      if (rhsRefs.length === 0) continue;
      for (const id of bindings(node.getNameNode())) {
        if (isPrimitiveType(id.getType())) continue;
        const sym = id.getSymbol()?.compilerSymbol;
        if (!sym) continue;
        for (const ref of rhsRefs) addAliasEdge(summary, sym, ref);
      }
      continue;
    }

    if (Node.isCallExpression(node)) {
      const callee = node.getExpression();
      const args = node.getArguments().filter(Node.isExpression);
      if (Node.isPropertyAccessExpression(callee)) {
        const recv = callee.getExpression();
        const method = callee.getName();
        const staticName = Node.isIdentifier(recv) ? `${recv.getText()}.${method}` : "";
        if (staticName === "Object.assign" || staticName === "Object.defineProperty") {
          if (args[0]) {
            markTargetsMutated(summary, args[0]);
            const dstTargets = rootTargets(args[0]);
            for (let i = 1; i < args.length; i++) {
              if (isPrimitiveType(args[i].getType())) continue;
              for (const { target } of dstTargets) {
                for (const ref of extractAliasedRefs(args[i])) addAliasEdge(summary, target, ref);
              }
            }
          }
          continue;
        }
        if (PURE_STATIC_METHODS.has(staticName)
            || (Node.isIdentifier(recv) && PURE_GLOBAL_OBJECTS.has(recv.getText()))) {
          continue;
        }
        if (MUTATING_METHODS.has(method)) {
          markTargetsMutated(summary, recv);
          const recvTargets = rootTargets(recv);
          for (const arg of args) {
            if (isPrimitiveType(arg.getType())) continue;
            for (const { target } of recvTargets) {
              for (const ref of extractAliasedRefs(arg)) addAliasEdge(summary, target, ref);
            }
          }
          continue;
        }
        const callable = resolveCallableBody(callee);
        if (callable) {
          const effects = analyzeCallableEffects(callable, new Set(visited));
          if (effects.mutatesThis) markTargetsMutated(summary, recv);
          for (const idx of effects.mutatedParams) {
            if (args[idx]) markTargetsMutated(summary, args[idx]);
          }
          continue;
        }
        if (!PURE_METHODS.has(method) && !isPrimitiveType(recv.getType()) && !resolveCallableIsPureExtern(callee)) {
          markTargetsMutated(summary, recv);
          for (const arg of args) {
            if (!isPrimitiveType(arg.getType())) markTargetsMutated(summary, arg);
          }
        }
        continue;
      }

      if (Node.isIdentifier(callee) && PURE_GLOBAL_FNS.has(callee.getText())) continue;
      const callable = resolveCallableBody(callee);
      if (callable) {
        const effects = analyzeCallableEffects(callable, new Set(visited));
        for (const idx of effects.mutatedParams) {
          if (args[idx]) markTargetsMutated(summary, args[idx]);
        }
      } else if (!resolveCallableIsPureExtern(callee)) {
        for (const arg of args) {
          if (!isPrimitiveType(arg.getType())) markTargetsMutated(summary, arg);
        }
      }
    }
  }

  return summary;
}

function collectCaptures(arrow: ArrowFunction): {
  bindings: Map<ts.Symbol, { name: string; isModuleLevel: boolean; isMutableDecl: boolean }>;
  capturesThis: boolean;
} {
  const captured = new Map<ts.Symbol, { name: string; isModuleLevel: boolean; isMutableDecl: boolean }>();
  const file = arrow.getSourceFile();
  const scanRoots: Node[] = [
    arrow.getBody(),
    ...arrow.getParameters().map(p => p.getInitializer()).filter((n): n is Expression => n !== undefined),
  ];
  let capturesThis = false;

  for (const scanRoot of scanRoots) {
    const nodes = [scanRoot, ...scanRoot.getDescendants()];
    for (const node of nodes) {
      if (node.getKind() === SyntaxKind.ThisKeyword) {
        const ownerFn = node.getFirstAncestor(a =>
          Node.isFunctionExpression(a) || Node.isFunctionDeclaration(a) || Node.isMethodDeclaration(a));
        if (!ownerFn || !ownerFn.getAncestors().includes(arrow)) capturesThis = true;
        continue;
      }
      if (!Node.isIdentifier(node) || !isValueReference(node)) continue;
      const sym = valueSymbol(node);
      if (!sym || captured.has(sym.compilerSymbol)) continue;
      for (const decl of sym.getDeclarations()) {
        if (decl.getSourceFile() !== file) continue;
        if (decl === arrow || decl.getAncestors().includes(arrow)) continue;
        if (!Node.isVariableDeclaration(decl) && !Node.isBindingElement(decl) && !Node.isParameterDeclaration(decl)) continue;
        const varDecl = Node.isVariableDeclaration(decl) ? decl
          : Node.isBindingElement(decl) ? decl.getFirstAncestorByKind(SyntaxKind.VariableDeclaration) : undefined;
        const list = varDecl?.getParent();
        const isMutableDecl = !!(list && Node.isVariableDeclarationList(list) && list.getDeclarationKind() !== "const");
        const isModuleLevel = Node.isSourceFile(scopeOf(varDecl ?? decl));
        captured.set(sym.compilerSymbol, { name: node.getText(), isModuleLevel, isMutableDecl });
        break;
      }
    }
  }
  return { bindings: captured, capturesThis };
}

function enclosingAnalysisRoot(arrow: ArrowFunction): Node {
  let outermost: Node = arrow;
  for (const anc of arrow.getAncestors()) {
    if (Node.isSourceFile(anc)) break;
    if (functionLike(anc) || Node.isConstructorDeclaration(anc)
        || Node.isGetAccessorDeclaration(anc) || Node.isSetAccessorDeclaration(anc)
        || (Node.isVariableDeclaration(anc) && Node.isSourceFile(scopeOf(anc)))) {
      outermost = anc;
    }
  }
  return outermost;
}

function targetsOverlapViaAliases(
  targets: { target: AliasTarget }[],
  captured: Map<ts.Symbol, unknown>,
  capturesThis: boolean,
  summary: MutationSummary,
): boolean {
  const visited = new Set<ts.Symbol>();
  let reachesThis = false;
  const queue: ts.Symbol[] = [];
  for (const { target } of targets) {
    if (target === "this") {
      reachesThis = true;
      for (const sym of summary.thisAliases) {
        if (!visited.has(sym)) { visited.add(sym); queue.push(sym); }
      }
    } else if (!visited.has(target)) {
      visited.add(target);
      queue.push(target);
    }
  }
  while (queue.length > 0) {
    const cur = queue.pop()!;
    if (captured.has(cur)) return true;
    if (summary.thisAliases.has(cur)) {
      reachesThis = true;
      for (const sym of summary.thisAliases) {
        if (!visited.has(sym)) { visited.add(sym); queue.push(sym); }
      }
    }
    for (const next of summary.aliases.get(cur) ?? []) {
      if (!visited.has(next)) { visited.add(next); queue.push(next); }
    }
  }
  return reachesThis && capturesThis;
}

function isImmediatePureArrayCallback(
  arrow: ArrowFunction,
  captured: Map<ts.Symbol, unknown>,
  capturesThis: boolean,
  getEnclosingMut: () => MutationSummary,
): boolean {
  let cur: Node = arrow;
  while (cur.getParent() && Node.isParenthesizedExpression(cur.getParent()!)) {
    cur = cur.getParent()!;
  }
  const call = cur.getParent();
  if (!call || !Node.isCallExpression(call)) return false;
  const args = call.getArguments();
  if (args[0] !== cur) return false;
  const callee = call.getExpression();
  if (!Node.isPropertyAccessExpression(callee)) return false;
  const method = callee.getName();
  if (!IMMEDIATE_ARRAY_CALLBACK_METHODS.has(method)) return false;
  const recv = callee.getExpression();
  if (!isArrayOrTupleType(recv.getType())) return false;

  // `sort` mutates its receiver in place while calling the comparator.
  if (method === "sort") {
    const recvTargets = rootTargets(recv);
    for (const { target } of recvTargets) {
      if (target === "this" && capturesThis) return false;
      if (target !== "this" && captured.has(target)) return false;
    }
    if (targetsOverlapViaAliases(recvTargets, captured, capturesThis, getEnclosingMut())) return false;
  }

  // Sibling arguments (e.g. `reduce(cb, init)`) run after the closure is created
  // and before it is invoked; ensure they do not mutate captured bindings.
  for (let i = 1; i < args.length; i++) {
    const arg = args[i];
    if (!Node.isExpression(arg)) continue;
    const argMut = analyzeMutations(arg);
    const { mutated, mutatedThis } = propagateAliases(argMut);
    if (capturesThis && mutatedThis) return false;
    for (const sym of captured.keys()) {
      if (argMut.reassigned.has(sym) || mutated.has(sym)) return false;
    }
  }

  return true;
}

/** Both Dafny and Lean lambdas snapshot captured variables by value at closure
 *  creation time, while JavaScript closures share live bindings and mutable
 *  heap references. Reject any closure that mutates an outer binding or
 *  captures a binding mutated outside an immediate array callback. */
export function rejectMutableCaptures(arrow: ArrowFunction): void {
  const { bindings: captured, capturesThis } = collectCaptures(arrow);
  if (captured.size === 0 && !capturesThis) return;
  const line = arrow.getStartLineNumber();

  // Rule 1: no closure (even an inline callback) may mutate an outer binding.
  const bodyMut = analyzeMutations(arrow.getBody());
  const bodyProp = propagateAliases(bodyMut);
  for (const [sym, info] of captured) {
    if (bodyMut.reassigned.has(sym) || bodyProp.mutated.has(sym)) {
      throw new Error(`Unsupported closure over mutable variable '${info.name}' at line ${line}: `
        + `closure mutates captured outer binding '${info.name}'`);
    }
  }
  if (capturesThis && bodyProp.mutatedThis) {
    throw new Error(`Unsupported closure over mutable 'this' at line ${line}: `
      + `closure mutates captured 'this'`);
  }

  // Rule 2: non-immediate closures cannot capture bindings mutated in the
  // enclosing scope (directly, through an alias, or through a mutating call).
  let cachedEnclosingMut: MutationSummary | undefined;
  const getEnclosingMut = (): MutationSummary => {
    cachedEnclosingMut ??= analyzeMutations(enclosingAnalysisRoot(arrow));
    return cachedEnclosingMut;
  };
  if (isImmediatePureArrayCallback(arrow, captured, capturesThis, getEnclosingMut)) return;

  const enclosingMut = getEnclosingMut();
  const enclosingProp = propagateAliases(enclosingMut);
  for (const [sym, info] of captured) {
    if (enclosingMut.reassigned.has(sym)) {
      throw new Error(`Unsupported closure over mutable variable '${info.name}' at line ${line}: `
        + `captured binding '${info.name}' is reassigned`);
    }
    if (enclosingProp.mutated.has(sym)) {
      throw new Error(`Unsupported closure over mutable variable '${info.name}' at line ${line}: `
        + `captured binding '${info.name}' is mutated`);
    }
    if (info.isModuleLevel && info.isMutableDecl) {
      throw new Error(`Unsupported closure over mutable variable '${info.name}' at line ${line}: `
        + `captured module variable '${info.name}' is mutable`);
    }
  }
  if (capturesThis && enclosingProp.mutatedThis) {
    throw new Error(`Unsupported closure over mutable 'this' at line ${line}: `
      + `captured 'this' is mutated`);
  }
}
