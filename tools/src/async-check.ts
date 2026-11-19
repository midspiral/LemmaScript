/**
 * Async stage 1 — the fragment where `await` can be erased.
 *
 * An async function is verified as a sequential function whose `await e`
 * denotes the fulfillment value of `e`, and whose `throw` rejects the returned
 * promise (a path with no fulfillment, so no postcondition applies). This is
 * exact when no other computation can observe or change what the function
 * relies on across a suspension. `checkAsyncFragment` enforces that:
 *
 *  - every promise-valued call is directly awaited (or returned from an async
 *    function), so a rejection ends the caller's path at the call site;
 *  - `await` appears only as a whole declaration initializer, assignment
 *    right-hand side, return value, or expression statement;
 *  - an awaited operand is a call, a promise parameter, or a plain
 *    (non-thenable) value;
 *  - a value of reference type is not read after a suspension that follows
 *    its binding (another task may have mutated it meanwhile); `this` is
 *    not used, and there are no async callbacks.
 *
 * See SPEC.md §4.5.
 */

import { Node, SyntaxKind, Type } from "ts-morph";

type FnLike = Node & { getBody(): Node | undefined };

export function isAsyncFunction(fn: Node): boolean {
  return (fn as { isAsync?: () => boolean }).isAsync?.() ?? false;
}

export function isPromiseType(t: Type): boolean {
  const name = (t.getSymbol() ?? t.getAliasSymbol())?.getName();
  return name === "Promise" && t.getTypeArguments().length <= 1;
}

/** `Promise<T>` → `T` (`Promise<void>` / bare `Promise` → `void`); other types unchanged. */
export function fulfillmentType(t: Type): Type | "void" {
  if (!isPromiseType(t)) return t;
  const args = t.getTypeArguments();
  return args.length === 1 ? args[0] : "void";
}

/** Could awaiting a value of this type run user code (a thenable)? */
function mayBeThenable(t: Type): boolean {
  if (t.isAny() || t.isUnknown() || isPromiseType(t)) return true;
  if (t.isUnion()) return t.getUnionTypes().some(mayBeThenable);
  if (t.isIntersection()) return t.getIntersectionTypes().some(mayBeThenable);
  if (t.isTypeParameter()) return true;
  return t.isObject() && t.getProperty("then") !== undefined;
}

/** Immutable values: safe to retain across a suspension. */
function isValueType(t: Type): boolean {
  if (t.isString() || t.isNumber() || t.isBigInt() || t.isBoolean() || t.isUndefined() || t.isNull()
      || t.isLiteral() || t.isBooleanLiteral() || t.isEnum() || t.isEnumLiteral() || t.isTemplateLiteral()
      || t.isVoid() || t.isNever()) return true;
  if (t.isUnion()) return t.getUnionTypes().every(isValueType);
  // A promise's outcome is permanent once settled; it is modeled by that outcome.
  if (isPromiseType(t)) return true;
  return false;
}

const FUNCTION_KINDS = new Set([
  SyntaxKind.FunctionDeclaration, SyntaxKind.MethodDeclaration, SyntaxKind.ArrowFunction,
  SyntaxKind.FunctionExpression, SyntaxKind.Constructor, SyntaxKind.GetAccessor, SyntaxKind.SetAccessor,
]);

function nearestFunction(node: Node): Node | undefined {
  for (let p = node.getParent(); p; p = p.getParent()) if (FUNCTION_KINDS.has(p.getKind())) return p;
  return undefined;
}

/** Skip type-only wrappers and parentheses between an expression and its consumer. */
function consumer(node: Node): { parent: Node | undefined; child: Node } {
  let child = node;
  let parent = node.getParent();
  while (parent && (Node.isParenthesizedExpression(parent) || Node.isAsExpression(parent)
      || Node.isTypeAssertion(parent) || Node.isNonNullExpression(parent) || Node.isSatisfiesExpression(parent))) {
    child = parent;
    parent = parent.getParent();
  }
  return { parent, child };
}

function stripParens(node: Node): Node {
  while (Node.isParenthesizedExpression(node) || Node.isAsExpression(node) || Node.isNonNullExpression(node)
      || Node.isSatisfiesExpression(node) || Node.isTypeAssertion(node)) node = node.getExpression();
  return node;
}

const LOOP_KINDS = new Set([
  SyntaxKind.WhileStatement, SyntaxKind.DoStatement, SyntaxKind.ForStatement,
  SyntaxKind.ForOfStatement, SyntaxKind.ForInStatement,
]);

/** Calls that return a newly allocated array or object. */
const FRESH_METHODS = new Set(["slice", "map", "filter", "concat", "flatMap", "toSorted", "toReversed", "toSpliced", "with"]);
function isFreshAllocation(e: Node): boolean {
  e = stripParens(e);
  if (Node.isArrayLiteralExpression(e) || Node.isObjectLiteralExpression(e)) return true;
  if (!Node.isCallExpression(e)) return false;
  const callee = e.getExpression();
  if (!Node.isPropertyAccessExpression(callee)) return false;
  const recv = callee.getExpression().getText();
  return FRESH_METHODS.has(callee.getName())
    || (recv === "Array" && callee.getName() === "from")
    || (recv === "Object" && ["keys", "values", "entries"].includes(callee.getName()));
}

/** A `const` initialized with a fresh allocation whose every use reads from it
 *  in place: no other computation can hold a reference to mutate it. */
function isUnescapedFreshLocal(decl: Node, body: Node): boolean {
  if (!Node.isVariableDeclaration(decl) || !Node.isIdentifier(decl.getNameNode())) return false;
  const list = decl.getParent();
  if (!Node.isVariableDeclarationList(list) || list.getDeclarationKind() !== "const") return false;
  const init = decl.getInitializer();
  if (!init || !isFreshAllocation(init)) return false;
  return (decl.getNameNode() as import("ts-morph").Identifier).findReferencesAsNodes().every(ref => {
    if (ref === decl.getNameNode()) return true;
    if (!body.containsRange(ref.getPos(), ref.getEnd())) return false;
    const { parent, child } = consumer(ref);
    if (!parent) return false;
    if (Node.isPropertyAccessExpression(parent) || Node.isElementAccessExpression(parent))
      return parent.getExpression() === child;
    if (Node.isForOfStatement(parent)) return parent.getExpression() === child;
    if (Node.isSpreadElement(parent)) return Node.isArrayLiteralExpression(parent.getParent());
    return false;
  });
}

export interface AsyncCheckOptions {
  /** Statements whose right-hand side is discarded (`//@ havoc`). */
  isHavocked: (stmt: Node) => boolean;
}

/**
 * Throws if `fn` steps outside the stage-1 async fragment. Applies to every
 * extracted function: synchronous ones may not create promises either.
 */
export function checkAsyncFragment(fn: FnLike, name: string, opts: AsyncCheckOptions): void {
  const body = fn.getBody();
  if (!body) return;
  const isAsync = isAsyncFunction(fn);
  const fail = (node: Node, why: string): never => {
    throw new Error(`${name} (line ${node.getStartLineNumber()}): ${why}`);
  };
  const havocked = (node: Node): boolean => {
    const stmt = node.getFirstAncestor(a => Node.isStatement(a));
    return !!stmt && opts.isHavocked(stmt);
  };
  const ownedByFn = (node: Node) => nearestFunction(node) === fn;

  // Async callbacks run on their own schedule: not modeled.
  for (const k of [SyntaxKind.ArrowFunction, SyntaxKind.FunctionExpression]) {
    for (const lam of body.getDescendantsOfKind(k)) {
      if (isAsyncFunction(lam)) fail(lam, "async callbacks are not supported; only top-level async functions are");
    }
  }

  // Every promise-valued call is consumed immediately by `await` or `return`.
  for (const call of body.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    if (!isPromiseType(call.getType()) || havocked(call)) continue;
    const { parent } = consumer(call);
    const awaited = !!parent && Node.isAwaitExpression(parent) && ownedByFn(parent);
    const returned = isAsync && !!parent && Node.isReturnStatement(parent) && ownedByFn(parent);
    if (!awaited && !returned) {
      fail(call, `the promise from '${call.getExpression().getText()}(...)' must be awaited where it is created`
        + (isAsync ? " (or returned)" : "; a synchronous function cannot consume it"));
    }
  }

  if (!isAsync) return;

  const thisNode = body.getFirstDescendantByKind(SyntaxKind.ThisKeyword);
  if (thisNode) fail(thisNode, "async methods cannot use 'this': shared state across a suspension is not supported yet");

  const awaits = body.getDescendantsOfKind(SyntaxKind.AwaitExpression).filter(ownedByFn);
  for (const a of awaits) {
    if (havocked(a)) continue;
    const { parent, child } = consumer(a);
    const ok = !!parent && (
      (Node.isVariableDeclaration(parent) && parent.getInitializer() === child
        && Node.isVariableStatement(parent.getParent()?.getParent())) ||
      (Node.isBinaryExpression(parent) && parent.getOperatorToken().getKind() === SyntaxKind.EqualsToken
        && parent.getRight() === child && Node.isExpressionStatement(consumer(parent).parent)) ||
      Node.isReturnStatement(parent) ||
      Node.isExpressionStatement(parent));
    if (!ok) {
      fail(a, "await must be a whole declaration initializer, assignment right-hand side, return value, or statement");
    }
    const operand = stripParens(a.getExpression());
    const t = operand.getType();
    if (isPromiseType(t)) {
      const isCall = Node.isCallExpression(operand);
      const isParam = Node.isIdentifier(operand) && operand.getSymbol()?.getDeclarations()
        .some(d => Node.isParameterDeclaration(d) && d.getParent() === fn);
      if (!isCall && !isParam) fail(a, "an awaited promise must be a call or a parameter");
    } else if (mayBeThenable(t)) {
      fail(a, `awaited value of type '${t.getText()}' may be a thenable`);
    }
  }

  // Promise parameters: awaited, passed on to an awaited call, or returned.
  for (const p of (fn as unknown as { getParameters(): Node[] }).getParameters()) {
    if (!Node.isParameterDeclaration(p) || !isPromiseType(p.getType())) continue;
    const nameNode = p.getNameNode();
    if (!Node.isIdentifier(nameNode)) fail(p, "promise parameters cannot be destructured");
    for (const ref of (nameNode as import("ts-morph").Identifier).findReferencesAsNodes()) {
      if (ref.getSourceFile() !== fn.getSourceFile() || !body.containsRange(ref.getPos(), ref.getEnd())) continue;
      const { parent } = consumer(ref);
      const ok = !!parent && (Node.isAwaitExpression(parent) || Node.isReturnStatement(parent)
        || (Node.isCallExpression(parent) && parent.getArguments().includes(consumer(ref).child as never)
            && isPromiseType(parent.getType())));
      if (!ok) fail(ref, `promise parameter '${p.getName()}' may only be awaited, returned, or passed to an awaited call`);
    }
  }

  if (awaits.length === 0) return;

  // References bound before a suspension may be stale after it.
  const suspensions = awaits.map(a => a.getEnd());
  // The part of each loop that runs again after a suspension. A for-of/for-in
  // evaluates its iterated expression once, before the first iteration.
  const loops = body.getDescendants().filter(n => LOOP_KINDS.has(n.getKind()) && ownedByFn(n)
    && awaits.some(a => n.containsRange(a.getPos(), a.getEnd())))
    .map(l => (Node.isForOfStatement(l) || Node.isForInStatement(l)) ? l.getStatement() : l);
  // A for-of over a live array observes mutations made during its suspensions.
  for (const l of body.getDescendantsOfKind(SyntaxKind.ForOfStatement)) {
    if (!ownedByFn(l) || !awaits.some(a => l.getStatement().containsRange(a.getPos(), a.getEnd()))) continue;
    const iterated = l.getExpression();
    const sym = Node.isIdentifier(stripParens(iterated)) ? stripParens(iterated).getSymbol() : undefined;
    const freshLocal = sym?.getDeclarations().some(d => isUnescapedFreshLocal(d, body));
    if (!isValueType(iterated.getType()) && !isFreshAllocation(iterated) && !freshLocal) {
      fail(iterated, `a loop that awaits may not iterate '${iterated.getText()}' in place: another task may `
        + "modify it during a suspension. Iterate a copy, e.g. [...xs].");
    }
  }
  const bodyStart = body.getStart();
  for (const id of body.getDescendantsOfKind(SyntaxKind.Identifier)) {
    const parent = id.getParent();
    if (!parent) continue;
    if (Node.isPropertyAccessExpression(parent) && parent.getNameNode() === id) continue;
    if ((Node.isVariableDeclaration(parent) || Node.isParameterDeclaration(parent) || Node.isBindingElement(parent)
        || Node.isPropertyAssignment(parent) || Node.isFunctionDeclaration(parent) || Node.isPropertySignature(parent))
        && (parent as unknown as { getNameNode(): Node }).getNameNode() === id) continue;
    if (Node.isBindingElement(parent) && parent.getPropertyNameNode() === id) continue;
    let sym = Node.isShorthandPropertyAssignment(parent) ? parent.getValueSymbol() : id.getSymbol();
    if (!sym) continue;
    sym = sym.getAliasedSymbol() ?? sym;
    const decl = sym.getDeclarations()[0];
    if (!decl || !(Node.isVariableDeclaration(decl) || Node.isParameterDeclaration(decl) || Node.isBindingElement(decl))) continue;
    const t = id.getType();
    if (isValueType(t) || t.getCallSignatures().length > 0) continue;
    if (isUnescapedFreshLocal(decl, body)) continue;
    const local = decl.getSourceFile() === fn.getSourceFile()
      && body.containsRange(decl.getPos(), decl.getEnd());
    const bound = local
      ? (decl.getFirstAncestorByKind(SyntaxKind.VariableDeclaration) ?? decl).getEnd()
      : bodyStart;
    const read = id.getStart();
    const crossed = suspensions.some(s => bound < s && s <= read)
      || loops.some(l => l.containsRange(id.getPos(), id.getEnd()) && bound < l.getStart());
    if (crossed) {
      fail(id, `'${id.getText()}' (type '${t.getText(id)}') is read after an await but bound before it; `
        + "another task may modify it during the suspension. Read what you need before the first await.");
    }
  }
}
