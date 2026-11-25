/**
 * Output checks for the narrow pass.
 *
 * These checks read narrow's output and report shapes that the later passes
 * would emit incorrectly. They do not trust the types that `resolve` stamped on
 * expression nodes: `resolve` copies TypeScript's flow narrowing onto a read of
 * an optional, and that stamp is exactly what is wrong when narrow fails to
 * bind the read inside a `someMatch`. Instead, the type of an access path is
 * recomputed from declarations:
 *
 * - parameters, `let`/`ghostLet`, `for…of` names, lambda parameters and
 *   quantifier variables take their declared `ty`;
 * - `\result` takes the function's return type;
 * - inside the `Some` arm of a `someMatch`, the binder and (for a path
 *   scrutinee) the scrutinee path itself take the binder's type, because
 *   `transform` substitutes the binder for that path;
 * - a field takes its declared type from the receiver's record, union variant,
 *   or class declaration. A field declared with `?` is optional.
 *
 * Paths whose declaration cannot be found (generic records, built-in members,
 * globals) are not checked.
 *
 * Unwrapped-optional check. A violation is reported when
 * - an access path is optional by declaration but `resolve` stamped it
 *   non-optional (it would be emitted as the raw `Option`), or
 * - an optional value is the receiver of a field or index read, an operand of
 *   arithmetic (`+ - * / % **`, unary `-`), one of two optional operands of
 *   a relational comparison, or an argument for a parameter whose resolved
 *   type is a primitive or a collection, or
 * - an arithmetic node stamped optional is an operand of a comparison
 *   (`=== !== < <= > >=`). Arithmetic never yields an optional; the stamp is
 *   left over from before narrow bound its operand, and `transform` lowers the
 *   comparison as a match on an `Option`. Elsewhere the stale stamp is unused.
 * Allowed positions for an optional value: either side of `===`/`!==` (compared
 * with `undefined`, `null`, or a value; `transform` lowers this when exactly one
 * side is optional), one side of a relational comparison (lowered the same
 * way), the left of `??` and the receiver of `?.`, a `someMatch` scrutinee,
 * boolean positions (truthiness), arguments for optional, user-typed or
 * unresolved parameters, and stored values.
 *
 * Binder-collision check. A violation is reported when a `someMatch` binder
 * - equals an identifier in the user's source, or
 * - reuses the name of an enclosing `someMatch` binder whose scrutinee is a
 *   different access path (or is not an access path), which would shadow the
 *   outer value.
 */

import type { TExpr, TStmt, TModule, TFunction, Ty } from "./typedir.js";
import type { FieldInfo, TypeDeclInfo } from "./types.js";
import { parseTsType } from "./types.js";

export type NarrowCheck = "unwrapped-optional" | "binder-collision";

export interface NarrowViolation {
  check: NarrowCheck;
  /** Function (or `Class.method`) containing the violation. */
  fn: string;
  /** The offending expression, or the binder for a binder collision. */
  expr: string;
  detail: string;
}

interface Binding { binder: string; path: string | null }

interface Scope {
  types: Map<string, Ty>;
  binders: Binding[];
}

interface Ctx {
  mod: TModule;
  fn: string;
  userNames: ReadonlySet<string>;
  out: NarrowViolation[];
}

const ARITH = new Set(["+", "-", "*", "/", "%", "**"]);
const RELATIONAL = new Set(["<", "<=", ">", ">="]);
// Operators `transform` lowers as a match when exactly one side is typed optional.
const COMPARISON = new Set([...RELATIONAL, "===", "!=="]);
const STALE_ARITH = "arithmetic result typed as optional; transform will treat the value as an Option";
const isStaleArith = (e: TExpr) =>
  ((e.kind === "binop" && ARITH.has(e.op)) || (e.kind === "unop" && e.op === "-")) && isOptional(e.ty);
// Parameter types that cannot accept an optional argument. A user type may be a
// type parameter instantiated with an optional, so it is not included.
const CONCRETE_PARAM: ReadonlySet<Ty["kind"]> = new Set(["bool", "nat", "int", "real", "string", "array", "tuple", "map", "set"]);

/** Run both checks over every function, method, and constant of a narrowed
 *  module. `userNames` is the set of identifiers in the user's source. */
export function checkNarrowedModule(mod: TModule, userNames: ReadonlySet<string>): NarrowViolation[] {
  const out: NarrowViolation[] = [];
  const globals = new Map<string, Ty>();
  for (const c of mod.constants) globals.set(c.name, c.ty);
  for (const fn of mod.functions) checkFunction(fn, fn.name, null, globals, mod, userNames, out);
  for (const cls of mod.classes) {
    for (const m of cls.methods) {
      checkFunction(m, `${cls.name}.${m.name}`, cls.name, globals, mod, userNames, out);
    }
  }
  for (const c of mod.constants) {
    walkExpr(c.value, { types: new Map(globals), binders: [] }, { mod, fn: c.name, userNames, out });
  }
  return out;
}

function checkFunction(fn: TFunction, label: string, className: string | null, globals: Map<string, Ty>,
  mod: TModule, userNames: ReadonlySet<string>, out: NarrowViolation[]): void {
  const types = new Map(globals);
  for (const p of fn.params) types.set(p.name, p.ty);
  if (className !== null) types.set("this", { kind: "user", name: className });
  const ctx: Ctx = { mod, fn: label, userNames, out };
  const scope: Scope = { types, binders: [] };
  for (const r of fn.requires) walkExpr(r, scope, ctx);
  if (fn.decreases) walkExpr(fn.decreases, scope, ctx);
  const post: Scope = { types: new Map(types), binders: [] };
  post.types.set("\\result", fn.returnTy);
  for (const e of fn.ensures) walkExpr(e, post, ctx);
  walkStmts(fn.body, { types: new Map(types), binders: [] }, ctx);
}

// ── Declared types ──────────────────────────────────────────

export function pathKey(e: TExpr): string | null {
  if (e.kind === "var") return e.name;
  if (e.kind === "field") {
    const inner = pathKey(e.obj);
    return inner === null ? null : `${inner}.${e.field}`;
  }
  return null;
}

function declaredTy(e: TExpr, scope: Scope, ctx: Ctx): Ty | null {
  const key = pathKey(e);
  if (key === null) return null;
  const bound = scope.types.get(key);
  if (bound) return bound;
  if (e.kind !== "field") return null;
  const objTy = declaredTy(e.obj, scope, ctx);
  if (!objTy || objTy.kind === "optional") return null;
  return fieldTy(objTy, e.field, e.ofVariant, ctx);
}

function fieldTy(ty: Ty, field: string, ofVariant: string | undefined, ctx: Ctx, depth = 0): Ty | null {
  if (depth > 8 || ty.kind !== "user") return null;
  const cls = ctx.mod.classes.find(c => c.name === ty.name);
  if (cls) return cls.fields.find(f => f.name === field)?.ty ?? null;
  const decl = ctx.mod.typeDecls.find(d => d.name === ty.name);
  if (!decl || (decl.typeParams && decl.typeParams.length > 0)) return null;
  if (decl.kind === "alias" && decl.aliasOfTy) return fieldTy(decl.aliasOfTy, field, ofVariant, ctx, depth + 1);
  return fieldInfoTy(declField(decl, field, ofVariant));
}

function declField(decl: TypeDeclInfo, field: string, ofVariant: string | undefined): FieldInfo | null {
  if (decl.kind === "record") return decl.fields?.find(f => f.name === field) ?? null;
  if (decl.kind !== "discriminated-union" || !decl.variants) return null;
  const variants = ofVariant ? decl.variants.filter(v => v.name === ofVariant) : decl.variants;
  const found = variants.map(v => v.fields.find(f => f.name === field)).filter((f): f is FieldInfo => !!f);
  // Without a known variant, only trust a field that every variant declaring it agrees is (non-)optional.
  if (found.length === 0) return null;
  const optional = found.map(f => isOptional(fieldInfoTy(f)));
  return optional.every(o => o === optional[0]) ? found[0] : null;
}

function fieldInfoTy(f: FieldInfo | null): Ty | null {
  if (!f) return null;
  const ty = f.type ?? parseTsType(f.tsType);
  return f.optionalKey && ty.kind !== "optional" ? { kind: "optional", inner: ty } : ty;
}

const isOptional = (ty: Ty | null): boolean => ty?.kind === "optional";

/** The type to judge a value by: declared for an access path, otherwise the stamp. */
function valueTy(e: TExpr, scope: Scope, ctx: Ctx): Ty {
  return declaredTy(e, scope, ctx) ?? exprTy(e);
}

function exprTy(e: TExpr): Ty {
  return "ty" in e ? e.ty : { kind: "unknown" };
}

// ── Walkers ─────────────────────────────────────────────────

function report(ctx: Ctx, check: NarrowCheck, e: TExpr | string, detail: string): void {
  ctx.out.push({ check, fn: ctx.fn, expr: typeof e === "string" ? e : show(e), detail });
}

function requireUnwrapped(e: TExpr, role: string, scope: Scope, ctx: Ctx): void {
  // Emitted arithmetic is never an Option; a stale stamp matters only under a comparison.
  if (isStaleArith(e)) return;
  if (isOptional(valueTy(e, scope, ctx))) report(ctx, "unwrapped-optional", e, `optional value used as ${role}`);
}

function withBinder(scope: Scope, binder: string, binderTy: Ty, scrutinee: TExpr, ctx: Ctx): Scope {
  const path = pathKey(scrutinee);
  if (ctx.userNames.has(binder)) {
    report(ctx, "binder-collision", binder, `binder for ${show(scrutinee)} equals a user identifier`);
  }
  const outer = scope.binders.find(b => b.binder === binder);
  if (outer && (outer.path === null || outer.path !== path)) {
    report(ctx, "binder-collision", binder,
      `binder for ${show(scrutinee)} rebinds the enclosing binder for ${outer.path ?? "a non-path scrutinee"}`);
  }
  const types = new Map(scope.types);
  types.set(binder, binderTy);
  if (path !== null) {
    // Facts about the scrutinee's subpaths came from the optional value; keep them.
    types.set(path, binderTy);
  }
  return { types, binders: [...scope.binders, { binder, path }] };
}

function extend(scope: Scope, names: { name: string; ty: Ty }[]): Scope {
  if (names.length === 0) return scope;
  const types = new Map(scope.types);
  for (const n of names) {
    types.set(n.name, n.ty);
    // A rebound name hides any facts about its old subpaths.
    for (const k of [...types.keys()]) if (k.startsWith(`${n.name}.`)) types.delete(k);
  }
  return { types, binders: scope.binders };
}

function walkExpr(e: TExpr, scope: Scope, ctx: Ctx): void {
  switch (e.kind) {
    case "var": {
      const d = declaredTy(e, scope, ctx);
      if (isOptional(d) && !isOptional(e.ty)) {
        report(ctx, "unwrapped-optional", e, "optional by declaration but typed as unwrapped, with no someMatch binding it");
      }
      return;
    }
    case "num": case "bigint": case "str": case "bool": case "havoc":
      return;
    case "field": {
      requireUnwrapped(e.obj, "a field receiver", scope, ctx);
      walkExpr(e.obj, scope, ctx);
      const d = declaredTy(e, scope, ctx);
      if (isOptional(d) && !isOptional(e.ty)) {
        report(ctx, "unwrapped-optional", e, "optional by declaration but typed as unwrapped, with no someMatch binding it");
      }
      return;
    }
    case "index":
      requireUnwrapped(e.obj, "an index receiver", scope, ctx);
      walkExpr(e.obj, scope, ctx);
      walkExpr(e.idx, scope, ctx);
      return;
    case "binop":
      if (ARITH.has(e.op)) {
        requireUnwrapped(e.left, `an operand of ${e.op}`, scope, ctx);
        requireUnwrapped(e.right, `an operand of ${e.op}`, scope, ctx);
      } else if (COMPARISON.has(e.op)) {
        for (const side of [e.left, e.right]) if (isStaleArith(side)) report(ctx, "unwrapped-optional", side, STALE_ARITH);
        if (RELATIONAL.has(e.op) && isOptional(valueTy(e.left, scope, ctx)) && isOptional(valueTy(e.right, scope, ctx))) {
          report(ctx, "unwrapped-optional", e, `both operands of ${e.op} are optional`);
        }
      }
      walkExpr(e.left, scope, ctx);
      walkExpr(e.right, scope, ctx);
      return;
    case "unop":
      if (e.op === "-") requireUnwrapped(e.expr, "an operand of unary -", scope, ctx);
      walkExpr(e.expr, scope, ctx);
      return;
    case "call":
      walkExpr(e.fn, scope, ctx);
      e.args.forEach((a, i) => {
        const p = e.paramTys?.[i];
        if (p && CONCRETE_PARAM.has(p.kind)) requireUnwrapped(a, `an argument for a parameter of type ${p.kind}`, scope, ctx);
        walkExpr(a, scope, ctx);
      });
      return;
    case "record":
      if (e.spread) walkExpr(e.spread, scope, ctx);
      for (const f of e.fields) walkExpr(f.value, scope, ctx);
      return;
    case "arrayLiteral":
      for (const x of e.elems) walkExpr(x, scope, ctx);
      return;
    case "lambda":
      walkStmts(e.body, extend(scope, e.params), ctx);
      return;
    case "conditional":
      walkExpr(e.cond, scope, ctx);
      walkExpr(e.then, scope, ctx);
      walkExpr(e.else, scope, ctx);
      return;
    case "optChain":
      walkExpr(e.obj, scope, ctx);
      for (const step of e.chain) {
        if (step.kind === "call") for (const a of step.args) walkExpr(a, scope, ctx);
        if (step.kind === "index") walkExpr(step.idx, scope, ctx);
      }
      return;
    case "nullish":
      walkExpr(e.left, scope, ctx);
      walkExpr(e.right, scope, ctx);
      return;
    case "someMatch":
      walkScrutinee(e.scrutinee, scope, ctx);
      walkExpr(e.someBody, withBinder(scope, e.binder, e.binderTy, e.scrutinee, ctx), ctx);
      walkExpr(e.noneBody, scope, ctx);
      return;
    case "tagMatch":
      walkExpr(e.scrutinee, scope, ctx);
      for (const c of e.cases) walkExpr(c.body, scope, ctx);
      if (e.fallthrough) walkExpr(e.fallthrough, scope, ctx);
      return;
    case "forall": case "exists":
      walkExpr(e.body, extend(scope, [{ name: e.var, ty: e.varTy }]), ctx);
      return;
  }
}

/** A scrutinee is read as an optional, so its own stamp is not checked. */
function walkScrutinee(e: TExpr, scope: Scope, ctx: Ctx): void {
  if (e.kind === "field") {
    requireUnwrapped(e.obj, "a field receiver", scope, ctx);
    walkExpr(e.obj, scope, ctx);
  } else if (e.kind !== "var") {
    walkExpr(e, scope, ctx);
  }
}

function walkStmts(stmts: TStmt[], scope: Scope, ctx: Ctx): void {
  let cur = scope;
  for (const s of stmts) cur = walkStmt(s, cur, ctx);
}

/** Walk one statement; returns the scope for the statements after it. */
function walkStmt(s: TStmt, scope: Scope, ctx: Ctx): Scope {
  switch (s.kind) {
    case "let": case "ghostLet":
      walkExpr(s.init, scope, ctx);
      return extend(scope, [{ name: s.name, ty: s.ty }]);
    case "assign": case "ghostAssign":
      walkExpr(s.value, scope, ctx);
      return scope;
    case "return":
      walkExpr(s.value, scope, ctx);
      return scope;
    case "expr":
      walkExpr(s.expr, scope, ctx);
      return scope;
    case "assert":
      walkExpr(s.expr, scope, ctx);
      return scope;
    case "break": case "continue": case "throw":
      return scope;
    case "if":
      walkExpr(s.cond, scope, ctx);
      walkStmts(s.then, scope, ctx);
      walkStmts(s.else, scope, ctx);
      return scope;
    case "while":
      walkExpr(s.cond, scope, ctx);
      for (const inv of s.invariants) walkExpr(inv, scope, ctx);
      if (s.decreases) walkExpr(s.decreases, scope, ctx);
      if (s.doneWith) walkExpr(s.doneWith, scope, ctx);
      walkStmts(s.body, scope, ctx);
      return scope;
    case "switch":
      walkExpr(s.expr, scope, ctx);
      for (const c of s.cases) walkStmts(c.body, scope, ctx);
      walkStmts(s.defaultBody, scope, ctx);
      return scope;
    case "forof": {
      walkExpr(s.iterable, scope, ctx);
      const inner = extend(scope, s.names.map((name, i) => ({ name, ty: s.nameTypes[i] ?? { kind: "unknown" } })));
      for (const inv of s.invariants) walkExpr(inv, inner, ctx);
      if (s.doneWith) walkExpr(s.doneWith, inner, ctx);
      walkStmts(s.body, inner, ctx);
      return scope;
    }
    case "someMatch":
      walkScrutinee(s.scrutinee, scope, ctx);
      walkStmts(s.someBody, withBinder(scope, s.binder, s.binderTy, s.scrutinee, ctx), ctx);
      walkStmts(s.noneBody, scope, ctx);
      return scope;
    case "tagMatch":
      walkExpr(s.scrutinee, scope, ctx);
      for (const c of s.cases) walkStmts(c.body, scope, ctx);
      walkStmts(s.fallthrough, scope, ctx);
      return scope;
  }
}

// ── Display ─────────────────────────────────────────────────

export function show(e: TExpr): string {
  switch (e.kind) {
    case "var": return e.name;
    case "num": return String(e.value);
    case "bigint": return `${e.value}n`;
    case "str": return JSON.stringify(e.value);
    case "bool": return String(e.value);
    case "binop": return `(${show(e.left)} ${e.op} ${show(e.right)})`;
    case "unop": return `${e.op}${show(e.expr)}`;
    case "call": return `${show(e.fn)}(${e.args.map(show).join(", ")})`;
    case "index": return `${show(e.obj)}[${show(e.idx)}]`;
    case "field": return `${show(e.obj)}.${e.field}`;
    case "conditional": return `(${show(e.cond)} ? ${show(e.then)} : ${show(e.else)})`;
    case "nullish": return `(${show(e.left)} ?? ${show(e.right)})`;
    case "someMatch": return `someMatch ${show(e.scrutinee)} { Some(${e.binder}) => ${show(e.someBody)}, None => ${show(e.noneBody)} }`;
    default: return `<${e.kind}>`;
  }
}
