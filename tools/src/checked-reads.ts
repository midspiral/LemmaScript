/**
 * Post-narrow checked-read insertion (`midspiral/LemmaScript#387`, Milestone 4 /
 * `robertpenner/LemmaScript#52`).
 *
 * After `narrow.ts`'s `someMatch` / `tagMatch` drivers run, any access path
 * that `resolve.ts` proved non-optional (via `&&`/`||` chains, `if ... else`,
 * `while` presence guards, or definite assignment narrowing) whose underlying
 * storage binding is still `Option<T>` is wrapped in an explicit
 * `{ kind: "checkedUnwrap", expr, ty }`.
 *
 * Lowering `checkedUnwrap` emits a backend-checked projection (`.value` in
 * Dafny, `.get (by grind)` in Lean) directly on the live storage variable,
 * without introducing match-binder copies, sequential `if i_branch0` splits,
 * or unnecessary `i_compareN` temporaries.
 */

import type { TExpr, TFunction, TModule, TStmt, Ty } from "./typedir.js";
import type { FieldInfo, TypeDeclInfo } from "./types.js";
import { parseTsType } from "./types.js";

const ARITH = new Set(["+", "-", "*", "/", "%", "**"]);

interface Scope {
  /** Storage types for variables and `someMatch`-bound paths. */
  types: Map<string, Ty>;
}

function pathKey(e: TExpr): string | null {
  if (e.kind === "var") return e.name;
  if (e.kind === "checkedUnwrap") return pathKey(e.expr);
  if (e.kind === "field") {
    const inner = pathKey(e.obj);
    return inner === null ? null : `${inner}.${e.field}`;
  }
  return null;
}

function isNullable(ty: Ty | null): ty is Extract<Ty, { kind: "optional" | "nullish" }> {
  return ty !== null && (ty.kind === "optional" || ty.kind === "nullish");
}

function fieldInfoTy(f: FieldInfo | null): Ty | null {
  if (!f) return null;
  const ty = f.type ?? parseTsType(f.tsType);
  if (!f.optionalKey) return ty;
  if (ty.kind === "nullish") return ty;
  if (ty.kind === "optional") {
    return ty.absent === "null" ? { kind: "nullish", inner: ty.inner } : ty;
  }
  return { kind: "optional", inner: ty };
}

function declField(decl: TypeDeclInfo, field: string, ofVariant: string | undefined): FieldInfo | null {
  if (decl.kind === "record") return decl.fields?.find(f => f.name === field) ?? null;
  if (decl.kind !== "discriminated-union" || !decl.variants) return null;
  const variants = ofVariant ? decl.variants.filter(v => v.name === ofVariant) : decl.variants;
  const found = variants.map(v => v.fields.find(f => f.name === field)).filter((f): f is FieldInfo => !!f);
  if (found.length === 0) return null;
  const nullable = found.map(f => isNullable(fieldInfoTy(f)));
  return nullable.every(o => o === nullable[0]) ? found[0]! : null;
}

function fieldStorageTy(ty: Ty, field: string, ofVariant: string | undefined, mod: TModule, depth = 0): Ty | null {
  if (depth > 8 || ty.kind !== "user") return null;
  const cls = mod.classes.find(c => c.name === ty.name);
  if (cls) return cls.fields.find(f => f.name === field)?.ty ?? null;
  const decl = mod.typeDecls.find(d => d.name === ty.name);
  if (!decl || (decl.typeParams && decl.typeParams.length > 0)) return null;
  if (decl.kind === "alias" && decl.aliasOfTy) {
    return fieldStorageTy(decl.aliasOfTy, field, ofVariant, mod, depth + 1);
  }
  return fieldInfoTy(declField(decl, field, ofVariant));
}

function storageTyOf(e: TExpr, scope: Scope, mod: TModule): Ty | null {
  if (e.kind === "checkedUnwrap") return e.ty;
  const key = pathKey(e);
  if (key !== null) {
    const bound = scope.types.get(key);
    if (bound) return bound;
  }
  if (e.kind !== "field") return null;
  const objTy = storageTyOf(e.obj, scope, mod);
  if (!objTy || objTy.kind === "optional" || objTy.kind === "nullish") return null;
  return fieldStorageTy(objTy, e.field, e.ofVariant, mod);
}

function extendScope(scope: Scope, names: { name: string; ty: Ty }[]): Scope {
  if (names.length === 0) return scope;
  const types = new Map(scope.types);
  for (const n of names) {
    types.set(n.name, n.ty);
    for (const k of [...types.keys()]) if (k.startsWith(`${n.name}.`)) types.delete(k);
  }
  return { types };
}

function enterSomeMatch(scope: Scope, scrutinee: TExpr, binder: string, binderTy: Ty): Scope {
  const types = new Map(scope.types);
  types.set(binder, binderTy);
  const key = pathKey(scrutinee);
  if (key !== null) types.set(key, binderTy);
  return { types };
}

function isDefinitelyUnwrappedStamp(ty: Ty): boolean {
  return !isNullable(ty) && ty.kind !== "unknown" && ty.kind !== "void" && ty.kind !== "null";
}

/** Rewrite an expression that is the direct operand of `===`/`!==`/`==`/`!=`
 *  with `undefined` or `null`: never wrap the operand itself in `checkedUnwrap`
 *  (restore its declared `Option<T>` or `Nullish<T>` storage type so
 *  `transform.ts` emits the right presence check), while still rewriting any
 *  optional/nullish receiver prefix. */
function rewritePresenceOperand(e: TExpr, scope: Scope, mod: TModule): TExpr {
  const storage = storageTyOf(e, scope, mod);
  if (e.kind === "var" && isNullable(storage)) {
    return { ...e, ty: storage };
  }
  if (e.kind === "field") {
    const obj = rewriteExpr(e.obj, scope, mod);
    const updated: TExpr = obj === e.obj ? e : { ...e, obj };
    const fStorage = storageTyOf(updated, scope, mod);
    if (isNullable(fStorage)) return { ...updated, ty: fStorage };
    return updated;
  }
  return rewriteExpr(e, scope, mod);
}

function isNullishVar(e: TExpr): boolean {
  return e.kind === "var" && (e.name === "undefined" || e.name === "null");
}

function rewriteExpr(e: TExpr, scope: Scope, mod: TModule): TExpr {
  switch (e.kind) {
    case "var": {
      const storage = storageTyOf(e, scope, mod);
      if (isNullable(storage)) {
        if (isDefinitelyUnwrappedStamp(e.ty)) {
          return { kind: "checkedUnwrap", expr: { ...e, ty: storage }, ty: e.ty };
        }
        // Partially narrowed `fromNullish` value still lives in `Nullish<T>` storage.
        if (storage.kind === "nullish" && e.ty.kind === "optional" && e.ty.fromNullish) {
          return { ...e, ty: storage };
        }
      }
      return e;
    }
    case "num": case "bigint": case "str": case "bool": case "havoc":
      return e;
    case "checkedUnwrap":
      return { ...e, expr: rewriteExpr(e.expr, scope, mod) };
    case "field": {
      // Rewrite receiver first (so an optional/nullish receiver `box` becomes `checkedUnwrap(box)`).
      const obj = rewriteExpr(e.obj, scope, mod);
      const updated: TExpr = obj === e.obj ? e : { ...e, obj };
      // Check if this field itself is optional/nullish by declaration (or bound in scope) while stamped non-nullable.
      const storage = storageTyOf(updated, scope, mod);
      if (isNullable(storage)) {
        if (isDefinitelyUnwrappedStamp(updated.ty)) {
          return { kind: "checkedUnwrap", expr: { ...updated, ty: storage }, ty: updated.ty };
        }
        if (storage.kind === "nullish" && updated.ty.kind === "optional" && updated.ty.fromNullish) {
          return { ...updated, ty: storage };
        }
      }
      return updated;
    }
    case "index":
      return { ...e, obj: rewriteExpr(e.obj, scope, mod), idx: rewriteExpr(e.idx, scope, mod) };
    case "binop": {
      let left: TExpr;
      let right: TExpr;
      if (["===", "!==", "==", "!="].includes(e.op) && (isNullishVar(e.left) || isNullishVar(e.right))) {
        left = isNullishVar(e.right) ? rewritePresenceOperand(e.left, scope, mod) : rewriteExpr(e.left, scope, mod);
        right = isNullishVar(e.left) ? rewritePresenceOperand(e.right, scope, mod) : rewriteExpr(e.right, scope, mod);
      } else {
        left = rewriteExpr(e.left, scope, mod);
        right = rewriteExpr(e.right, scope, mod);
      }
      let ty = e.ty;
      // Clear stale optional/nullish arithmetic stamp once operands are unwrapped.
      if (ARITH.has(e.op) && isNullable(ty) && !isNullable(left.ty) && !isNullable(right.ty)) {
        ty = left.ty;
      }
      return { ...e, left, right, ty };
    }
    case "unop": {
      const expr = rewriteExpr(e.expr, scope, mod);
      let ty = e.ty;
      if (e.op === "-" && isNullable(ty) && !isNullable(expr.ty)) ty = expr.ty;
      return { ...e, expr, ty };
    }
    case "call":
      return {
        ...e,
        fn: rewriteExpr(e.fn, scope, mod),
        args: e.args.map(a => rewriteExpr(a, scope, mod)),
      };
    case "record":
      return {
        ...e,
        spread: e.spread ? rewriteExpr(e.spread, scope, mod) : null,
        fields: e.fields.map(f => ({ ...f, value: rewriteExpr(f.value, scope, mod) })),
      };
    case "arrayLiteral":
      return { ...e, elems: e.elems.map(el => rewriteExpr(el, scope, mod)) };
    case "lambda": {
      const inner = extendScope(scope, e.params.map(p => ({ name: p.name, ty: p.ty })));
      return { ...e, body: rewriteStmts(e.body, inner, mod) };
    }
    case "conditional":
      return {
        ...e,
        cond: rewriteExpr(e.cond, scope, mod),
        then: rewriteExpr(e.then, scope, mod),
        else: rewriteExpr(e.else, scope, mod),
      };
    case "optChain":
      return {
        ...e,
        obj: rewriteExpr(e.obj, scope, mod),
        chain: e.chain.map(st =>
          st.kind === "call"
            ? { ...st, args: st.args.map(a => rewriteExpr(a, scope, mod)) }
            : st.kind === "index"
              ? { ...st, idx: rewriteExpr(st.idx, scope, mod) }
              : st,
        ),
      };
    case "nullish":
      return { ...e, left: rewriteExpr(e.left, scope, mod), right: rewriteExpr(e.right, scope, mod) };
    case "someMatch": {
      // Do NOT unwrap the scrutinee itself (it is supposed to remain Option<T>),
      // but DO rewrite any optional prefix inside a nested scrutinee (e.g. `box.inner`).
      const scrutinee = e.scrutinee.kind === "field"
        ? { ...e.scrutinee, obj: rewriteExpr(e.scrutinee.obj, scope, mod) }
        : e.scrutinee;
      const someScope = enterSomeMatch(scope, e.scrutinee, e.binder, e.binderTy);
      return {
        ...e,
        scrutinee,
        someBody: rewriteExpr(e.someBody, someScope, mod),
        noneBody: rewriteExpr(e.noneBody, scope, mod),
      };
    }
    case "tagMatch":
      return {
        ...e,
        scrutinee: rewriteExpr(e.scrutinee, scope, mod),
        cases: e.cases.map(c => ({ ...c, body: rewriteExpr(c.body, scope, mod) })),
        fallthrough: e.fallthrough ? rewriteExpr(e.fallthrough, scope, mod) : null,
      };
    case "forall":
    case "exists": {
      const inner = extendScope(scope, [{ name: e.var, ty: e.varTy }]);
      return { ...e, body: rewriteExpr(e.body, inner, mod) };
    }
  }
}

function rewriteStmts(stmts: TStmt[], scope: Scope, mod: TModule): TStmt[] {
  let cur = scope;
  const out: TStmt[] = [];
  for (const s of stmts) {
    switch (s.kind) {
      case "let": {
        const init = rewriteExpr(s.init, cur, mod);
        out.push({ ...s, init });
        cur = extendScope(cur, [{ name: s.name, ty: s.ty }]);
        break;
      }
      case "ghostLet": {
        const init = rewriteExpr(s.init, cur, mod);
        out.push({ ...s, init });
        cur = extendScope(cur, [{ name: s.name, ty: s.ty }]);
        break;
      }
      case "assign":
        out.push({ ...s, value: rewriteExpr(s.value, cur, mod) });
        break;
      case "ghostAssign":
        out.push({ ...s, value: rewriteExpr(s.value, cur, mod) });
        break;
      case "return":
        out.push({ ...s, value: rewriteExpr(s.value, cur, mod) });
        break;
      case "expr":
        out.push({ ...s, expr: rewriteExpr(s.expr, cur, mod) });
        break;
      case "assert":
        out.push({ ...s, expr: rewriteExpr(s.expr, cur, mod) });
        break;
      case "break":
      case "continue":
      case "throw":
        out.push(s);
        break;
      case "if":
        out.push({
          ...s,
          cond: rewriteExpr(s.cond, cur, mod),
          then: rewriteStmts(s.then, cur, mod),
          else: rewriteStmts(s.else, cur, mod),
        });
        break;
      case "while":
        out.push({
          ...s,
          cond: rewriteExpr(s.cond, cur, mod),
          invariants: s.invariants.map(inv => rewriteExpr(inv, cur, mod)),
          decreases: s.decreases ? rewriteExpr(s.decreases, cur, mod) : null,
          doneWith: s.doneWith ? rewriteExpr(s.doneWith, cur, mod) : null,
          body: rewriteStmts(s.body, cur, mod),
        });
        break;
      case "forof": {
        const iterable = rewriteExpr(s.iterable, cur, mod);
        const loopScope = extendScope(cur, [
          ...s.names.map((n, i) => ({ name: n, ty: s.nameTypes[i] ?? ({ kind: "unknown" } as Ty) })),
          { name: s.idx, ty: { kind: "nat" } },
        ]);
        out.push({
          ...s,
          iterable,
          invariants: s.invariants.map(inv => rewriteExpr(inv, loopScope, mod)),
          doneWith: s.doneWith ? rewriteExpr(s.doneWith, loopScope, mod) : null,
          body: rewriteStmts(s.body, loopScope, mod),
        });
        break;
      }
      case "switch":
        out.push({
          ...s,
          expr: rewriteExpr(s.expr, cur, mod),
          cases: s.cases.map(c => ({ ...c, body: rewriteStmts(c.body, cur, mod) })),
          defaultBody: rewriteStmts(s.defaultBody, cur, mod),
        });
        break;
      case "someMatch": {
        const scrutinee = s.scrutinee.kind === "field"
          ? { ...s.scrutinee, obj: rewriteExpr(s.scrutinee.obj, cur, mod) }
          : s.scrutinee;
        const someScope = enterSomeMatch(cur, s.scrutinee, s.binder, s.binderTy);
        out.push({
          ...s,
          scrutinee,
          someBody: rewriteStmts(s.someBody, someScope, mod),
          noneBody: rewriteStmts(s.noneBody, cur, mod),
        });
        break;
      }
      case "tagMatch":
        out.push({
          ...s,
          scrutinee: rewriteExpr(s.scrutinee, cur, mod),
          cases: s.cases.map(c => ({ ...c, body: rewriteStmts(c.body, cur, mod) })),
          fallthrough: rewriteStmts(s.fallthrough, cur, mod),
        });
        break;
    }
  }
  return out;
}

function rewriteFunction(fn: TFunction, className: string | null, globals: Map<string, Ty>, mod: TModule): TFunction {
  const types = new Map(globals);
  for (const p of fn.params) types.set(p.name, p.ty);
  if (className !== null) types.set("this", { kind: "user", name: className });
  const scope: Scope = { types };
  const postTypes = new Map(types);
  postTypes.set("\\result", fn.returnTy);
  const postScope: Scope = { types: postTypes };

  return {
    ...fn,
    requires: fn.requires.map(r => rewriteExpr(r, scope, mod)),
    decreases: fn.decreases ? rewriteExpr(fn.decreases, scope, mod) : null,
    ensures: fn.ensures.map(e => rewriteExpr(e, postScope, mod)),
    body: rewriteStmts(fn.body, scope, mod),
  };
}

/** Reconcile any narrowed-but-not-someMatch-bound optional reads by inserting
 *  explicit `checkedUnwrap` nodes. */
export function insertCheckedUnwraps(mod: TModule): TModule {
  const globals = new Map<string, Ty>();
  for (const c of mod.constants) globals.set(c.name, c.ty);

  return {
    ...mod,
    constants: mod.constants.map(c => ({
      ...c,
      value: rewriteExpr(c.value, { types: new Map(globals) }, mod),
    })),
    functions: mod.functions.map(fn => rewriteFunction(fn, null, globals, mod)),
    classes: mod.classes.map(cls => ({
      ...cls,
      methods: cls.methods.map(m => rewriteFunction(m, cls.name, globals, mod)),
    })),
  };
}
