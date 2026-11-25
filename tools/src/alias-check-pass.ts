/**
 * Intra-procedural live-alias mutation checker (`midspiral/LemmaScript#387`,
 * Milestone 3b / `robertpenner/LemmaScript#50`).
 *
 * Mirrors `NoLiveAliasAtTarget` in `formal/narrowing-model.dfy`:
 *   - Read-only aliases (`const b = a; return a.length + b.length`) are ALLOWED.
 *   - Dead-source moves (`const b = a; b.push(1); return b.length`) are ALLOWED.
 *   - Live-alias mutations (`const b = a; b.push(1); return a.length`) are
 *     REJECTED with a diagnostic naming both bindings.
 *
 * Uses the self-verified alias conflict kernel from `alias-check.ts`.
 */

import type { TExpr, TFunction, TModule, TStmt, Ty } from "./typedir.js";
import type { TypeDeclInfo } from "./types.js";
import { declOfTy } from "./typedecls.js";
import { isMutatingCollectionMethod } from "./place-lowering.js";
import { bindCopyGroup, bindFreshGroup, findLiveAliasConflict } from "./alias-check.js";

export interface LiveAliasConflict {
  fn: string;
  mutatedVar: string;
  liveAlias: string;
  detail: string;
}

type AliasMap = Map<string, number>;

interface AliasState {
  map: AliasMap;
  /** Variables whose *nested* mutable fields/elements share references with
   *  the listed ancestor variables via a shallow copy (`{ ...a, ... }`,
   *  `[...a]`, `new Map(m)`, `[a]`, `{ items: a.items }`). Top-level mutations
   *  on a shallow copy are safe in JS; nested mutations or extracting a nested
   *  mutable member alias the shallow parents. */
  shallowParents: Map<string, Set<string>>;
  nextId: number;
}

function cloneAliasState(s: AliasState): AliasState {
  const sp = new Map<string, Set<string>>();
  for (const [k, v] of s.shallowParents.entries()) sp.set(k, new Set(v));
  return { map: new Map(s.map), shallowParents: sp, nextId: s.nextId };
}

/** True for JS types whose values have mutable reference identity in JS
 *  (arrays, maps, sets, tuples, records, discriminated unions, and optionals
 *  wrapping them). Primitives and string-unions are immutable values. */
export function isMutableRefTy(ty: Ty, typeDecls: TypeDeclInfo[]): boolean {
  switch (ty.kind) {
    case "array":
    case "map":
    case "set":
    case "tuple":
      return true;
    case "optional":
      return isMutableRefTy(ty.inner, typeDecls);
    case "user": {
      const decl = declOfTy(typeDecls, ty);
      if (!decl) return false;
      if (decl.kind === "string-union" || decl.kind === "opaque") return false;
      if (decl.kind === "alias") return decl.aliasOfTy ? isMutableRefTy(decl.aliasOfTy, typeDecls) : false;
      return true; // record or discriminated-union
    }
    default:
      return false;
  }
}

/** True if values of `ty` contain nested mutable references (so a shallow copy
 *  such as `[...a]`, `new Map(m)`, or `{ ...obj }` still shares inner mutable
 *  objects with the source). */
function hasNestedMutableRef(ty: Ty, typeDecls: TypeDeclInfo[], seen = new Set<string>()): boolean {
  switch (ty.kind) {
    case "array":
    case "set":
      return isMutableRefTy(ty.elem, typeDecls);
    case "map":
      return isMutableRefTy(ty.value, typeDecls);
    case "tuple":
      return ty.elems.some(e => isMutableRefTy(e, typeDecls));
    case "optional":
      return hasNestedMutableRef(ty.inner, typeDecls, seen);
    case "user": {
      const decl = declOfTy(typeDecls, ty);
      if (!decl || seen.has(decl.name)) return false;
      seen.add(decl.name);
      if (decl.kind === "record" && decl.fields) {
        return decl.fields.some(f => f.type ? isMutableRefTy(f.type, typeDecls) : false);
      }
      if (decl.kind === "discriminated-union" && decl.variants) {
        return decl.variants.some(v => v.fields.some(f => f.type ? isMutableRefTy(f.type, typeDecls) : false));
      }
      if (decl.kind === "alias" && decl.aliasOfTy) {
        return hasNestedMutableRef(decl.aliasOfTy, typeDecls, seen);
      }
      return false;
    }
    default:
      return false;
  }
}

/** Root variable of a pure access path `x`, `x.a`, `x.a.b` (or null). */
function accessPathRoot(e: TExpr): string | null {
  if (e.kind === "var") return e.name;
  if (e.kind === "field") return accessPathRoot(e.obj);
  return null;
}

interface AliasSourceInfo {
  /** Direct same-object alias roots (e.g. `const b = a`, `const b = flag ? a : c`). */
  direct: string[];
  /** Shallow-copy parent roots whose nested mutable members are shared
   *  (e.g. `const b = { ...a, count: 2 }`, `const b = [...matrix]`, `const m2 = new Map(m)`). */
  shallow: string[];
  /** True when reading a nested mutable member from a base expression (e.g. `b[0]`, `b.items`, `m2.get(k)`),
   *  which promotes `b`'s `shallowParents` into the result's direct aliases! */
  derefBases: string[];
}

function mergeSourceInfo(parts: AliasSourceInfo[]): AliasSourceInfo {
  const direct = new Set<string>();
  const shallow = new Set<string>();
  const derefBases = new Set<string>();
  for (const p of parts) {
    for (const v of p.direct) direct.add(v);
    for (const v of p.shallow) shallow.add(v);
    for (const v of p.derefBases) derefBases.add(v);
  }
  return { direct: [...direct], shallow: [...shallow], derefBases: [...derefBases] };
}

/** Collect all direct and shallow-copy alias sources of `e` (handling
 *  conditionals, `??`, `?.`, `||`/`&&`, `record`, `arrayLiteral`, `m.get`,
 *  `m.values()`, `m.entries()`, and `freshClone` shallow clones). */
function aliasSourceInfo(e: TExpr, typeDecls: TypeDeclInfo[], allowNonMutableWrap = false): AliasSourceInfo {
  const empty: AliasSourceInfo = { direct: [], shallow: [], derefBases: [] };
  if (!allowNonMutableWrap && !isMutableRefTy(e.ty, typeDecls)) return empty;

  const isClone = "freshClone" in e && !!e.freshClone;
  if (isClone) {
    // Explicit JS shallow clone (`[...a]`, `new Map(m)`, `new Set(s)`, `{ ...a }`):
    // Top-level object is fresh (no direct alias!), but if the cloned container
    // holds nested mutable references, record its underlying roots as `shallow`.
    if (!hasNestedMutableRef(e.ty, typeDecls)) return empty;
    const inner = aliasSourceInfo({ ...e, freshClone: undefined } as TExpr, typeDecls, true);
    return {
      direct: [],
      shallow: [...new Set([...inner.direct, ...inner.shallow, ...inner.derefBases])],
      derefBases: [],
    };
  }

  switch (e.kind) {
    case "var":
      return e.name === "undefined" || e.name === "null"
        ? empty
        : { direct: [e.name], shallow: [], derefBases: [] };
    case "field": {
      const base = aliasSourceInfo(e.obj, typeDecls, true);
      const root = accessPathRoot(e.obj);
      const derefs = root ? [root, ...base.derefBases] : base.derefBases;
      return { direct: [...base.direct], shallow: [...base.shallow], derefBases: [...new Set(derefs)] };
    }
    case "index": {
      const base = aliasSourceInfo(e.obj, typeDecls, true);
      const root = accessPathRoot(e.obj);
      const derefs = root ? [root, ...base.derefBases] : base.derefBases;
      return { direct: [...base.direct], shallow: [...base.shallow], derefBases: [...new Set(derefs)] };
    }
    case "call":
      if (e.fn.kind === "field") {
        const m = e.fn.field;
        const objTy = e.fn.obj.ty.kind;
        if (
          (objTy === "map" && (m === "get" || m === "values" || m === "entries")) ||
          ((objTy === "set" || objTy === "array") && (m === "values" || m === "entries"))
        ) {
          const base = aliasSourceInfo(e.fn.obj, typeDecls, true);
          const root = accessPathRoot(e.fn.obj);
          const derefs = root ? [root, ...base.derefBases] : base.derefBases;
          return { direct: [...base.direct], shallow: [...base.shallow], derefBases: [...new Set(derefs)] };
        }
      }
      return empty;
    case "conditional":
      return mergeSourceInfo([
        aliasSourceInfo(e.then, typeDecls),
        aliasSourceInfo(e.else, typeDecls),
      ]);
    case "nullish":
      return mergeSourceInfo([
        aliasSourceInfo(e.left, typeDecls),
        aliasSourceInfo(e.right, typeDecls),
      ]);
    case "optChain": {
      const base = aliasSourceInfo(e.obj, typeDecls, true);
      const root = accessPathRoot(e.obj);
      const derefs = root ? [root, ...base.derefBases] : base.derefBases;
      return { direct: [...base.direct], shallow: [...base.shallow], derefBases: [...new Set(derefs)] };
    }
    case "binop":
      if (e.op === "||" || e.op === "&&") {
        return mergeSourceInfo([
          aliasSourceInfo(e.left, typeDecls),
          aliasSourceInfo(e.right, typeDecls),
        ]);
      }
      return empty;
    case "record": {
      // A record literal / spread `{ ...a, count: 2 }` or `{ items: a.items }` allocates a
      // fresh outer object, so it has no `direct` alias, but its spread and mutable-ref field
      // values share nested references -> record them in `shallow`.
      const shallow = new Set<string>();
      if (e.spread && hasNestedMutableRef(e.ty, typeDecls)) {
        const sp = aliasSourceInfo(e.spread, typeDecls, true);
        for (const v of [...sp.direct, ...sp.shallow, ...sp.derefBases]) shallow.add(v);
      }
      for (const f of e.fields) {
        if (isMutableRefTy(f.value.ty, typeDecls)) {
          const fi = aliasSourceInfo(f.value, typeDecls, true);
          for (const v of [...fi.direct, ...fi.shallow, ...fi.derefBases]) shallow.add(v);
        }
      }
      return { direct: [], shallow: [...shallow], derefBases: [] };
    }
    case "arrayLiteral": {
      // `[a, b]` allocates a fresh outer array; any mutable-ref elements are shared -> `shallow`.
      const shallow = new Set<string>();
      for (const el of e.elems) {
        if (isMutableRefTy(el.ty, typeDecls)) {
          const ei = aliasSourceInfo(el, typeDecls, true);
          for (const v of [...ei.direct, ...ei.shallow, ...ei.derefBases]) shallow.add(v);
        }
      }
      return { direct: [], shallow: [...shallow], derefBases: [] };
    }
    case "someMatch":
      return mergeSourceInfo([
        aliasSourceInfo(e.someBody, typeDecls),
        aliasSourceInfo(e.noneBody, typeDecls),
      ]);
    default:
      return empty;
  }
}

// ── Free variable collection ────────────────────────────────

function collectFreeVarsExpr(e: TExpr, out: Set<string>): void {
  switch (e.kind) {
    case "var":
      if (e.name !== "undefined" && e.name !== "null" && e.name !== "\\result") out.add(e.name);
      return;
    case "num": case "bigint": case "str": case "bool": case "havoc":
      return;
    case "binop":
      collectFreeVarsExpr(e.left, out);
      collectFreeVarsExpr(e.right, out);
      return;
    case "unop":
      collectFreeVarsExpr(e.expr, out);
      return;
    case "call":
      collectFreeVarsExpr(e.fn, out);
      for (const a of e.args) collectFreeVarsExpr(a, out);
      return;
    case "index":
      collectFreeVarsExpr(e.obj, out);
      collectFreeVarsExpr(e.idx, out);
      return;
    case "field":
      collectFreeVarsExpr(e.obj, out);
      return;
    case "record":
      if (e.spread) collectFreeVarsExpr(e.spread, out);
      for (const f of e.fields) collectFreeVarsExpr(f.value, out);
      return;
    case "arrayLiteral":
      for (const el of e.elems) collectFreeVarsExpr(el, out);
      return;
    case "lambda": {
      const inner = liveBeforeStmts(e.body, new Set(), new Set(), new Set(), new Set());
      for (const p of e.params) inner.delete(p.name);
      for (const v of inner) out.add(v);
      return;
    }
    case "conditional":
      collectFreeVarsExpr(e.cond, out);
      collectFreeVarsExpr(e.then, out);
      collectFreeVarsExpr(e.else, out);
      return;
    case "optChain":
      collectFreeVarsExpr(e.obj, out);
      for (const step of e.chain) {
        if (step.kind === "call") for (const a of step.args) collectFreeVarsExpr(a, out);
        else if (step.kind === "index") collectFreeVarsExpr(step.idx, out);
      }
      return;
    case "nullish":
      collectFreeVarsExpr(e.left, out);
      collectFreeVarsExpr(e.right, out);
      return;
    case "someMatch":
      collectFreeVarsExpr(e.scrutinee, out);
      {
        const sb = new Set<string>();
        collectFreeVarsExpr(e.someBody, sb);
        sb.delete(e.binder);
        for (const v of sb) out.add(v);
      }
      collectFreeVarsExpr(e.noneBody, out);
      return;
    case "tagMatch":
      collectFreeVarsExpr(e.scrutinee, out);
      for (const c of e.cases) collectFreeVarsExpr(c.body, out);
      if (e.fallthrough) collectFreeVarsExpr(e.fallthrough, out);
      return;
    case "forall":
    case "exists": {
      const inner = new Set<string>();
      collectFreeVarsExpr(e.body, inner);
      inner.delete(e.var);
      for (const v of inner) out.add(v);
      return;
    }
  }
}

function freeVarsExpr(e: TExpr): Set<string> {
  const s = new Set<string>();
  collectFreeVarsExpr(e, s);
  return s;
}

function unionSets(...sets: ReadonlySet<string>[]): Set<string> {
  const out = new Set<string>();
  for (const s of sets) for (const v of s) out.add(v);
  return out;
}

function setsEqual(a: ReadonlySet<string>, b: ReadonlySet<string>): boolean {
  if (a.size !== b.size) return false;
  for (const v of a) if (!b.has(v)) return false;
  return true;
}

// ── In-place mutation target detection ──────────────────────

interface MutationInfo {
  root: string;
  /** True when the mutation modifies a *nested* member of `root` (e.g.
   *  `b.items.push(99)`, `m.get(k)?.push(99)`, `b.a.x = 1`) rather than the
   *  top-level container `root` itself (`b.count = 5`, `m.set(k, v)`, `a.push(1)`). */
  nested: boolean;
}

/** If statement `s` mutates a storage variable in place (rather than merely
 *  rebinding a local variable to a fresh object), return `{ root, nested }`. */
function mutationInfoOfStmt(s: TStmt): MutationInfo | null {
  if (s.kind === "expr") {
    const e = s.expr;
    if (e.kind === "call" && e.fn.kind === "field" && (
      isMutatingCollectionMethod(e.fn.obj.ty, e.fn.field) ||
      (e.fn.obj.ty.kind === "unknown" && ["push", "unshift", "sort", "set", "add", "delete"].includes(e.fn.field))
    )) {
      const root = accessPathRoot(e.fn.obj);
      if (!root) return null;
      return { root, nested: e.fn.obj.kind === "field" };
    }
    // Optional chaining mutation before narrow: `m.get(k)?.push(v)` or `b?.items?.push(v)` or `arr?.push(v)`
    if (e.kind === "optChain" && e.chain.length >= 2) {
      const last = e.chain[e.chain.length - 1]!;
      const prev = e.chain[e.chain.length - 2]!;
      if (last.kind === "call" && prev.kind === "field") {
        const method = prev.name;
        if (["push", "unshift", "sort", "set", "add", "delete"].includes(method)) {
          if (e.obj.kind === "call" && e.obj.fn.kind === "field" && e.obj.fn.field === "get") {
            const root = accessPathRoot(e.obj.fn.obj);
            return root ? { root, nested: true } : null;
          }
          const root = accessPathRoot(e.obj);
          const nested = e.obj.kind === "field" || e.chain.length > 2;
          return root ? { root, nested } : null;
        }
      }
    }
    // Post-narrow `m.get(k)?.push(v)` lowered to expression `someMatch`
    if (e.kind === "someMatch" &&
        e.scrutinee.kind === "call" && e.scrutinee.fn.kind === "field" &&
        e.scrutinee.fn.field === "get" && e.scrutinee.fn.obj.ty.kind === "map" &&
        e.someBody.kind === "call" && e.someBody.fn.kind === "field" &&
        ["push", "unshift", "sort", "set", "add", "delete"].includes(e.someBody.fn.field)) {
      const root = accessPathRoot(e.scrutinee.fn.obj);
      return root ? { root, nested: true } : null;
    }
    return null;
  }
  if (s.kind === "let" && s.init.kind === "call" && s.init.fn.kind === "field" &&
      (s.init.fn.field === "pop" || s.init.fn.field === "shift") && s.init.fn.obj.ty.kind === "array") {
    const root = accessPathRoot(s.init.fn.obj);
    return root ? { root, nested: s.init.fn.obj.kind === "field" } : null;
  }
  if (s.kind === "assign") {
    if (s.value.kind === "call" && s.value.fn.kind === "field" &&
        (s.value.fn.field === "pop" || s.value.fn.field === "shift") && s.value.fn.obj.ty.kind === "array") {
      const root = accessPathRoot(s.value.fn.obj);
      return root ? { root, nested: s.value.fn.obj.kind === "field" } : null;
    }
    // Dotted field assignment (`b.count = ...` -> top-level field of `b`; `b.a.x = ...` -> nested).
    if (s.target.includes(".")) {
      const parts = s.target.split(".");
      const root = parts[0]!;
      return { root, nested: parts.length > 2 };
    }
    // Array index assignment (`arr[i] = v` desugared to `arr = arr.with(i, v)`): mutates `arr` in place.
    if (s.value.kind === "call" && s.value.fn.kind === "field" && s.value.fn.field === "with" &&
        s.value.fn.obj.kind === "var" && s.value.fn.obj.name === s.target) {
      return { root: s.target, nested: false };
    }
    return null;
  }
  return null;
}

// ── Backward liveness analysis (with explicit break/continue targets) ──

function liveBeforeStmt(
  s: TStmt,
  liveAfter: ReadonlySet<string>,
  ensuresVars: ReadonlySet<string>,
  breakLive: ReadonlySet<string>,
  continueLive: ReadonlySet<string>,
): Set<string> {
  switch (s.kind) {
    case "return":
      return unionSets(freeVarsExpr(s.value), ensuresVars);
    case "throw":
      return new Set();
    case "break":
      return new Set(breakLive);
    case "continue":
      return new Set(continueLive);
    case "let": {
      const next = new Set(liveAfter);
      next.delete(s.name);
      return unionSets(next, freeVarsExpr(s.init));
    }
    case "ghostLet": {
      const next = new Set(liveAfter);
      next.delete(s.name);
      return unionSets(next, freeVarsExpr(s.init));
    }
    case "assign": {
      const mut = mutationInfoOfStmt(s);
      const next = new Set(liveAfter);
      if (mut) {
        next.add(mut.root);
      } else if (!s.target.includes(".")) {
        next.delete(s.target);
      }
      return unionSets(next, freeVarsExpr(s.value));
    }
    case "ghostAssign": {
      const next = new Set(liveAfter);
      next.delete(s.target);
      return unionSets(next, freeVarsExpr(s.value));
    }
    case "expr":
      return unionSets(liveAfter, freeVarsExpr(s.expr));
    case "assert":
      return unionSets(liveAfter, freeVarsExpr(s.expr));
    case "if":
      return unionSets(
        freeVarsExpr(s.cond),
        liveBeforeStmts(s.then, liveAfter, ensuresVars, breakLive, continueLive),
        liveBeforeStmts(s.else, liveAfter, ensuresVars, breakLive, continueLive),
      );
    case "someMatch": {
      const someLive = liveBeforeStmts(s.someBody, liveAfter, ensuresVars, breakLive, continueLive);
      someLive.delete(s.binder);
      return unionSets(
        freeVarsExpr(s.scrutinee),
        someLive,
        liveBeforeStmts(s.noneBody, liveAfter, ensuresVars, breakLive, continueLive),
      );
    }
    case "tagMatch": {
      const parts: Set<string>[] = [
        freeVarsExpr(s.scrutinee),
        liveBeforeStmts(s.fallthrough, liveAfter, ensuresVars, breakLive, continueLive),
      ];
      for (const c of s.cases) parts.push(liveBeforeStmts(c.body, liveAfter, ensuresVars, breakLive, continueLive));
      return unionSets(...parts);
    }
    case "switch": {
      const parts: Set<string>[] = [
        freeVarsExpr(s.expr),
        liveBeforeStmts(s.defaultBody, liveAfter, ensuresVars, liveAfter, continueLive),
      ];
      for (const c of s.cases) parts.push(liveBeforeStmts(c.body, liveAfter, ensuresVars, liveAfter, continueLive));
      return unionSets(...parts);
    }
    case "while": {
      const headVars = unionSets(
        freeVarsExpr(s.cond),
        ...s.invariants.map(freeVarsExpr),
        ...(s.decreases ? [freeVarsExpr(s.decreases)] : []),
        ...(s.doneWith ? [freeVarsExpr(s.doneWith)] : []),
      );
      let loopLive = unionSets(liveAfter, headVars);
      for (let iter = 0; iter < 32; iter++) {
        const next = unionSets(loopLive, liveBeforeStmts(s.body, loopLive, ensuresVars, liveAfter, loopLive));
        if (setsEqual(next, loopLive)) break;
        loopLive = next;
      }
      return loopLive;
    }
    case "forof": {
      const headVars = unionSets(
        freeVarsExpr(s.iterable),
        ...s.invariants.map(freeVarsExpr),
        ...(s.doneWith ? [freeVarsExpr(s.doneWith)] : []),
      );
      let loopLive = unionSets(liveAfter, headVars);
      for (let iter = 0; iter < 32; iter++) {
        const bodyLive = liveBeforeStmts(s.body, loopLive, ensuresVars, liveAfter, loopLive);
        for (const n of s.names) bodyLive.delete(n);
        bodyLive.delete(s.idx);
        const next = unionSets(loopLive, bodyLive);
        if (setsEqual(next, loopLive)) break;
        loopLive = next;
      }
      return loopLive;
    }
  }
}

function liveBeforeStmts(
  stmts: readonly TStmt[],
  liveAfter: ReadonlySet<string>,
  ensuresVars: ReadonlySet<string>,
  breakLive: ReadonlySet<string>,
  continueLive: ReadonlySet<string>,
): Set<string> {
  let cur = new Set(liveAfter);
  for (let i = stmts.length - 1; i >= 0; i--) {
    cur = liveBeforeStmt(stmts[i]!, cur, ensuresVars, breakLive, continueLive);
  }
  return cur;
}

/** Precompute `liveAfter[i]` for every statement `stmts[i]`. */
function computeStmtLiveAfter(
  stmts: readonly TStmt[],
  liveAfterBlock: ReadonlySet<string>,
  ensuresVars: ReadonlySet<string>,
  breakLive: ReadonlySet<string>,
  continueLive: ReadonlySet<string>,
): Set<string>[] {
  const result: Set<string>[] = new Array(stmts.length);
  let cur = new Set(liveAfterBlock);
  for (let i = stmts.length - 1; i >= 0; i--) {
    result[i] = cur;
    cur = liveBeforeStmt(stmts[i]!, cur, ensuresVars, breakLive, continueLive);
  }
  return result;
}

// ── Conservative alias-map + shallowParents join ────────────

function uniteGroups(map: AliasMap, vars: string[]): AliasMap {
  const present = vars.filter(v => map.has(v));
  if (present.length < 2) return map;
  const targetGroup = map.get(present[0]!)!;
  const groupsToMerge = new Set(present.map(v => map.get(v)!));
  const next = new Map(map);
  for (const [k, g] of next.entries()) {
    if (groupsToMerge.has(g)) next.set(k, targetGroup);
  }
  return next;
}

function joinAliasStates(states: AliasState[]): AliasState {
  if (states.length === 0) return { map: new Map(), shallowParents: new Map(), nextId: 0 };
  if (states.length === 1) return cloneAliasState(states[0]!);

  const allVars = new Set<string>();
  let nextId = 0;
  for (const st of states) {
    if (st.nextId > nextId) nextId = st.nextId;
    for (const k of st.map.keys()) allVars.add(k);
  }

  const parent = new Map<string, string>();
  for (const v of allVars) parent.set(v, v);
  const find = (x: string): string => {
    let r = x;
    while (parent.get(r)! !== r) r = parent.get(r)!;
    let cur = x;
    while (cur !== r) {
      const p = parent.get(cur)!;
      parent.set(cur, r);
      cur = p;
    }
    return r;
  };
  const unite = (a: string, b: string): void => {
    const ra = find(a);
    const rb = find(b);
    if (ra !== rb) parent.set(ra, rb);
  };

  for (const st of states) {
    const byGroup = new Map<number, string>();
    for (const [v, g] of st.map.entries()) {
      const rep = byGroup.get(g);
      if (rep !== undefined) unite(rep, v);
      else byGroup.set(g, v);
    }
  }

  const rootToId = new Map<string, number>();
  const joined: AliasMap = new Map();
  for (const v of allVars) {
    const r = find(v);
    let id = rootToId.get(r);
    if (id === undefined) {
      id = nextId++;
      rootToId.set(r, id);
    }
    joined.set(v, id);
  }

  const shallowParents = new Map<string, Set<string>>();
  for (const st of states) {
    for (const [k, ps] of st.shallowParents.entries()) {
      let dst = shallowParents.get(k);
      if (!dst) {
        dst = new Set();
        shallowParents.set(k, dst);
      }
      for (const p of ps) dst.add(p);
    }
  }

  return { map: joined, shallowParents, nextId };
}

function aliasStatesEqual(a: AliasState, b: AliasState): boolean {
  if (a.map.size !== b.map.size) return false;
  for (const [k1, g1] of a.map.entries()) {
    if (!b.map.has(k1)) return false;
    const b1 = b.map.get(k1)!;
    for (const [k2, g2] of a.map.entries()) {
      if ((g1 === g2) !== (b1 === b.map.get(k2)!)) return false;
    }
  }
  if (a.shallowParents.size !== b.shallowParents.size) return false;
  for (const [k, s1] of a.shallowParents.entries()) {
    const s2 = b.shallowParents.get(k);
    if (!s2 || !setsEqual(s1, s2)) return false;
  }
  return true;
}

/** Apply binding `dst = initExpr` to `state`, updating both direct alias
 *  equivalence classes and `shallowParents` (including promoting `shallowParents`
 *  of dereferenced bases into direct aliases when extracting nested mutable members). */
function bindAliasFromExpr(
  state: AliasState,
  dst: string,
  srcInfo: AliasSourceInfo,
): AliasState {
  const next = cloneAliasState(state);
  // Start `dst` in a fresh group first (clears prior direct alias on reassignment).
  next.map = bindFreshGroup(next.map, dst, next.nextId);
  next.nextId += 1;
  next.shallowParents.delete(dst);

  // Collect all direct alias partners: explicit `direct` roots PLUS `shallowParents`
  // of any dereferenced base (e.g. `const row = b[0]` where `b` is a shallow copy of `a`
  // -> `row` directly aliases `a`'s inner element!).
  const directPartners = new Set<string>();
  for (const d of srcInfo.direct) {
    if (d !== dst && next.map.has(d)) directPartners.add(d);
  }
  for (const base of srcInfo.derefBases) {
    const sp = state.shallowParents.get(base);
    if (sp) {
      for (const p of sp) {
        if (p !== dst && next.map.has(p)) directPartners.add(p);
      }
    }
  }

  if (directPartners.size > 0) {
    const first = [...directPartners][0]!;
    next.map = bindCopyGroup(next.map, dst, first, next.nextId);
    next.nextId += 1;
    if (directPartners.size > 1) {
      next.map = uniteGroups(next.map, [dst, ...directPartners]);
    }
  }

  // Record shallow parents (including transitive shallow parents of any direct/shallow source).
  const newShallow = new Set<string>();
  for (const s of srcInfo.shallow) {
    if (s !== dst && next.map.has(s)) newShallow.add(s);
    const parentSp = state.shallowParents.get(s);
    if (parentSp) for (const p of parentSp) if (p !== dst && next.map.has(p)) newShallow.add(p);
  }
  for (const d of directPartners) {
    const parentSp = state.shallowParents.get(d);
    if (parentSp) for (const p of parentSp) if (p !== dst && next.map.has(p)) newShallow.add(p);
  }
  if (newShallow.size > 0) next.shallowParents.set(dst, newShallow);
  return next;
}

/** Find a live conflicting alias for `mutated` (checking direct alias group, and
 *  for nested mutations also checking `shallowParents` and any other variable
 *  whose `shallowParents` includes `mutated` or shares its direct group). */
function findConflictForMutation(
  mut: MutationInfo,
  state: AliasState,
  liveAfter: ReadonlySet<string>,
): string {
  const candidates = [...state.map.keys()];
  const direct = findLiveAliasConflict(mut.root, state.map, new Set(liveAfter), candidates);
  if (direct !== "") return direct;
  if (!mut.nested) return "";

  const mutGroup = state.map.get(mut.root);
  // Check shallow parents of `mut.root` (and anyone sharing their direct group).
  const sp = state.shallowParents.get(mut.root);
  if (sp) {
    for (const p of sp) {
      if (p !== mut.root && liveAfter.has(p)) return p;
      const pg = state.map.get(p);
      if (pg !== undefined) {
        for (const c of candidates) {
          if (c !== mut.root && liveAfter.has(c) && state.map.get(c) === pg) return c;
        }
      }
    }
  }
  // Symmetric check: another live variable `c` is a shallow copy of `mut.root` (or its group).
  for (const [c, cParents] of state.shallowParents.entries()) {
    if (c === mut.root || !liveAfter.has(c)) continue;
    for (const p of cParents) {
      if (p === mut.root || (mutGroup !== undefined && state.map.get(p) === mutGroup)) {
        return c;
      }
    }
  }
  return "";
}

// ── Forward alias analysis + live-conflict checking ─────────

interface CheckFlow {
  /** Normal fall-through state (`null` when the block terminated via return/throw/break/continue). */
  out: AliasState | null;
  breakStates: AliasState[];
  continueStates: AliasState[];
}

function checkLambdasInExpr(
  e: TExpr,
  state: AliasState,
  liveAfter: ReadonlySet<string>,
  ensuresVars: ReadonlySet<string>,
  typeDecls: TypeDeclInfo[],
  fnName: string,
  out: LiveAliasConflict[],
): void {
  switch (e.kind) {
    case "lambda": {
      let lamState = cloneAliasState(state);
      for (const p of e.params) {
        if (isMutableRefTy(p.ty, typeDecls)) {
          lamState.map = bindFreshGroup(lamState.map, p.name, lamState.nextId);
          lamState.nextId += 1;
          lamState.shallowParents.delete(p.name);
        }
      }
      // Captured variables remain observed by the enclosing scope after the callback returns.
      const lamLiveOut = unionSets(liveAfter, ensuresVars);
      for (const p of e.params) lamLiveOut.delete(p.name);
      checkStmts(e.body, lamState, lamLiveOut, lamLiveOut, new Set(), new Set(), typeDecls, fnName, out);
      return;
    }
    case "binop":
      checkLambdasInExpr(e.left, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      checkLambdasInExpr(e.right, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "unop":
      checkLambdasInExpr(e.expr, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "call":
      checkLambdasInExpr(e.fn, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      for (const a of e.args) checkLambdasInExpr(a, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "index":
      checkLambdasInExpr(e.obj, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      checkLambdasInExpr(e.idx, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "field":
      checkLambdasInExpr(e.obj, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "record":
      if (e.spread) checkLambdasInExpr(e.spread, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      for (const f of e.fields) checkLambdasInExpr(f.value, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "arrayLiteral":
      for (const el of e.elems) checkLambdasInExpr(el, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "conditional":
      checkLambdasInExpr(e.cond, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      checkLambdasInExpr(e.then, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      checkLambdasInExpr(e.else, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "optChain":
      checkLambdasInExpr(e.obj, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      for (const st of e.chain) {
        if (st.kind === "call") for (const a of st.args) checkLambdasInExpr(a, state, liveAfter, ensuresVars, typeDecls, fnName, out);
        else if (st.kind === "index") checkLambdasInExpr(st.idx, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      }
      return;
    case "nullish":
      checkLambdasInExpr(e.left, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      checkLambdasInExpr(e.right, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "someMatch":
      checkLambdasInExpr(e.scrutinee, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      checkLambdasInExpr(e.someBody, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      checkLambdasInExpr(e.noneBody, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    case "tagMatch":
      checkLambdasInExpr(e.scrutinee, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      for (const c of e.cases) checkLambdasInExpr(c.body, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      if (e.fallthrough) checkLambdasInExpr(e.fallthrough, state, liveAfter, ensuresVars, typeDecls, fnName, out);
      return;
    default:
      return;
  }
}

function checkStmts(
  stmts: readonly TStmt[],
  state: AliasState,
  liveAfterBlock: ReadonlySet<string>,
  ensuresVars: ReadonlySet<string>,
  breakLive: ReadonlySet<string>,
  continueLive: ReadonlySet<string>,
  typeDecls: TypeDeclInfo[],
  fnName: string,
  out: LiveAliasConflict[],
): CheckFlow {
  const liveAfterList = computeStmtLiveAfter(stmts, liveAfterBlock, ensuresVars, breakLive, continueLive);
  let cur: AliasState | null = cloneAliasState(state);
  const breakStates: AliasState[] = [];
  const continueStates: AliasState[] = [];

  for (let i = 0; i < stmts.length; i++) {
    if (!cur) break; // unreachable after return/throw/break/continue
    const s = stmts[i]!;
    const liveAfter = liveAfterList[i]!;

    // 1. Check any lambdas embedded in expressions of this statement.
    if (s.kind === "let" || s.kind === "ghostLet") {
      checkLambdasInExpr(s.init, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
    } else if (s.kind === "assign" || s.kind === "ghostAssign" || s.kind === "return") {
      checkLambdasInExpr(s.value, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
    } else if (s.kind === "expr" || s.kind === "assert") {
      checkLambdasInExpr(s.expr, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
    } else if (s.kind === "if") {
      checkLambdasInExpr(s.cond, cur, liveAfter, ensuresVars, typeDecls, fnName, out);
    }

    // 2. Check for live-alias conflict if this statement mutates a root in place.
    const mut = mutationInfoOfStmt(s);
    if (mut && cur.map.has(mut.root)) {
      const conflict = findConflictForMutation(mut, cur, liveAfter);
      if (conflict !== "") {
        out.push({
          fn: fnName,
          mutatedVar: mut.root,
          liveAlias: conflict,
          detail:
            `Live-alias mutation in \`${fnName}\`: mutating \`${mut.root}\` in place while alias ` +
            `\`${conflict}\` is still observed afterward. LemmaScript models arrays, maps, sets, ` +
            `and records as immutable values, so mutating \`${mut.root}\` would not update \`${conflict}\` ` +
            `(clone explicitly or mutate through a single live binding).`,
        });
      }
    }

    // 3. Advance alias state according to statement kind.
    switch (s.kind) {
      case "return":
      case "throw":
        cur = null;
        break;
      case "break":
        breakStates.push(cloneAliasState(cur));
        cur = null;
        break;
      case "continue":
        continueStates.push(cloneAliasState(cur));
        cur = null;
        break;
      case "let": {
        if (isMutableRefTy(s.ty, typeDecls)) {
          cur = bindAliasFromExpr(cur, s.name, aliasSourceInfo(s.init, typeDecls));
        }
        break;
      }
      case "assign": {
        if (!mut && !s.target.includes(".")) {
          if (isMutableRefTy(s.value.ty, typeDecls)) {
            cur = bindAliasFromExpr(cur, s.target, aliasSourceInfo(s.value, typeDecls));
          } else if (cur.map.has(s.target)) {
            const next = cloneAliasState(cur);
            next.map = bindFreshGroup(next.map, s.target, next.nextId);
            next.nextId += 1;
            next.shallowParents.delete(s.target);
            cur = next;
          }
        }
        break;
      }
      case "if": {
        const thenFlow = checkStmts(s.then, cur, liveAfter, ensuresVars, breakLive, continueLive, typeDecls, fnName, out);
        const elseFlow = checkStmts(s.else, cur, liveAfter, ensuresVars, breakLive, continueLive, typeDecls, fnName, out);
        breakStates.push(...thenFlow.breakStates, ...elseFlow.breakStates);
        continueStates.push(...thenFlow.continueStates, ...elseFlow.continueStates);
        const exits = [thenFlow.out, elseFlow.out].filter((x): x is AliasState => x !== null);
        cur = exits.length > 0 ? joinAliasStates(exits) : null;
        break;
      }
      case "someMatch": {
        const someFlow = checkStmts(s.someBody, cur, liveAfter, ensuresVars, breakLive, continueLive, typeDecls, fnName, out);
        const noneFlow = checkStmts(s.noneBody, cur, liveAfter, ensuresVars, breakLive, continueLive, typeDecls, fnName, out);
        breakStates.push(...someFlow.breakStates, ...noneFlow.breakStates);
        continueStates.push(...someFlow.continueStates, ...noneFlow.continueStates);
        const exits = [someFlow.out, noneFlow.out].filter((x): x is AliasState => x !== null);
        cur = exits.length > 0 ? joinAliasStates(exits) : null;
        break;
      }
      case "tagMatch": {
        const exits: AliasState[] = [];
        for (const c of s.cases) {
          const cf = checkStmts(c.body, cur, liveAfter, ensuresVars, breakLive, continueLive, typeDecls, fnName, out);
          if (cf.out) exits.push(cf.out);
          breakStates.push(...cf.breakStates);
          continueStates.push(...cf.continueStates);
        }
        const ff = checkStmts(s.fallthrough, cur, liveAfter, ensuresVars, breakLive, continueLive, typeDecls, fnName, out);
        if (ff.out) exits.push(ff.out);
        breakStates.push(...ff.breakStates);
        continueStates.push(...ff.continueStates);
        cur = exits.length > 0 ? joinAliasStates(exits) : null;
        break;
      }
      case "switch": {
        const exits: AliasState[] = [];
        for (const c of s.cases) {
          const cf = checkStmts(c.body, cur, liveAfter, ensuresVars, liveAfter, continueLive, typeDecls, fnName, out);
          if (cf.out) exits.push(cf.out);
          exits.push(...cf.breakStates); // switch catches `break`
          continueStates.push(...cf.continueStates);
        }
        const df = checkStmts(s.defaultBody, cur, liveAfter, ensuresVars, liveAfter, continueLive, typeDecls, fnName, out);
        if (df.out) exits.push(df.out);
        exits.push(...df.breakStates);
        continueStates.push(...df.continueStates);
        cur = exits.length > 0 ? joinAliasStates(exits) : null;
        break;
      }
      case "while": {
        const loopLiveAfter = liveBeforeStmt(s, liveAfter, ensuresVars, breakLive, continueLive);
        let loopIn = cur;
        for (let iter = 0; iter < 16; iter++) {
          const dummyOut: LiveAliasConflict[] = [];
          const bf = checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, liveAfter, loopLiveAfter, typeDecls, fnName, dummyOut);
          const backEdges: AliasState[] = [loopIn, ...bf.continueStates];
          if (bf.out) backEdges.push(bf.out);
          const merged = joinAliasStates(backEdges);
          if (aliasStatesEqual(merged, loopIn)) break;
          loopIn = merged;
        }
        const finalFlow = checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, liveAfter, loopLiveAfter, typeDecls, fnName, out);
        cur = joinAliasStates([loopIn, ...finalFlow.breakStates]);
        break;
      }
      case "forof": {
        const loopLiveAfter = liveBeforeStmt(s, liveAfter, ensuresVars, breakLive, continueLive);
        const iterInfo = aliasSourceInfo(s.iterable, typeDecls, true);
        const iterRoot = accessPathRoot(s.iterable);
        const elemInfo: AliasSourceInfo = {
          direct: iterInfo.direct,
          shallow: iterInfo.shallow,
          derefBases: [...new Set([...iterInfo.derefBases, ...(iterRoot ? [iterRoot] : [])])],
        };
        const iterContainerTy: Ty | null =
          s.iterable.kind === "call" && s.iterable.fn.kind === "field" &&
          (s.iterable.fn.field === "values" || s.iterable.fn.field === "entries")
            ? s.iterable.fn.obj.ty
            : s.iterable.ty;
        const iterYieldsMutable = iterContainerTy !== null && hasNestedMutableRef(iterContainerTy, typeDecls);
        let loopIn = cloneAliasState(cur);
        for (let idx = 0; idx < s.names.length; idx++) {
          const n = s.names[idx]!;
          const ty = s.nameTypes[idx];
          if ((ty && isMutableRefTy(ty, typeDecls)) || ((!ty || ty.kind === "unknown") && iterYieldsMutable)) {
            loopIn = bindAliasFromExpr(loopIn, n, elemInfo);
          }
        }
        for (let iter = 0; iter < 16; iter++) {
          const dummyOut: LiveAliasConflict[] = [];
          const bf = checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, liveAfter, loopLiveAfter, typeDecls, fnName, dummyOut);
          const backEdges: AliasState[] = [loopIn, ...bf.continueStates];
          if (bf.out) backEdges.push(bf.out);
          const merged = joinAliasStates(backEdges);
          if (aliasStatesEqual(merged, loopIn)) break;
          loopIn = merged;
        }
        const finalFlow = checkStmts(s.body, loopIn, loopLiveAfter, ensuresVars, liveAfter, loopLiveAfter, typeDecls, fnName, out);
        cur = joinAliasStates([loopIn, ...finalFlow.breakStates]);
        break;
      }
      default:
        break;
    }
  }
  return { out: cur, breakStates, continueStates };
}

function checkFunctionAliases(
  fn: TFunction,
  fnLabel: string,
  typeDecls: TypeDeclInfo[],
  out: LiveAliasConflict[],
  isClassMethod = false,
): void {
  let state: AliasState = { map: new Map(), shallowParents: new Map(), nextId: 1 };
  const paramNames = new Set<string>();
  if (isClassMethod) {
    state.map = bindFreshGroup(state.map, "this", state.nextId);
    state.nextId += 1;
  }
  for (const p of fn.params) {
    paramNames.add(p.name);
    if (isMutableRefTy(p.ty, typeDecls)) {
      state.map = bindFreshGroup(state.map, p.name, state.nextId);
      state.nextId += 1;
    }
  }
  // In Dafny/Lean, parameter mentions in `//@ ensures` refer to the entry
  // (pre-state) parameter value (e.g., `swap.ts`: `\result[i] === arr[j]`),
  // not a post-mutation executable read of `arr`. Keep non-parameter variables
  // (and `this` for class methods, where `this.field` in `ensures` is post-state).
  const ensuresVars = new Set<string>();
  for (const e of fn.ensures) {
    for (const v of freeVarsExpr(e)) {
      if (!paramNames.has(v)) ensuresVars.add(v);
    }
  }
  checkStmts(fn.body, state, ensuresVars, ensuresVars, new Set(), new Set(), typeDecls, fnLabel, out);
}

/** Check all functions and class methods in `mod` for live-alias mutations. */
export function checkModuleLiveAliases(mod: TModule): LiveAliasConflict[] {
  const out: LiveAliasConflict[] = [];
  for (const fn of mod.functions) {
    checkFunctionAliases(fn, fn.name, mod.typeDecls, out, false);
  }
  for (const cls of mod.classes ?? []) {
    for (const m of cls.methods) {
      checkFunctionAliases(m, `${cls.name}.${m.name}`, mod.typeDecls, out, true);
    }
  }
  return out;
}

/** Reject a module if any function mutates a mutable-ref binding while an alias is still live. */
export function assertNoLiveAliasMutations(mod: TModule): TModule {
  const conflicts = checkModuleLiveAliases(mod);
  if (conflicts.length > 0) {
    throw new Error(conflicts[0]!.detail);
  }
  return mod;
}
