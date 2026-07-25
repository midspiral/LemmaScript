/**
 * narrow — Structural-narrowing rewrite pass.
 *
 * Pipeline: resolve → narrow → transform → emit.
 *
 * Positional drivers over condition-facts (DESIGN_LS_IN_LS.md §4): the
 * *semantics* of conditions — what a check establishes, `&&`/`||`-chain
 * analysis, binder minting, discriminant detection — live in
 * `condition-facts.ts`; this pass owns *where* a condition sits (if
 * statement, early return + rest consumption, ternary, implication, guard
 * statement, conditional initializer, nullish/optional chains, discriminant
 * chains) and rewrites each position into `someMatch` / `tagMatch` IR via
 * the shared materializers.
 *
 * Following TS semantics, narrowing rules only fire for pure access paths
 * (`var(x)` or `field(purePath, name)`). Complex scrutinees (call results,
 * index ops) require bind-first: `const v = m.get(k); if (v !== undefined) ...`.
 * The `optChain` rule is the exception: narrow constructs the someBody to use the
 * binder directly, so any scrutinee shape is allowed.
 *
 * Transform lowers `someMatch` to IR `match` Some/None, substituting the
 * binder for path-shaped scrutinees via `replacePathInTExpr` /
 * `replacePathInTStmts`. Resolve runs before narrow and handles type narrowing
 * only (env extension, `narrowedPaths`). Narrow doesn't substitute on raw IR
 * — the body keeps its original expressions until transform.
 *
 * Walker shape: bottom-up over TExpr/TStmt. At each node, recurse children
 * via the *Recurse* helpers, then try the rules in order. List-level rules
 * (early-return, let-cond) run in `walkStmts` so they can consume the rest
 * of the block. Rule order matters — see the comments at the two dispatch
 * chains.
 *
 * State is explicit (§6.1): a `CondCtx` (type declarations + the next
 * optChain binder index) threads through the walk — every walker returns
 * its rewritten node plus the (possibly advanced) ctx, list walks are
 * state-threaded folds, and nothing is mutated (§6.2). Rules take the
 * recursed node and the post-recursion ctx; a rule that mints a binder or
 * re-walks a constructed node returns the advanced ctx, all others pass
 * it through.
 */

import type { TModule, TFunction, TConst, TClass, TStmt, TExpr,
  TChainStep, TRecordField, TExprCase, TStmtCase, TSwitchCase } from "./typedir.js";
import { isTerminatorKind } from "./typedir.js";
import { freshName } from "./names.js";
import { builtinPure } from "./builtins.js";
import {
  type CondCtx, type PresentFact, type NoneDetector, type IsArrayFact,
  presentFact, leadingPresent, leadingIsArray, flattenOr, noneDetector,
  binderHintFor, binderHintForMapAccess, freshOcBinder,
  applyChain, restoreDiscriminantFlag, arrayBoundsCond, exprEqual,
  isArrayFact, typeofStringFact, variantFact, negVariantFact,
  presentMatchStmts, presentMatchExpr,
} from "./condition-facts.js";

// ── Walkers ──────────────────────────────────────────────────

interface ExprOut { expr: TExpr; ctx: CondCtx }
interface ExprsOut { exprs: TExpr[]; ctx: CondCtx }
interface StmtOut { stmt: TStmt; ctx: CondCtx }
interface StmtsOut { stmts: TStmt[]; ctx: CondCtx }

function walkExpr(e: TExpr, ctx: CondCtx): ExprOut {
  const r = recurseExpr(e, ctx);
  return ruleNullish(r.expr, r.ctx) ?? ruleNullishIndex(r.expr, r.ctx) ?? ruleOptChainIndex(r.expr, r.ctx) ?? ruleOptChain(r.expr, r.ctx) ?? ruleImplOptional(r.expr, r.ctx) ?? ruleImplArrayIsArray(r.expr, r.ctx) ?? ruleConditionalArrayIsArray(r.expr, r.ctx) ?? ruleConditionalAndArrayIsArray(r.expr, r.ctx) ?? ruleConditionalAndOptional(r.expr, r.ctx) ?? ruleConditionalOptionalSimple(r.expr, r.ctx) ?? ruleConditionalInMap(r.expr, r.ctx) ?? ruleConditionalOptionalTruthy(r.expr, r.ctx) ?? r;
}

/** State-threaded fold of `walkExpr` over a list, left to right. */
function walkExprs(es: TExpr[], ctx: CondCtx): ExprsOut {
  if (es.length === 0) return { exprs: [], ctx };
  const head = walkExpr(es[0], ctx);
  const tail = walkExprs(es.slice(1), head.ctx);
  return { exprs: [head.expr].concat(tail.exprs), ctx: tail.ctx };
}

interface StepsOut { steps: TChainStep[]; ctx: CondCtx }

function walkChainSteps(steps: TChainStep[], ctx: CondCtx): StepsOut {
  if (steps.length === 0) return { steps: [], ctx };
  const s = steps[0];
  let step: TChainStep = s;
  let c = ctx;
  if (s.kind === "call") {
    const args = walkExprs(s.args, ctx);
    step = { ...s, args: args.exprs };
    c = args.ctx;
  } else if (s.kind === "index") {
    const idx = walkExpr(s.idx, ctx);
    step = { ...s, idx: idx.expr };
    c = idx.ctx;
  }
  const rest = walkChainSteps(steps.slice(1), c);
  return { steps: [step].concat(rest.steps), ctx: rest.ctx };
}

interface RecordFieldsOut { fields: TRecordField[]; ctx: CondCtx }

function walkRecordFields(fields: TRecordField[], ctx: CondCtx): RecordFieldsOut {
  if (fields.length === 0) return { fields: [], ctx };
  const v = walkExpr(fields[0].value, ctx);
  const rest = walkRecordFields(fields.slice(1), v.ctx);
  return { fields: [{ ...fields[0], value: v.expr }].concat(rest.fields), ctx: rest.ctx };
}

interface ExprCasesOut { cases: TExprCase[]; ctx: CondCtx }

function walkExprCases(cases: TExprCase[], ctx: CondCtx): ExprCasesOut {
  if (cases.length === 0) return { cases: [], ctx };
  const b = walkExpr(cases[0].body, ctx);
  const rest = walkExprCases(cases.slice(1), b.ctx);
  return { cases: [{ ...cases[0], body: b.expr }].concat(rest.cases), ctx: rest.ctx };
}

interface StmtCasesOut { cases: TStmtCase[]; ctx: CondCtx }

function walkStmtCases(cases: TStmtCase[], ctx: CondCtx): StmtCasesOut {
  if (cases.length === 0) return { cases: [], ctx };
  const b = walkStmts(cases[0].body, ctx);
  const rest = walkStmtCases(cases.slice(1), b.ctx);
  return { cases: [{ ...cases[0], body: b.stmts }].concat(rest.cases), ctx: rest.ctx };
}

interface SwitchCasesOut { cases: TSwitchCase[]; ctx: CondCtx }

function walkSwitchCases(cases: TSwitchCase[], ctx: CondCtx): SwitchCasesOut {
  if (cases.length === 0) return { cases: [], ctx };
  const b = walkStmts(cases[0].body, ctx);
  const rest = walkSwitchCases(cases.slice(1), b.ctx);
  return { cases: [{ ...cases[0], body: b.stmts }].concat(rest.cases), ctx: rest.ctx };
}

function recurseExpr(e: TExpr, ctx: CondCtx): ExprOut {
  switch (e.kind) {
    case "var": case "num": case "str": case "bool":
    case "havoc":
      return { expr: e, ctx };
    case "binop": {
      const l = walkExpr(e.left, ctx);
      const r = walkExpr(e.right, l.ctx);
      return { expr: { ...e, left: l.expr, right: r.expr }, ctx: r.ctx };
    }
    case "unop": {
      const x = walkExpr(e.expr, ctx);
      return { expr: { ...e, expr: x.expr }, ctx: x.ctx };
    }
    case "call": {
      const fn = walkExpr(e.fn, ctx);
      const args = walkExprs(e.args, fn.ctx);
      return { expr: { ...e, fn: fn.expr, args: args.exprs }, ctx: args.ctx };
    }
    case "index": {
      const obj = walkExpr(e.obj, ctx);
      const idx = walkExpr(e.idx, obj.ctx);
      return { expr: { ...e, obj: obj.expr, idx: idx.expr }, ctx: idx.ctx };
    }
    case "field": {
      const obj = walkExpr(e.obj, ctx);
      return { expr: { ...e, obj: obj.expr }, ctx: obj.ctx };
    }
    case "record": {
      // Statement form, not `e.spread !== null ? walkExpr(…) : null`: the
      // walkers lower to methods, and a method call inside a match-expression
      // arm gets lifted out of the binder's scope. Statement-position arms
      // keep the call in place (same hazard `ruleConditionalAndOptional`
      // guards against with containsMethodCall).
      let spread: ExprOut | null = null;
      if (e.spread !== null) spread = walkExpr(e.spread, ctx);
      const fields = walkRecordFields(e.fields, spread ? spread.ctx : ctx);
      return { expr: { ...e, spread: spread ? spread.expr : null, fields: fields.fields },
        ctx: fields.ctx };
    }
    case "arrayLiteral": {
      const elems = walkExprs(e.elems, ctx);
      return { expr: { ...e, elems: elems.exprs }, ctx: elems.ctx };
    }
    case "lambda": {
      const body = walkStmts(e.body, ctx);
      return { expr: { ...e, body: body.stmts }, ctx: body.ctx };
    }
    case "conditional": {
      const cond = walkExpr(e.cond, ctx);
      const then = walkExpr(e.then, cond.ctx);
      const els = walkExpr(e.else, then.ctx);
      return { expr: { ...e, cond: cond.expr, then: then.expr, else: els.expr }, ctx: els.ctx };
    }
    case "optChain": {
      const obj = walkExpr(e.obj, ctx);
      const chain = walkChainSteps(e.chain, obj.ctx);
      return { expr: { ...e, obj: obj.expr, chain: chain.steps }, ctx: chain.ctx };
    }
    case "nullish": {
      const l = walkExpr(e.left, ctx);
      const r = walkExpr(e.right, l.ctx);
      return { expr: { ...e, left: l.expr, right: r.expr }, ctx: r.ctx };
    }
    case "forall": {
      const b = walkExpr(e.body, ctx);
      return { expr: { ...e, body: b.expr }, ctx: b.ctx };
    }
    case "exists": {
      const b = walkExpr(e.body, ctx);
      return { expr: { ...e, body: b.expr }, ctx: b.ctx };
    }
    case "someMatch": {
      const some = walkExpr(e.someBody, ctx);
      const none = walkExpr(e.noneBody, some.ctx);
      return { expr: { ...e, someBody: some.expr, noneBody: none.expr }, ctx: none.ctx };
    }
    case "tagMatch": {
      const scrut = walkExpr(e.scrutinee, ctx);
      const cases = walkExprCases(e.cases, scrut.ctx);
      let ft: ExprOut | null = null;
      if (e.fallthrough !== null) ft = walkExpr(e.fallthrough, cases.ctx);
      return { expr: { ...e, scrutinee: scrut.expr, cases: cases.cases,
        fallthrough: ft ? ft.expr : null }, ctx: ft ? ft.ctx : cases.ctx };
    }
  }
}

function walkStmt(s: TStmt, ctx: CondCtx): StmtOut {
  // Recurse into children first, then try rules at this node.
  const r = recurseStmt(s, ctx);
  // Optional narrowing fires before Array.isArray narrowing: in a chain like
  // `next && Array.isArray(next.content)` the optional check must unwrap `next`
  // *outside* the array match, since `next.content` is unreachable until then.
  // (When the chain has no leading optional, ruleIfAndOptional no-ops and the
  // array rule fires; independent narrows commute, so the order is harmless.)
  // && rules fire before the simple rule because they produce nested ifs whose
  // inner shape doesn't match the simple rule directly.
  return ruleIfAndOptional(r.stmt, r.ctx) ?? ruleIfAndArrayIsArray(r.stmt, r.ctx) ?? ruleIfOptionalSimple(r.stmt, r.ctx) ?? ruleExprStmtAndOptional(r.stmt, r.ctx) ?? ruleOptionalIndexBinding(r.stmt, r.ctx) ?? r;
}

function walkStmts(stmts: TStmt[], ctx: CondCtx): StmtsOut {
  if (stmts.length === 0) return { stmts: [], ctx };
  const s = stmts[0];
  const rest = stmts.slice(1);
  // Discriminant rules consume a prefix of stmts; remaining is processed normally.
  const tagged = ruleDiscriminantChain(stmts, ctx) ?? ruleDiscriminantNegEarlyReturn(stmts, ctx);
  if (tagged) {
    const w = walkStmt(tagged.stmt, ctx);
    const after = walkStmts(stmts.slice(tagged.consumed), w.ctx);
    return { stmts: [w.stmt].concat(after.stmts), ctx: after.ctx };
  }
  const orRewrite = ruleEarlyReturnOrChain(s, rest, ctx);
  if (orRewrite) return { stmts: [orRewrite.stmt], ctx: orRewrite.ctx };
  const consumed = ruleEarlyReturnConsume(s, rest) ?? ruleEarlyReturnOptChainCompare(s, rest, ctx);
  if (consumed) {
    const w = walkStmt(consumed, ctx);
    return { stmts: [w.stmt], ctx: w.ctx };
  }
  // walkStmt first — narrow's expression rules may rewrite the let init from
  // `conditional` to `someMatch`, in which case the let-cond desugar shouldn't fire.
  const walked = walkStmt(s, ctx);
  const expanded = ruleLetCondAndOptional(walked.stmt);
  if (expanded) {
    const ws = walkEach(expanded, walked.ctx);
    const after = walkStmts(rest, ws.ctx);
    return { stmts: ws.stmts.concat(after.stmts), ctx: after.ctx };
  }
  const after = walkStmts(rest, walked.ctx);
  return { stmts: [walked.stmt].concat(after.stmts), ctx: after.ctx };
}

/** State-threaded `walkStmt` over each statement — unlike `walkStmts`, no
 *  list-level rules. Used for the let-cond expansion, whose pieces are
 *  re-walked individually. */
function walkEach(stmts: TStmt[], ctx: CondCtx): StmtsOut {
  if (stmts.length === 0) return { stmts: [], ctx };
  const h = walkStmt(stmts[0], ctx);
  const t = walkEach(stmts.slice(1), h.ctx);
  return { stmts: [h.stmt].concat(t.stmts), ctx: t.ctx };
}

function recurseStmt(s: TStmt, ctx: CondCtx): StmtOut {
  switch (s.kind) {
    case "let": {
      const init = walkExpr(s.init, ctx);
      return { stmt: { ...s, init: init.expr }, ctx: init.ctx };
    }
    case "assign": {
      const v = walkExpr(s.value, ctx);
      return { stmt: { ...s, value: v.expr }, ctx: v.ctx };
    }
    case "return": {
      const v = walkExpr(s.value, ctx);
      return { stmt: { ...s, value: v.expr }, ctx: v.ctx };
    }
    case "break": case "continue": case "throw": return { stmt: s, ctx };
    case "expr": {
      const x = walkExpr(s.expr, ctx);
      return { stmt: { ...s, expr: x.expr }, ctx: x.ctx };
    }
    case "if": {
      const cond = walkExpr(s.cond, ctx);
      const then = walkStmts(s.then, cond.ctx);
      const els = walkStmts(s.else, then.ctx);
      return { stmt: { ...s, cond: cond.expr, then: then.stmts, else: els.stmts }, ctx: els.ctx };
    }
    case "while": {
      const cond = walkExpr(s.cond, ctx);
      const invs = walkExprs(s.invariants, cond.ctx);
      let dec: ExprOut | null = null;
      if (s.decreases !== null) dec = walkExpr(s.decreases, invs.ctx);
      let dw: ExprOut | null = null;
      if (s.doneWith !== null) dw = walkExpr(s.doneWith, dec ? dec.ctx : invs.ctx);
      const body = walkStmts(s.body, dw ? dw.ctx : dec ? dec.ctx : invs.ctx);
      return { stmt: { ...s, cond: cond.expr, invariants: invs.exprs,
        decreases: dec ? dec.expr : null, doneWith: dw ? dw.expr : null,
        body: body.stmts }, ctx: body.ctx };
    }
    case "switch": {
      const x = walkExpr(s.expr, ctx);
      const cases = walkSwitchCases(s.cases, x.ctx);
      const def = walkStmts(s.defaultBody, cases.ctx);
      return { stmt: { ...s, expr: x.expr, cases: cases.cases, defaultBody: def.stmts },
        ctx: def.ctx };
    }
    case "forof": {
      const it = walkExpr(s.iterable, ctx);
      const invs = walkExprs(s.invariants, it.ctx);
      let dw: ExprOut | null = null;
      if (s.doneWith !== null) dw = walkExpr(s.doneWith, invs.ctx);
      const body = walkStmts(s.body, dw ? dw.ctx : invs.ctx);
      return { stmt: { ...s, iterable: it.expr, invariants: invs.exprs,
        doneWith: dw ? dw.expr : null, body: body.stmts }, ctx: body.ctx };
    }
    case "ghostLet": {
      const init = walkExpr(s.init, ctx);
      return { stmt: { ...s, init: init.expr }, ctx: init.ctx };
    }
    case "ghostAssign": {
      const v = walkExpr(s.value, ctx);
      return { stmt: { ...s, value: v.expr }, ctx: v.ctx };
    }
    case "assert": {
      const x = walkExpr(s.expr, ctx);
      return { stmt: { ...s, expr: x.expr }, ctx: x.ctx };
    }
    case "someMatch": {
      const some = walkStmts(s.someBody, ctx);
      const none = walkStmts(s.noneBody, some.ctx);
      return { stmt: { ...s, someBody: some.stmts, noneBody: none.stmts }, ctx: none.ctx };
    }
    case "tagMatch": {
      const scrut = walkExpr(s.scrutinee, ctx);
      const cases = walkStmtCases(s.cases, scrut.ctx);
      const ft = walkStmts(s.fallthrough, cases.ctx);
      return { stmt: { ...s, scrutinee: scrut.expr, cases: cases.cases,
        fallthrough: ft.stmts }, ctx: ft.ctx };
    }
  }
}

function isTerminating(stmts: TStmt[]): boolean {
  if (stmts.length === 0) return false;
  return isTerminatorKind(stmts[stmts.length - 1].kind);
}

// ── Presence drivers ────────────────────────────────────────

/** Driver: `if (e !== undefined) then else` — presence fact in if position.
 *  → `someMatch e { Some(_e_val) => then, None => else }`. Requires a
 *  non-empty Some branch. */
function ruleIfOptionalSimple(s: TStmt, ctx: CondCtx): StmtOut | null {
  if (s.kind !== "if") return null;
  const check = presentFact(s.cond);
  if (!check) return null;
  const someBody = check.negated ? s.else : s.then;
  const noneBody = check.negated ? s.then : s.else;
  if (someBody.length === 0) return null;
  return { stmt: presentMatchStmts(check, someBody, noneBody), ctx };
}

/** Driver: `if (e === undefined) terminate; rest` — presence fact in
 *  early-return position, consuming the rest of the block into the
 *  narrowed scope. Fires when the Some branch is empty. */
function ruleEarlyReturnConsume(s: TStmt, rest: TStmt[]): TStmt | null {
  if (s.kind !== "if") return null;
  if (rest.length === 0) return null;
  const check = presentFact(s.cond);
  if (!check) return null;
  const someBranch = check.negated ? s.else : s.then;
  const noneBranch = check.negated ? s.then : s.else;
  if (someBranch.length !== 0) return null;
  if (!isTerminating(noneBranch)) return null;
  return presentMatchStmts(check, rest, noneBranch);
}

/** Left-nested `||` of non-empty leaves — the inverse of `flattenOr`. */
function orChain(leaves: TExpr[]): TExpr {
  //@ requires leaves.length > 0
  let acc: TExpr = leaves[0];
  for (let i = 1; i < leaves.length; i++) {
    acc = { kind: "binop", op: "||", left: acc, right: leaves[i], ty: { kind: "bool" } };
  }
  return acc;
}

/** Driver: `if (D1 || … || Dn) terminate; rest` — De-Morgan position. Each `Di`
 *  that detects some optional `x` is None (`!x`, `x === undefined`,
 *  `x?.chain !== lit`) narrows that `x` to Some across `rest`; the rest —
 *  value guards reading a narrowed `x` directly, plus the detectors' Some-case
 *  residuals — become a trailing early-return. Sound: reaching `rest` means
 *  every disjunct was false, so every detected optional is present.
 *
 *  Returns a PRE-WALKED result, unlike the other consumed rules, and
 *  walkStmts must not walk it again. The terminating branch is duplicated
 *  into every None arm, and a decreasing termination measure exists only
 *  when duplicated statements are already walked — walked output is inert,
 *  while un-walked material weighs in once per copy. Walk order mirrors
 *  recurseStmt on someMatch (someBody before noneBody, innermost arms
 *  first), so minted binder numbering agrees with machine-walked nests. */
function ruleEarlyReturnOrChain(s: TStmt, rest: TStmt[], ctx: CondCtx): StmtOut | null {
  if (s.kind !== "if") return null;
  if (rest.length === 0) return null;
  if (s.then.length === 0 || s.else.length !== 0 || !isTerminating(s.then)) return null;
  if (s.cond.kind !== "binop" || s.cond.op !== "||") return null;  // single check is the simpler rule
  const leaves = flattenOr(s.cond);
  if (leaves.length < 2) return null;

  const detectors: NoneDetector[] = [];
  const residualLeaves: TExpr[] = [];
  const seen = new Set<string>();
  for (const leaf of leaves) {
    const d = noneDetector(leaf, ctx);
    if (!d) { residualLeaves.push(leaf); continue; }
    const key = binderHintFor(d.scrutinee);
    if (key === null) return null;  // unreachable: detector scrutinees are path-shaped
    if (seen.has(key)) return null;  // two detectors on one optional: rare; leave to other rules
    seen.add(key);
    detectors.push(d);
    if (d.residual) residualLeaves.push(d.residual);
  }
  if (detectors.length === 0) return null;

  // Statement form: a ternary would let transform lift the orChain call above
  // the emptiness guard, where its non-empty precondition can't hold.
  let inner: TStmt[] = rest;
  if (residualLeaves.length > 0) {
    inner = [{ kind: "if", cond: orChain(residualLeaves), then: s.then, else: [] }, ...rest];
  }
  const wInner = walkStmts(inner, ctx);
  let nest: TStmt[] = wInner.stmts;
  let c = wInner.ctx;
  for (let i = detectors.length - 1; i >= 0; i--) {
    // Non-empty after any iteration; the loop runs at least once (detectors ≠ []).
    //@ invariant nest.length > 0 || i === detectors.length - 1
    const d = detectors[i]!;
    const wThen = walkStmts(s.then, c);
    c = wThen.ctx;
    nest = [{ kind: "someMatch", scrutinee: d.scrutinee, binderTy: d.innerTy, binder: d.binder, someBody: nest, noneBody: wThen.stmts }];
  }
  return { stmt: nest[0], ctx: c };
}

/** Driver: `if (opt?.chain !== lit) terminate; rest` — bound-optional
 *  early-return. `opt?.chain` is `undefined` when `opt` is None, and
 *  `undefined !== lit` is true, so the None case takes the terminating branch —
 *  falling through to `rest` proves `opt` is Some. Rewrite to
 *    someMatch opt { Some(v) => [if (v.chain !== lit) terminate; rest]; None => terminate }
 *  narrowing `opt` to `v` across `rest` and handing the now-non-optional inner
 *  guard to the ordinary rules (e.g. discriminant narrowing). Restricted to
 *  `!==` so the None case is guaranteed to terminate. */
function ruleEarlyReturnOptChainCompare(s: TStmt, rest: TStmt[], ctx: CondCtx): TStmt | null {
  if (s.kind !== "if") return null;
  if (rest.length === 0) return null;
  if (s.else.length !== 0 || !isTerminating(s.then)) return null;
  const c = s.cond;
  if (c.kind !== "binop" || c.op !== "!==") return null;
  const ocOnLeft = c.left.kind === "optChain";
  const oc = ocOnLeft ? c.left : c.right.kind === "optChain" ? c.right : null;
  if (oc === null) return null;
  if (oc.kind !== "optChain") return null;
  if (oc.obj.ty.kind !== "optional") return null;
  const lit = ocOnLeft ? c.right : c.left;
  const innerTy = oc.obj.ty.inner;
  const hint = binderHintFor(oc.obj);
  if (hint === null) return null;
  const binder = freshName(hint);
  const binderVar: TExpr = { kind: "var", name: binder, ty: innerTy };
  const unwrapped = restoreDiscriminantFlag(applyChain(binderVar, oc.chain), ctx.decls);
  const innerGuard: TExpr = { kind: "binop", op: "!==", left: unwrapped, right: lit, ty: { kind: "bool" } };
  // Keep `rest` as trailing statements (not an else branch) — `s.then` terminates,
  // so `if (g) terminate; rest` ≡ `if (g) terminate else rest`, and the trailing
  // form lets the ordinary early-exit rules (e.g. discriminant narrowing) fire on
  // the now-non-optional inner guard when `chain` is a union discriminant.
  const someBody: TStmt[] = [{ kind: "if", cond: innerGuard, then: s.then, else: [] }, ...rest];
  return { kind: "someMatch", scrutinee: oc.obj, binder, binderTy: innerTy, someBody, noneBody: s.then };
}

/** Driver (expression): `e !== undefined ? a : b` — presence fact in
 *  ternary position. */
function ruleConditionalOptionalSimple(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "conditional") return null;
  const check = presentFact(e.cond);
  if (!check) return null;
  const someBody = check.negated ? e.else : e.then;
  const noneBody = check.negated ? e.then : e.else;
  return { expr: presentMatchExpr(check, someBody, noneBody, e.ty), ctx };
}

/** Driver (expression): `(path !== undefined [&& rest]) ==> B` — presence
 *  fact in implication position (spec premises). The premise's optional
 *  checks bind narrowed values that the conclusion can use.
 *  → `someMatch path { Some(_p_val) => (rest ==> B), None => true }`.
 *  Walks the inner ==> recursively so chained checks become nested
 *  someMatches. Spec form: no falsy gate (historical shape — presence
 *  suffices in the premise). */
function ruleImplOptional(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "binop" || e.op !== "==>") return null;
  // No uninitialized let (it has no backend model), and presence guards are
  // split from dependent reads so each early return narrows on its own.
  let check: PresentFact | null = null;
  let restCond: TExpr | null = null;
  const extracted = leadingPresent(e.left);
  if (extracted) {
    check = extracted.check;
    restCond = extracted.restCond;
  } else {
    const c = presentFact(e.left);
    if (c === null) return null;
    if (c.negated) return null;
    check = c;
  }
  if (check === null) return null;
  const innerBody: TExpr = restCond
    ? { kind: "binop", op: "==>", left: restCond, right: e.right, ty: { kind: "bool" } }
    : e.right;
  const w = walkExpr(innerBody, ctx);
  return {
    expr: {
      kind: "someMatch",
      scrutinee: check.scrutinee, binderTy: check.innerTy,
      binder: check.binder,
      someBody: w.expr,
      noneBody: { kind: "bool", value: true, ty: { kind: "bool" } },
      ty: { kind: "bool" },
    },
    ctx: w.ctx,
  };
}

/** Driver (expression): `left ?? right` — nullish coalescing.
 *  → `someMatch left { Some(_v) => _v, None => right }`.
 *  Single-evaluation: scrutinee may be any expression. Presence-only
 *  semantics (`??` tests null/undefined, not falsiness) — no falsy gate. */
function ruleNullish(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "nullish") return null;
  if (e.left.ty.kind !== "optional") return null;
  const innerTy = e.left.ty.inner;
  const b = freshOcBinder(ctx);
  return {
    expr: {
      kind: "someMatch",
      scrutinee: e.left, binder: b.name, binderTy: innerTy,
      someBody: { kind: "var", name: b.name, ty: innerTy },
      noneBody: e.right,
      ty: e.ty,
    },
    ctx: b.ctx,
  };
}

/** Driver (expression): `arr[i] ?? right` — in-bounds fact in nullish
 *  position. Under noUncheckedIndexedAccess `arr[i]` is `T | undefined`,
 *  undefined exactly when out of bounds, so
 *  → `(0 <= i && i < arr.length) ? arr[i] : right`. The guarded `then`
 *  keeps the seq index in bounds for the backend. (Map index is already
 *  optional-typed and handled by ruleNullish above.) */
function ruleNullishIndex(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "nullish") return null;
  if (e.left.kind !== "index") return null;
  if (e.left.obj.ty.kind !== "array") return null;
  const cond = arrayBoundsCond(e.left.obj, e.left.idx);
  return { expr: { kind: "conditional", cond, then: e.left, else: e.right, ty: e.ty }, ctx };
}

/** Driver (expression): `arr[i]?.<chain>` — in-bounds fact in optChain
 *  position, the optChain sibling of ruleNullishIndex.
 *  → `(0 <= i && i < arr.length) ? <chain on arr[i]> : undefined`. The
 *  conditional's optional type makes transform wrap the in-bounds chain
 *  result in Some and the OOB branch in None. (ruleOptChain itself bails
 *  here: an array index is typed as the non-optional element type.) */
function ruleOptChainIndex(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.kind !== "index") return null;
  if (e.obj.obj.ty.kind !== "array") return null;
  const cond = arrayBoundsCond(e.obj.obj, e.obj.idx);
  const body = applyChain(e.obj, e.chain); // arr[i] — in bounds under `cond`
  const undef: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  return { expr: { kind: "conditional", cond, then: body, else: undef, ty: e.ty }, ctx };
}

/** Driver (statement): reconcile a `const e = arr[i]` whose binding is optional
 *  (`e: T | undefined`) but whose array-index initializer is total (`T`) —
 *  in-bounds fact in initializer position. Model the index as its JS
 *  semantics — `e := inBounds ? arr[i] : undefined` — so `e` is a real
 *  `Option<T>` and a later `e?.f` someMatch is well-typed; an in-bounds proof
 *  makes the None branch dead. Skipped when the element type is already
 *  optional: no mismatch. */
function ruleOptionalIndexBinding(s: TStmt, ctx: CondCtx): StmtOut | null {
  if (s.kind !== "let") return null;
  if (s.ty.kind !== "optional") return null;
  const init = s.init;
  if (init.kind !== "index") return null;
  if (init.obj.ty.kind !== "array") return null;
  if (init.ty.kind === "optional") return null;  // array-of-optionals: not a flag artifact
  const cond = arrayBoundsCond(init.obj, init.idx);
  const undef: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  const guarded: TExpr = { kind: "conditional", cond, then: init, else: undef, ty: s.ty };
  return { stmt: { ...s, init: guarded }, ctx };
}

/** Driver (expression): `obj?.<chain>` — single-eval optional chain.
 *  → `someMatch obj { Some(_oc{N}_val) => apply(chain, _oc{N}_val), None => undefined }`.
 *  The someBody applies the chain to the binder directly (field/call/index),
 *  so transform doesn't substitute. Scrutinee can be any expression. */
function ruleOptChain(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.ty.kind !== "optional") return null;
  const innerTy = e.obj.ty.inner;
  const b = freshOcBinder(ctx);
  const body = applyChain({ kind: "var", name: b.name, ty: innerTy }, e.chain);
  const noneBody: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  return {
    expr: {
      kind: "someMatch",
      scrutinee: e.obj, binder: b.name, binderTy: innerTy,
      someBody: body, noneBody, ty: e.ty,
    },
    ctx: b.ctx,
  };
}

/** Driver (expression): `k in m ? m[k] : default` — key-membership fact in
 *  ternary position, m map-typed. The then-branch must be exactly `m[k]`.
 *  → `someMatch m[k] { Some(_m_k_val) => _m_k_val, None => default }`.
 *  The existing Dafny peephole collapses the result to
 *  `if k in m then m[k] else default`. */
function ruleConditionalInMap(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "conditional") return null;
  if (e.cond.kind !== "binop" || e.cond.op !== "in") return null;
  const m = e.cond.right;
  const k = e.cond.left;
  if (m.ty.kind !== "map") return null;
  // Then-branch must be exactly m[k].
  if (e.then.kind !== "index") return null;
  if (!exprEqual(e.then.obj, m) || !exprEqual(e.then.idx, k)) return null;
  // Only narrow when the else branch has a concrete non-optional type — otherwise
  // the overall ternary could legitimately be Option<V> (e.g., `k in m ? m[k] : undefined`).
  if (e.else.ty.kind === "optional" || e.else.ty.kind === "void") return null;
  // Dormant backup: when resolve's in-atom narrowing has already fired, e.then.ty is V,
  // not Option<V>. The `someMatch` scrutinee would then have the wrong shape. Skip —
  // the enclosing expression is already a plain if-then-else of the correct type.
  if (e.then.ty.kind !== "optional") return null;
  const innerTy = m.ty.value;
  const b = binderHintForMapAccess(m, k, ctx);
  return {
    expr: {
      kind: "someMatch",
      scrutinee: e.then, binder: b.name, binderTy: innerTy,
      someBody: { kind: "var", name: b.name, ty: innerTy },
      noneBody: e.else, ty: innerTy,
    },
    ctx: b.ctx,
  };
}

/** Driver (expression): `opt ? a : b` (truthiness — cond itself is optional).
 *  Only fires for simple var or simple `obj.field` cond. Historical shape:
 *  no falsy gate on the bound value (unlike the other truthiness positions). */
function ruleConditionalOptionalTruthy(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "conditional") return null;
  if (e.cond.ty.kind !== "optional") return null;
  const hint = binderHintFor(e.cond);
  if (hint === null) return null;
  const binder = freshName(hint);
  return {
    expr: {
      kind: "someMatch",
      scrutinee: e.cond, binderTy: e.cond.ty.inner,
      binder,
      someBody: e.then, noneBody: e.else, ty: e.ty,
    },
    ctx,
  };
}

/** Driver: `if (x !== undefined && rest) then` (no else) — presence fact in
 *  guarded-if position.
 *  → `someMatch x { Some(_x_val) => if rest then then; , None => {} }`.
 *  Walks the inner if back through narrow so that nested optional checks in
 *  rest also become someMatches. */
function ruleIfAndOptional(s: TStmt, ctx: CondCtx): StmtOut | null {
  if (s.kind !== "if") return null;
  if (s.else.length !== 0) return null;
  const extracted = leadingPresent(s.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerIf: TStmt = { kind: "if", cond: restCond, then: s.then, else: [] };
  const w = walkStmt(innerIf, ctx);
  return { stmt: presentMatchStmts(check, [w.stmt], []), ctx: w.ctx };
}

/** Driver: a bare expression statement `x !== undefined && rest` (the
 *  `if`-less guard idiom, TS-equivalent to `if (x !== undefined) rest;`).
 *  → `someMatch x { Some(_x_val) => rest;, None => {} }`.
 *  Runs `rest` for effect inside the narrowed scope. Unlike the ternary
 *  driver (`ruleConditionalAndOptional`), a method call in `rest` is fine
 *  here: a statement-level someMatch arm keeps it in statement position, so
 *  transform never ANF-lifts it out of the arm. */
function ruleExprStmtAndOptional(s: TStmt, ctx: CondCtx): StmtOut | null {
  if (s.kind !== "expr") return null;
  if (s.expr.kind !== "binop" || s.expr.op !== "&&") return null;
  const extracted = leadingPresent(s.expr);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerStmt: TStmt = { kind: "expr", expr: restCond };
  const w = walkStmt(innerStmt, ctx);
  return { stmt: presentMatchStmts(check, [w.stmt], []), ctx: w.ctx };
}

/** Driver (statement): `let x = (e_opt && rest) ? a : b` — presence fact in
 *  conditional-initializer position, where rest may contain method calls.
 *  → `var x: T := b; someMatch e_opt { Some(_v) => { if rest { x := a } } }`.
 *  Statement-level form is needed because Dafny doesn't allow method calls
 *  inside match expression arms. */
function ruleLetCondAndOptional(s: TStmt): TStmt[] | null {
  if (s.kind !== "let" || s.mutable) return null;
  if (s.init.kind !== "conditional") return null;
  const extracted = leadingPresent(s.init.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const assignIf: TStmt = { kind: "if", cond: restCond,
    then: [{ kind: "assign", target: s.name, value: s.init.then }], else: [] };
  return [
    { kind: "let", name: s.name, ty: s.ty, mutable: true, init: s.init.else },
    presentMatchStmts(check, [assignIf], []),
  ];
}

/** Does this expression contain a method call that would be lifted to a
 *  var binding outside its containing expression by transform? Such calls
 *  are unsafe inside a match arm — the lifted binding would reference a
 *  name only valid in the arm. Builtins whose registry entry is `pure`
 *  (they lower to pure Dafny expressions: `x in arr`, `x in m`, `s.Keys`,
 *  …) are exempt even though they carry `callKind: "method"`. */
function containsMethodCall(e: TExpr): boolean {
  if (e.kind === "call" && e.callKind === "method") {
    const bid = e.builtinId;
    if (bid === undefined) return true;
    if (!builtinPure(bid)) return true;
  }
  switch (e.kind) {
    case "var": case "num": case "str": case "bool":
    case "havoc":
      return false;
    case "binop": return containsMethodCall(e.left) || containsMethodCall(e.right);
    case "unop": return containsMethodCall(e.expr);
    case "call": return containsMethodCall(e.fn) || e.args.some(containsMethodCall);
    case "index": return containsMethodCall(e.obj) || containsMethodCall(e.idx);
    case "field": return containsMethodCall(e.obj);
    case "record":
      return (e.spread ? containsMethodCall(e.spread) : false) ||
        e.fields.some(f => containsMethodCall(f.value));
    case "arrayLiteral": return e.elems.some(containsMethodCall);
    case "lambda": return false;  // body is its own scope
    case "conditional":
      return containsMethodCall(e.cond) || containsMethodCall(e.then) || containsMethodCall(e.else);
    case "optChain": return containsMethodCall(e.obj);
    case "nullish": return containsMethodCall(e.left) || containsMethodCall(e.right);
    case "forall": case "exists": return containsMethodCall(e.body);
    case "someMatch": return containsMethodCall(e.scrutinee) ||
      containsMethodCall(e.someBody) || containsMethodCall(e.noneBody);
    case "tagMatch": return containsMethodCall(e.scrutinee) ||
      e.cases.some(c => containsMethodCall(c.body)) ||
      (e.fallthrough ? containsMethodCall(e.fallthrough) : false);
  }
}

/** Driver (expression): `x !== undefined && rest ? a : b` — presence fact in
 *  guarded-ternary position.
 *  → `someMatch x { Some(_x_val) => if rest then a else b, None => b }`.
 *  Walks the inner conditional back through narrow so chained checks become
 *  nested someMatches. Does NOT fire if the guard `rest` contains method
 *  calls — transform lifts those out of the match arm, breaking the binder
 *  scope. The original transform's let-desugar handles those by lifting to
 *  a mutable var first. */
function ruleConditionalAndOptional(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "conditional") return null;
  const extracted = leadingPresent(e.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  if (containsMethodCall(restCond)) return null;
  const innerCond: TExpr = {
    kind: "conditional",
    cond: restCond, then: e.then, else: e.else, ty: e.ty,
  };
  const w = walkExpr(innerCond, ctx);
  return { expr: presentMatchExpr(check, w.expr, e.else, e.ty), ctx: w.ctx };
}

// ── Variant drivers (discriminants and synth array-unions) ──

/** Driver (expression): `Array.isArray(x) ==> B` or `!Array.isArray(x) ==> B` —
 *  isArray fact in implication position (spec premises).
 *  → `tagMatch x { ArrayBranch => walkExpr(B), _ => true }` (or NonArrayBranch).
 *  The other variant becomes a vacuous-true fallthrough. */
function ruleImplArrayIsArray(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "binop" || e.op !== "==>") return null;
  const pos = isArrayFact(e.left, ctx);
  const neg = e.left.kind === "unop" && e.left.op === "!"
    ? isArrayFact(e.left.expr, ctx)
    : null;
  const matched = pos ?? (neg ? { scrutinee: neg.scrutinee, typeName: neg.typeName, variant: "NonArrayBranch" as const } : null);
  if (!matched) return null;
  const w = walkExpr(e.right, ctx);
  return {
    expr: {
      kind: "tagMatch",
      scrutinee: matched.scrutinee,
      typeName: matched.typeName,
      cases: [{ variant: matched.variant, body: w.expr }],
      fallthrough: { kind: "bool", value: true, ty: { kind: "bool" } },
      ty: { kind: "bool" },
    },
    ctx: w.ctx,
  };
}

/** Driver (expression): `Array.isArray(x) ? a : b` — isArray fact in ternary
 *  position (also `typeof x === "string"`, which selects the NonArrayBranch).
 *  → `tagMatch x { <variant> => walkExpr(then-side) } fallthrough walkExpr(else-side)`.
 *  Inside the matched arm, bare references to `x` are rewritten to the
 *  variant's payload field by `transformExpr` when emitting the tagMatch. */
function ruleConditionalArrayIsArray(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "conditional") return null;
  const pos = isArrayFact(e.cond, ctx);
  // `typeof x === "string"` is a positive check like `Array.isArray`, but selects
  // the NonArrayBranch — its then-branch is the matched-variant body.
  // Statement form with explicit null tests (not `pos ? … : …` truthiness or
  // `!pos && !tof && …` chains): optional truthiness inside `&&` lowers to
  // match-expression operands, a shape Dafny 4.11's translator asserts on.
  let tof: IsArrayFact | null = null;
  if (pos === null) tof = typeofStringFact(e.cond, ctx);
  let neg: IsArrayFact | null = null;
  if (pos === null) {
    if (tof === null) {
      if (e.cond.kind === "unop" && e.cond.op === "!") {
        neg = isArrayFact(e.cond.expr, ctx);
      }
    }
  }
  const matched = pos ?? tof ?? (neg ? { scrutinee: neg.scrutinee, typeName: neg.typeName, variant: "NonArrayBranch" as const } : null);
  if (!matched) return null;
  const positive = pos ?? tof;
  const thenBody = positive ? e.then : e.else;
  const elseBody = positive ? e.else : e.then;
  const wThen = walkExpr(thenBody, ctx);
  const wElse = walkExpr(elseBody, wThen.ctx);
  return {
    expr: {
      kind: "tagMatch",
      scrutinee: matched.scrutinee,
      typeName: matched.typeName,
      cases: [{ variant: matched.variant, body: wThen.expr }],
      fallthrough: wElse.expr,
      ty: e.ty,
    },
    ctx: wElse.ctx,
  };
}

/** Driver: `if (<rest> && Array.isArray(path) && <more>) then [else]` —
 *  isArray fact in guarded-if position.
 *  → `tagMatch path { ArrayBranch => if (<rest && more>) then [else] }`.
 *  The remaining conjuncts move inside the matched arm so any narrowing the
 *  `then` body relies on (typed `path` accesses) sees the unwrapped variant. */
function ruleIfAndArrayIsArray(s: TStmt, ctx: CondCtx): StmtOut | null {
  if (s.kind !== "if") return null;
  const extracted = leadingIsArray(s.cond, ctx);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  // Inner if uses the remaining conjunction. Walk recursively so nested
  // checks compose.
  const innerIf: TStmt = { kind: "if", cond: restCond, then: s.then, else: s.else };
  const w = walkStmt(innerIf, ctx);
  return {
    stmt: {
      kind: "tagMatch",
      scrutinee: check.scrutinee,
      typeName: check.typeName,
      cases: [{ variant: check.variant, body: [w.stmt] }],
      fallthrough: s.else,
    },
    ctx: w.ctx,
  };
}

/** Driver (expression): `(<rest> && Array.isArray(path)) ? a : b` — isArray
 *  fact in guarded-ternary position.
 *  → `tagMatch path { ArrayBranch => (<rest>) ? a : b } fallthrough b`. */
function ruleConditionalAndArrayIsArray(e: TExpr, ctx: CondCtx): ExprOut | null {
  if (e.kind !== "conditional") return null;
  const extracted = leadingIsArray(e.cond, ctx);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerCond: TExpr = {
    kind: "conditional",
    cond: restCond, then: e.then, else: e.else, ty: e.ty,
  };
  const w = walkExpr(innerCond, ctx);
  return {
    expr: {
      kind: "tagMatch",
      scrutinee: check.scrutinee,
      typeName: check.typeName,
      cases: [{ variant: check.variant, body: w.expr }],
      fallthrough: e.else,
      ty: e.ty,
    },
    ctx: w.ctx,
  };
}

/** An if-else-if chain flattened against one discriminator: the cases
 *  collected off the else spine, plus the fallthrough that ends it. */
interface ElseChain { cases: TStmtCase[]; fallthrough: TStmt[] }

/** Flatten an else-spine of `if (x.kind === "v")` tests on `scrutineeName`
 *  into cases; the first non-matching statement (or multi-statement else)
 *  becomes the fallthrough. */
function collectElseChain(s: TStmt, scrutineeName: string, ctx: CondCtx): ElseChain {
  if (s.kind !== "if") return { cases: [], fallthrough: [s] };
  const p = variantFact(s.cond, ctx);
  if (!p || p.scrutineeName !== scrutineeName) return { cases: [], fallthrough: [s] };
  const here: TStmtCase = { variant: p.variant, body: s.then };
  if (s.else.length === 0) return { cases: [here], fallthrough: [] };
  if (s.else.length === 1 && s.else[0].kind === "if") {
    const rest = collectElseChain(s.else[0], scrutineeName, ctx);
    return { cases: [here].concat(rest.cases), fallthrough: rest.fallthrough };
  }
  return { cases: [here], fallthrough: s.else };
}

/** A list-level rewrite: the replacement statement plus how many input
 *  statements it consumed. One named type shared by both discriminant rules
 *  so their `??` join has a single shape. */
interface ConsumedRewrite { stmt: TStmt; consumed: number }

/** Driver (list-level): consecutive `if (x.kind === "v") ...` chain →
 *  tagMatch. Walks consecutive top-level ifs on the same discriminator var;
 *  the first one with an else-branch ends the chain (else becomes
 *  fallthrough; if-else-if flattens into more cases). Returns the tagMatch
 *  and how many stmts consumed. */
function ruleDiscriminantChain(stmts: TStmt[], ctx: CondCtx): ConsumedRewrite | null {
  //@ ensures \result !== null ==> \result.consumed >= 0 && \result.consumed <= stmts.length
  if (stmts.length === 0 || stmts[0].kind !== "if") return null;
  const first = variantFact(stmts[0].cond, ctx);
  if (!first) return null;

  const cases: TStmtCase[] = [];

  let consumed = 0;
  for (let i = 0; i < stmts.length; i++) {
    //@ invariant consumed >= 0 && consumed <= stmts.length
    //@ invariant i <= stmts.length
    const s = stmts[i];
    if (s.kind !== "if") break;
    const p = variantFact(s.cond, ctx);
    if (!p || p.scrutineeName !== first.scrutineeName) break;
    cases.push({ variant: p.variant, body: s.then });
    consumed = i + 1;
    if (s.else.length > 0) {
      const tail: ElseChain = (s.else.length === 1 && s.else[0].kind === "if")
        ? collectElseChain(s.else[0], first.scrutineeName, ctx)
        : { cases: [], fallthrough: s.else };
      return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
        cases: cases.concat(tail.cases), fallthrough: tail.fallthrough }, consumed };
    }
  }
  if (cases.length === 0) return null;
  // If every case terminates, the trailing statements are the default arm
  // (preserving the clean dispatch-as-expression shape). Otherwise the tail runs
  // after the match for every variant, so leave it to the caller (empty default)
  // rather than mis-routing it into the default arm only.
  if (cases.every(c => isTerminating(c.body))) {
    return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
      cases, fallthrough: stmts.slice(consumed) }, consumed: stmts.length };
  }
  return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
    cases, fallthrough: [] }, consumed };
}

/** Driver (list-level): `if (x.kind !== "v") terminate; rest` → tagMatch
 *  with cases = [{ variant: v, body: rest }] and fallthrough = terminate. */
function ruleDiscriminantNegEarlyReturn(stmts: TStmt[], ctx: CondCtx): ConsumedRewrite | null {
  //@ ensures \result !== null ==> \result.consumed >= 0 && \result.consumed <= stmts.length
  if (stmts.length < 2) return null;
  const first = stmts[0];
  if (first.kind !== "if" || first.else.length > 0) return null;
  if (!isTerminating(first.then)) return null;
  const cond = negVariantFact(first.cond, ctx);
  if (!cond) return null;
  return { stmt: { kind: "tagMatch", scrutinee: cond.scrutinee, typeName: cond.typeName,
    cases: [{ variant: cond.variant, body: stmts.slice(1) }], fallthrough: first.then },
    consumed: stmts.length };
}

// ── Function / module entry ──────────────────────────────────

interface FunctionOut { fn: TFunction; ctx: CondCtx }

function narrowFunction(fn: TFunction, ctx: CondCtx): FunctionOut {
  const reqs = walkExprs(fn.requires, ctx);
  const enss = walkExprs(fn.ensures, reqs.ctx);
  let dec: ExprOut | null = null;
  if (fn.decreases !== null) dec = walkExpr(fn.decreases, enss.ctx);
  const body = walkStmts(fn.body, dec ? dec.ctx : enss.ctx);
  return {
    fn: {
      ...fn,
      requires: reqs.exprs,
      ensures: enss.exprs,
      decreases: dec ? dec.expr : null,
      body: body.stmts,
    },
    ctx: body.ctx,
  };
}

interface ConstantsOut { constants: TConst[]; ctx: CondCtx }

function narrowConstants(constants: TConst[], ctx: CondCtx): ConstantsOut {
  if (constants.length === 0) return { constants: [], ctx };
  const v = walkExpr(constants[0].value, ctx);
  const rest = narrowConstants(constants.slice(1), v.ctx);
  return { constants: [{ ...constants[0], value: v.expr }].concat(rest.constants), ctx: rest.ctx };
}

interface FunctionsOut { functions: TFunction[]; ctx: CondCtx }

function narrowFunctions(fns: TFunction[], ctx: CondCtx): FunctionsOut {
  if (fns.length === 0) return { functions: [], ctx };
  const f = narrowFunction(fns[0], ctx);
  const rest = narrowFunctions(fns.slice(1), f.ctx);
  return { functions: [f.fn].concat(rest.functions), ctx: rest.ctx };
}

interface ClassesOut { classes: TClass[]; ctx: CondCtx }

function narrowClasses(classes: TClass[], ctx: CondCtx): ClassesOut {
  if (classes.length === 0) return { classes: [], ctx };
  const methods = narrowFunctions(classes[0].methods, ctx);
  const rest = narrowClasses(classes.slice(1), methods.ctx);
  return { classes: [{ ...classes[0], methods: methods.functions }].concat(rest.classes),
    ctx: rest.ctx };
}

export function narrowModule(mod: TModule): TModule {
  const ctx: CondCtx = { decls: mod.typeDecls, ocN: 0 };
  const consts = narrowConstants(mod.constants, ctx);
  const fns = narrowFunctions(mod.functions, consts.ctx);
  const classes = narrowClasses(mod.classes, fns.ctx);
  return {
    ...mod,
    constants: consts.constants,
    functions: fns.functions,
    classes: classes.classes,
  };
}
