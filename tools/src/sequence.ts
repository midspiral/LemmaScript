/**
 * Sequencing — hoist assignment expressions into statements.
 *
 * Runs on the typed IR after narrowing. Afterwards the only `assignment` node
 * left is a statement-level write `target = value` with effect-free parts, so
 * expression lowering never has to order side effects.
 */

import type { TExpr, TStmt, TModule, TFunction, Ty } from "./typedir.js";
import { tyEqual } from "./typedir.js";
import { freshName } from "./names.js";
import { mapTExpr, asTAccessPath } from "./transform.js";
import { containsMethodCall } from "./narrow.js";

type Assignment = Extract<TExpr, { kind: "assignment" }>;

const bool: Ty = { kind: "bool" };
const REFERENCE_KINDS = ["array", "map", "set", "user", "tuple"];
const LITERAL_KINDS = ["num", "bigint", "str", "bool", "lambda"];

let counter = 0;

/** The expression walker stops at lambdas, which execute in their own scope. */
function anyTExpr(e: TExpr, predicate: (e: TExpr) => boolean): boolean {
  let found = false;
  mapTExpr(e, node => (found ||= predicate(node)) ? node : null);
  return found;
}

const hasAssignment = (e: TExpr) => anyTExpr(e, node => node.kind === "assignment");
const variable = (name: string, ty: Ty): TExpr => ({ kind: "var", name, ty });
const not = (expr: TExpr): TExpr => ({ kind: "unop", op: "!", expr, ty: bool });
const truthy = (e: TExpr): TExpr => e.ty.kind === "bool" ? e : not(not(e));

function bind(e: TExpr, out: TStmt[], prefix = "eval"): TExpr {
  if (LITERAL_KINDS.includes(e.kind)) return e;
  const name = freshName(`_${prefix}${counter++}`);
  out.push({ kind: "let", name, ty: e.ty, mutable: false, init: e });
  return variable(name, e.ty);
}

/** Save an operand before `later` operands run. Reading a collection captures
 *  its reference, so a stable access path stays live across later element or
 *  field writes; only a later rebinding of the path needs a snapshot. */
function save(e: TExpr, out: TStmt[], later: TExpr[], copy: boolean): TExpr {
  const value = seq(e, out);
  const reference = e.kind === "assignment" && e.op === "=" && tyEqual(e.ty, e.target.ty) ? e.target : value;
  const path = asTAccessPath(reference);
  const rebinds = (node: TExpr) => {
    const target = node.kind === "assignment" ? asTAccessPath(node.target) : null;
    return !!target && target.rootVar === path!.rootVar && target.fields.length <= path!.fields.length &&
      target.fields.every((field, i) => field === path!.fields[i]);
  };
  if (!copy && path && REFERENCE_KINDS.includes(e.ty.kind) && !later.some(next => anyTExpr(next, rebinds))) return reference;
  return bind(value, out);
}

/** Map immediate operands in evaluation order, keeping call dispatch metadata. */
function mapOperands(e: TExpr, f: (operand: TExpr, copy: boolean) => TExpr): TExpr {
  if (e.kind === "call") {
    const fn = e.fn.kind === "field"
      ? { ...e.fn, obj: e.fn.obj.kind === "var" && e.fn.obj.ty.kind === "unknown" ? e.fn.obj : f(e.fn.obj, false) }
      : e.fn.kind === "var" ? e.fn : f(e.fn, false);
    return { ...e, fn, args: e.args.map(arg => f(arg, false)) };
  }
  return mapTExpr(e, child => child === e ? null : f(child,
    (e.kind === "record" && child === e.spread) || (e.kind === "binop" && e.op === "arrayConcat" && child === e.left)));
}

/** Each arm owns its effects; only the selected arm assigns the result.
 *  Returns null when no arm has effects, so the expression form can stay. */
function branch(ty: Ty, bodies: TExpr[], out: TStmt[], build: (arms: TStmt[][]) => TStmt): TExpr | null {
  const effects: TStmt[][] = bodies.map(() => []);
  const values = bodies.map((body, i) => seq(body, effects[i]));
  if (effects.every(ss => !ss.length)) return null;
  const name = freshName(`_branch${counter++}`);
  const wrap = (v: TExpr): TExpr =>
    ty.kind !== "optional" || v.ty.kind === "optional" || v.ty.kind === "void" || v.ty.kind === "unknown" ? v
      : { kind: "call", fn: variable("Some", ty), args: [v], ty, callKind: "pure" };
  // Every arm assigns before the result is read, so the initializer is unobservable.
  out.push({ kind: "let", name, ty, mutable: true, init: { kind: "havoc", ty, placeholder: true } });
  out.push(build(values.map((v, i) => [...effects[i], { kind: "assign", target: name, value: wrap(v) }])));
  return variable(name, ty);
}

/** Evaluate computed indices once, before the right-hand side. */
function seqTarget(e: TExpr, out: TStmt[]): TExpr {
  if (e.kind === "field") return { ...e, obj: seqTarget(e.obj, out) };
  if (e.kind === "index") {
    const obj = seqTarget(e.obj, out);
    return { ...e, obj, idx: bind(seq(e.idx, out), out) };
  }
  return e.kind === "var" ? e : bind(seq(e, out), out);
}

function seqAssignment(e: Assignment, out: TStmt[]): TExpr {
  const target = seqTarget(e.target, out);
  const old = e.op === "=" ? null : bind(target, out);
  if (e.op === "&&=" || e.op === "||=" || e.op === "??=") {
    const assign: TExpr = { ...e, op: "=", target };
    if (e.op === "??=") {
      if (old!.ty.kind !== "optional") return old!;
      const binder = freshName(`_present${counter++}`);
      return seq({ kind: "someMatch", scrutinee: old!, binder, binderTy: old!.ty.inner,
        someBody: variable(binder, old!.ty.inner), noneBody: assign, ty: e.ty }, out);
    }
    return seq({ kind: "conditional", cond: truthy(old!), ty: e.ty,
      then: e.op === "&&=" ? assign : old!, else: e.op === "&&=" ? old! : assign }, out);
  }
  const value = seq(e.op === "=" ? e.value
    : { kind: "binop", op: e.op.slice(0, -1), left: old!, right: e.value, ty: e.ty }, out);
  out.push({ kind: "let", name: e.resultName, ty: e.ty, mutable: false, init: value });
  // Plain variables and `this` fields are ordinary assignments. Element and
  // field paths keep the node so the backend rebuilds the value to its root.
  const name = target.kind === "var" ? target.name
    : target.kind === "field" && target.obj.kind === "var" && target.obj.name === "this" ? `this.${target.field}` : null;
  out.push(name ? { kind: "assign", target: name, value: e.storedValue }
    : { kind: "expr", expr: { ...e, op: "=", target, value: e.storedValue, postfix: undefined } });
  return e.postfix ? old! : variable(e.resultName, e.ty);
}

/** An assignment-free expression for `e`'s value; `e`'s effects go to `out`. */
function seq(e: TExpr, out: TStmt[]): TExpr {
  if (!hasAssignment(e)) return e;
  switch (e.kind) {
    case "assignment":
      return seqAssignment(e, out);
    case "conditional": {
      const cond = seq(e.cond, out);
      return branch(e.ty, [e.then, e.else], out, ([then, else_]) => ({ kind: "if", cond, then, else: else_ }))
        ?? { ...e, cond };
    }
    case "someMatch": {
      let scrutinee = seq(e.scrutinee, out);
      return branch(e.ty, [e.someBody, e.noneBody], out, ([someBody, noneBody]) => {
        if (!asTAccessPath(scrutinee)) scrutinee = bind(scrutinee, out);
        return { kind: "someMatch", scrutinee, binder: e.binder, binderTy: e.binderTy, someBody, noneBody };
      }) ?? { ...e, scrutinee };
    }
    case "tagMatch": {
      const scrutinee = seq(e.scrutinee, out);
      const bodies = [...e.cases.map(c => c.body), ...(e.fallthrough ? [e.fallthrough] : [])];
      return branch(e.ty, bodies, out, arms => ({ kind: "tagMatch", scrutinee, typeName: e.typeName,
        cases: e.cases.map((c, i) => ({ variant: c.variant, body: arms[i] })),
        fallthrough: e.fallthrough ? arms[arms.length - 1] : [] })) ?? { ...e, scrutinee };
    }
  }
  if (e.kind === "binop" && (e.op === "&&" || e.op === "||")) {
    const left = bind(seq(e.left, out), out);
    return seq({ kind: "conditional", cond: truthy(left), ty: e.ty,
      then: e.op === "&&" ? e.right : left, else: e.op === "&&" ? left : e.right }, out);
  }
  const operands: TExpr[] = [];
  mapOperands(e, operand => { operands.push(operand); return operand; });
  let next = 0;
  return mapOperands(e, (operand, copy) => {
    const later = operands.slice(++next);
    return later.some(hasAssignment) ? save(operand, out, later, copy) : seq(operand, out);
  });
}

function seqStmt(s: TStmt): TStmt[] {
  const out: TStmt[] = [];
  switch (s.kind) {
    case "let": { const init = seq(s.init, out); return [...out, { ...s, init }]; }
    case "assign": { const value = seq(s.value, out); return [...out, { ...s, value }]; }
    case "return": { const value = seq(s.value, out); return [...out, { ...s, value }]; }
    case "expr": {
      const expr = seq(s.expr, out);
      return s.expr.kind === "assignment" ? out : [...out, { ...s, expr }];
    }
    case "if": {
      const cond = seq(s.cond, out);
      return [...out, { ...s, cond, then: seqStmts(s.then), else: seqStmts(s.else) }];
    }
    case "while": {
      const cond = seq(s.cond, out);
      const body = seqStmts(s.body);
      if (!out.length && !containsMethodCall(cond)) return [{ ...s, body }];
      // The test runs statements (an assignment, or a method call the backend
      // lifts) and can mutate state even when false. Head invariants apply
      // while testing; done_with applies after the final test.
      const name = freshName(`_testing${counter++}`);
      const testing = variable(name, bool);
      const done = s.doneWith ?? { kind: "bool", value: true, ty: bool };
      const implies = (left: TExpr, right: TExpr): TExpr => ({ kind: "binop", op: "==>", left, right, ty: bool });
      const num = (value: number, ty: Ty): TExpr => ({ kind: "num", value, ty });
      const d = s.decreases;
      return [
        { kind: "let", name, ty: bool, mutable: true, init: { kind: "bool", value: true, ty: bool } },
        { ...s, cond: testing, doneWith: done,
          invariants: [...s.invariants.map(inv => implies(testing, inv)), implies(not(testing), done)],
          decreases: d && { kind: "conditional", cond: testing, ty: d.ty,
            then: { kind: "binop", op: "+", left: d, right: num(1, d.ty), ty: d.ty }, else: num(0, d.ty) },
          body: [...out, { kind: "if", cond, then: body,
            else: [{ kind: "assign", target: name, value: { kind: "bool", value: false, ty: bool } }] }] },
      ];
    }
    case "forof": {
      let iterable = seq(s.iterable, out);
      if (containsMethodCall(iterable)) iterable = bind(iterable, out);
      return [...out, { ...s, iterable, body: seqStmts(s.body) }];
    }
    case "switch": {
      const expr = seq(s.expr, out);
      return [...out, { ...s, expr, cases: s.cases.map(c => ({ ...c, body: seqStmts(c.body) })),
        defaultBody: seqStmts(s.defaultBody) }];
    }
    case "someMatch":
      return [{ ...s, someBody: seqStmts(s.someBody), noneBody: seqStmts(s.noneBody) }];
    case "tagMatch":
      return [{ ...s, cases: s.cases.map(c => ({ ...c, body: seqStmts(c.body) })), fallthrough: seqStmts(s.fallthrough) }];
    default:
      return [s];
  }
}

function seqStmts(stmts: TStmt[]): TStmt[] { return stmts.flatMap(seqStmt); }

export function sequenceModule(mod: TModule): TModule {
  counter = 0;
  const fn = (f: TFunction): TFunction => ({ ...f, body: seqStmts(f.body) });
  return { ...mod, functions: mod.functions.map(fn),
    classes: mod.classes.map(c => ({ ...c, methods: c.methods.map(fn) })) };
}
