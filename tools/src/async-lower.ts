/** Continuation lowering for the closed, result-oriented async fragment.
 *
 * Each wait is a suspension point. Its continuation closes over immutable
 * versions of local bindings; assignment creates a new version. Keeping this
 * pass ahead of ordinary expression lifting preserves JS evaluation order.
 * Shared objects and unknown calls are rejected until their interference can
 * be represented. In particular, TS readonly/private is not an ownership proof.
 */
import type { TExpr, TFunction, TModule, TParam, TStmt, Ty } from "./typedir.js";

export type AsyncTerm =
  | { kind: "done"; rejected: boolean; value: TExpr }
  | { kind: "adopt"; promise: TExpr }
  | { kind: "let"; name: string; ty: Ty; value: TExpr; next: AsyncTerm }
  | { kind: "if"; cond: TExpr; then: AsyncTerm; else: AsyncTerm }
  | { kind: "check"; cond: TExpr; next: AsyncTerm }
  | { kind: "wait"; promise: TExpr; name: string; ty: Ty; next: AsyncTerm;
      errorName: string; rejected: AsyncTerm; line: number }
  | { kind: "create"; name: string; rejected: boolean; value: TExpr; next: AsyncTerm }
  | { kind: "call"; name: string; callee: string; args: TExpr[]; next: AsyncTerm };

export interface AsyncFunction {
  sourceName: string;
  name: string;
  line: number;
  params: TParam[];
  valueTy: Ty;
  requires: TExpr[];
  ensures: TExpr[];
  body: AsyncTerm;
}
export interface AsyncModule { file: string; functions: AsyncFunction[] }
type Env = Map<string, TExpr>;
type Continuation = (env: Env) => AsyncTerm;
type Exit = (value: TExpr, env: Env) => AsyncTerm;
interface Handlers { returned: Exit; thrown: Exit }
const unit: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
const variable = (name: string, ty: Ty): TExpr => ({ kind: "var", name, ty });

export function isAsyncScalar(ty: Ty): boolean {
  return ["bool", "int", "nat", "string", "void"].includes(ty.kind);
}
function isAsyncType(ty: Ty): boolean {
  return isAsyncScalar(ty) || ty.kind === "promise" && isAsyncScalar(ty.value);
}
function hasAsync(v: unknown): boolean {
  if (v === null || typeof v !== "object") return false;
  const kind = (v as { kind?: string }).kind;
  return kind === "await" || kind === "promise" || Object.values(v).some(hasAsync);
}

export function lowerAsyncModule(mod: TModule, backend: "dafny" | "lean"): { sync: TModule; async?: AsyncModule } {
  const selected = mod.functions.filter(f => f.isAsync);
  for (const cls of mod.classes) for (const fn of cls.methods) {
    if (fn.isAsync) throw new Error(`async ${cls.name}.${fn.name}: class methods require shared-state interference support`);
  }
  if (backend !== "dafny" && selected.length) throw new Error("async: use --backend=dafny; Lean async verification is not implemented");
  const names = new Map(selected.map((f, i) => [f.name, `f${i}_${f.name.replace(/[^a-zA-Z0-9_]/g, "_")}`]));
  const signatures = new Map(selected.map(f => [f.name, f]));
  for (const fn of mod.functions.filter(f => !f.isAsync)) {
    const callsAsync = (v: unknown): boolean => {
      if (!v || typeof v !== "object") return false;
      const e = v as TExpr;
      return e.kind === "call" && e.fn.kind === "var" && names.has(e.fn.name)
        || Object.values(v).some(callsAsync);
    };
    if (hasAsync(fn) || callsAsync(fn.body)) throw new Error(`async ${fn.name}: synchronous promise APIs are not supported yet`);
  }
  if (!selected.length) return { sync: mod };

  const edges = new Map<string, Set<string>>();
  const functions = selected.map(fn => {
    const calls = new Set<string>();
    edges.set(fn.name, calls);
    const fail = (why: string): never => { throw new Error(`${mod.file}:${fn.line ?? 1}: async ${fn.name}: ${why}`); };
    if (fn.autohavoc || fn.forcePure) fail("autohavoc/pure cannot abstract async effects");
    if (fn.typeParams.length) fail("generic async functions are not supported yet");
    if (fn.returnTy.kind !== "promise" || !isAsyncScalar(fn.returnTy.value)) fail("the return type must be Promise of a scalar or void");
    const valueTy = (fn.returnTy as Extract<Ty, { kind: "promise" }>).value;
    for (const p of fn.params) {
      if (!isAsyncType(p.ty)) fail(`parameter '${p.name}' needs shared-state/thenable support; only scalars and native scalar promises are supported`);
      if (p.ty.kind === "promise" && !fn.nativeParams?.includes(p.name)) fail(`add //@ native ${p.name} to explicitly require a native, unmodified promise at this boundary`);
    }
    for (const name of fn.nativeParams ?? []) {
      if (!fn.params.some(p => p.name === name && p.ty.kind === "promise")) fail(`//@ native ${name} must name a Promise parameter`);
    }
    const declared = new Set(fn.params.map(p => p.name));
    const checkBindings = (stmts: TStmt[]) => {
      for (const s of stmts) {
        const name = s.kind === "let" ? s.name : s.kind === "try" ? s.catchName : undefined;
        if (name) {
          if (declared.has(name)) fail(`shadowed binding '${name}' is not supported yet`);
          declared.add(name);
        }
        if (s.kind === "if") { checkBindings(s.then); checkBindings(s.else); }
        if (s.kind === "try") { checkBindings(s.body); checkBindings(s.catchBody ?? []); checkBindings(s.finallyBody); }
      }
    };
    checkBindings(fn.body);
    let serial = 0;
    const fresh = () => `v${serial++}`;
    const initial: Env = new Map();
    const constants = new Map(mod.constants.filter(c => isAsyncScalar(c.ty)).map(c => [c.name, c]));
    const resolvingConstants = new Set<string>();
    const params = fn.params.map((p, i) => ({ name: `p${i}`, ty: p.ty }));
    fn.params.forEach((p, i) => initial.set(p.name, variable(params[i].name, p.ty)));

    const atomic = (e: TExpr, env: Env, globalScope = false): TExpr => {
      switch (e.kind) {
        case "var": {
          if (e.name === "undefined" || e.name === "\\result") return e;
          const binding = env.get(e.name);
          if (binding) return binding;
          if (!globalScope && declared.has(e.name)) return fail(`binding '${e.name}' is used before initialization`);
          const constant = constants.get(e.name);
          if (constant && !resolvingConstants.has(e.name)) {
            if (constant.asyncUnsupported) return fail(constant.asyncUnsupported);
            resolvingConstants.add(e.name);
            // A global's initializer uses global scope, even if a parameter
            // happens to shadow a name mentioned in that initializer.
            const value = { ...atomic(constant.value, new Map(), true), ty: constant.ty };
            resolvingConstants.delete(e.name);
            return value;
          }
          return fail(`unbound/shared value '${e.name}' is not in the async fragment`);
        }
        case "bool": case "str": case "bigint": case "num": return e;
        case "binop": return { ...e, left: atomic(e.left, env, globalScope), right: atomic(e.right, env, globalScope) };
        case "unop": return { ...e, expr: atomic(e.expr, env, globalScope) };
        default: return fail(`${e.kind} is not a scalar contract expression`);
      }
    };
    const bind = (name: string, value: TExpr, env: Env, next: Continuation): AsyncTerm => {
      const id = fresh();
      const updated = new Map(env).set(name, variable(id, value.ty));
      return { kind: "let", name: id, ty: value.ty, value, next: next(updated) };
    };
    const expression = (e: TExpr, env: Env, h: Handlers, k: (value: TExpr) => AsyncTerm): AsyncTerm => {
      switch (e.kind) {
        case "var": case "bool": case "str": case "bigint": case "num": return k(atomic(e, env));
        case "unop": return expression(e.expr, env, h, value => k({ ...e, expr: value }));
        case "binop": return expression(e.left, env, h, left => {
          if (e.op === "&&" || e.op === "||") {
            if (left.ty.kind !== "bool" || e.right.ty.kind !== "bool") fail("short-circuit operands must be boolean");
            const rhs = expression(e.right, env, h, k);
            return { kind: "if", cond: left, then: e.op === "&&" ? rhs : k(left), else: e.op === "&&" ? k(left) : rhs };
          }
          return expression(e.right, env, h, right => k({ ...e, left, right }));
        });
        case "conditional": return expression(e.cond, env, h, cond => ({ kind: "if", cond,
          then: expression(e.then, env, h, k), else: expression(e.else, env, h, k) }));
        case "promise": return expression(e.value, env, h, value => {
          if (e.operation === "resolve" && value.ty.kind === "promise") return k(value);
          if (e.operation === "resolve" && value.ty.kind === "unknown")
            return fail("Promise.resolve of a caught unknown value may assimilate a thenable");
          if (!isAsyncScalar(value.ty) && value.ty.kind !== "unknown") fail("Promise.resolve/reject requires a scalar value");
          const name = fresh();
          return { kind: "create", name, rejected: e.operation === "reject", value,
            next: k(variable(name, e.ty)) };
        });
        case "await": return expression(e.expr, env, h, operand => {
          const wait = (promise: TExpr): AsyncTerm => {
            const name = fresh(), errorName = fresh();
            return { kind: "wait", promise, name, ty: e.ty, line: e.line,
              next: k(variable(name, e.ty)), errorName,
              rejected: h.thrown(variable(errorName, { kind: "unknown" }), env) };
          };
          if (operand.ty.kind === "promise") return wait(operand);
          if (!isAsyncScalar(operand.ty)) fail("await supports only native promises and scalar values");
          const name = fresh();
          return { kind: "create", name, rejected: false, value: operand,
            next: wait(variable(name, { kind: "promise", value: operand.ty })) };
        });
        case "call": {
          if (e.fn.kind !== "var" || !names.has(e.fn.name)) return fail("calls must target a selected async function; callback/external effects are not modeled");
          const callee = e.fn.name;
          if (env.has(callee)) return fail(`call to shadowed binding '${callee}' may invoke a callback`);
          if (e.args.length !== signatures.get(callee)!.params.length) fail("async calls must supply all parameters");
          calls.add(callee);
          const args = (i: number, values: TExpr[]): AsyncTerm => i === e.args.length
            ? (() => { const name = fresh(); return { kind: "call" as const, name, callee: names.get(callee)!, args: values, next: k(variable(name, e.ty)) }; })()
            : expression(e.args[i], env, h, value => args(i + 1, [...values, value]));
          return args(0, []);
        }
        default: return fail(`${e.kind} requires an effect or data model not supported by async lowering`);
      }
    };
    const statements = (ss: TStmt[], env: Env, h: Handlers, next: Continuation): AsyncTerm => {
      if (!ss.length) return next(env);
      const [s, ...rest] = ss;
      const tail: Continuation = updated => statements(rest, updated, h, next);
      switch (s.kind) {
        case "let": return expression(s.init, env, h, value => {
          if (!isAsyncType(value.ty)) fail(`local '${s.name}' is not a scalar or native promise`);
          return bind(s.name, value, env, tail);
        });
        case "assign":
          if (!env.has(s.target) || !declared.has(s.target)) return fail(`assignment to '${s.target}' may modify shared state`);
          return expression(s.value, env, h, value => bind(s.target, value, env, tail));
        case "return": return expression(s.value, env, h, value => h.returned(value, env));
        case "throw": return s.value ? expression(s.value, env, h, value => h.thrown(value, env)) : fail("missing thrown value");
        case "expr": return expression(s.expr, env, h, () => tail(env));
        case "assert":
          if (s.assumed) return fail("assume is not supported in async bodies");
          return { kind: "check", cond: atomic(s.expr, env), next: tail(env) };
        case "if": return expression(s.cond, env, h, cond => ({ kind: "if", cond,
          then: statements(s.then, new Map(env), h, tail), else: statements(s.else, new Map(env), h, tail) }));
        case "try": {
          const finish = (at: Env, cont: Continuation) => statements(s.finallyBody, at, h, cont);
          const caught: Handlers = {
            returned: (value, at) => finish(at, after => h.returned(value, after)),
            thrown: (value, at) => finish(at, after => h.thrown(value, after)),
          };
          const inner: Handlers = { ...caught, thrown: (value, at) => {
            if (!s.catchBody) return caught.thrown(value, at);
            const run: Continuation = caughtEnv => statements(s.catchBody!, caughtEnv, caught, after => finish(after, tail));
            return s.catchName ? bind(s.catchName, value, at, run) : run(at);
          } };
          return statements(s.body, env, inner, after => finish(after, tail));
        }
        default: return fail(`${s.kind} is not supported yet (async loops need suspension invariants)`);
      }
    };
    const returned: Exit = value => {
      if (value.ty.kind === "unknown") return fail("returning an unknown value may assimilate a thenable");
      return value.ty.kind === "promise" ? { kind: "adopt", promise: value } : { kind: "done", rejected: false, value };
    };
    const thrown: Exit = value => ({ kind: "done", rejected: true, value });
    return { sourceName: fn.name, name: names.get(fn.name)!, line: fn.line ?? 1, params, valueTy,
      requires: fn.requires.map(e => atomic(e, initial)), ensures: fn.ensures.map(e => atomic(e, initial)),
      body: statements(fn.body, initial, { returned, thrown }, at => returned(unit, at)) };
  });
  const visiting = new Set<string>(), visited = new Set<string>();
  const visit = (name: string) => {
    if (visiting.has(name)) throw new Error(`async ${name}: recursive async calls are not supported yet`);
    if (visited.has(name)) return;
    visiting.add(name);
    for (const target of edges.get(name) ?? []) visit(target);
    visiting.delete(name); visited.add(name);
  };
  selected.forEach(f => visit(f.name));
  return { sync: { ...mod, functions: mod.functions.filter(f => !f.isAsync) }, async: { file: mod.file, functions } };
}
