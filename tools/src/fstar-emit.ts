/**
 * Experimental pure F* backend. Consumes narrowed Typed IR directly: the
 * Dafny/Velvet lowering loses expression-valued callees and result binders.
 * Unsupported constructs fail before the command runner writes any artifacts.
 */
import type { TExpr, TStmt, TModule, TFunction, Ty } from "./typedir.js";
import { exactIntegerLiteral } from "./ir.js";

// Injective encoding, disjoint from compiler-owned ls_* binders. In particular,
// uppercase TS names are values, not F* constructors; '_' and '$' cannot collide.
function name(s: string): string {
  return "v_" + [...s].map(c => /[A-Za-z0-9]/.test(c) ? c : `_${c.codePointAt(0)!.toString(16)}_`).join("");
}

interface Context {
  vars: Map<string, Ty>;
  types: Set<string>;
  deps: Set<string>;
}

const MAP = `let rec ls_map (#a:Type) (#b:Type) (f:a -> Tot b) (xs:list a)
  : Tot (ys:list b{FStar.List.Tot.length ys == FStar.List.Tot.length xs})
    (decreases xs) =
  match xs with
  | [] -> []
  | x::tl -> f x :: ls_map f tl
`;

const FILTER = `let rec ls_filter (#a:Type) (f:a -> Tot bool) (xs:list a)
  : Tot (ys:list a{FStar.List.Tot.length ys <= FStar.List.Tot.length xs})
    (decreases xs) =
  match xs with
  | [] -> []
  | x::tl -> if f x then x :: ls_filter f tl else ls_filter f tl
`;

export function emitFstarFile(mod: TModule, moduleName: string): string {
  const fail = (message: string): never => { throw new Error(`F* (${mod.file}): ${message}`); };
  if (mod.classes.length) fail("classes are not supported by the pure backend");
  if (mod.externs.length) fail("externs are not supported by the pure backend (including cross-file calls)");
  if (mod.functions.some(f => f.autohavoc)) fail("autohavoc is not supported by the pure backend");
  // Algebraic data support is a later extension. Aliases over this subset are
  // expanded below, including function aliases which shared resolve preserves.
  for (const d of mod.typeDecls) {
    if (d.kind !== "alias" || !d.aliasOfTy || d.typeParams?.length) {
      fail(`type declaration '${d.name}' is not supported yet (only non-generic aliases)`);
    }
  }
  const aliases = new Map(mod.typeDecls.map(d => [d.name, d.aliasOfTy!]));
  const functions = new Map(mod.functions.map(f => [f.name, f]));
  const constants = new Map(mod.constants.map(c => [c.name, c.ty]));
  const helpers = new Set<string>();

  function expand(t: Ty, seen = new Set<string>()): Ty {
    if (t.kind !== "user" || !aliases.has(t.name)) return t;
    if (seen.has(t.name)) fail(`recursive type alias '${t.name}' is not supported`);
    return expand(aliases.get(t.name)!, new Set([...seen, t.name]));
  }
  function type(t: Ty, ctx: Context): string {
    t = expand(t);
    switch (t.kind) {
      case "int": return "int";
      case "nat": return "nat";
      case "bool": return "bool";
      case "array": return `(list ${type(t.elem, ctx)})`;
      case "fn": return `(${t.params.length ? t.params.map(p => type(p, ctx)).join(" -> ") : "unit"} -> Tot ${type(t.result, ctx)})`;
      case "user": if (ctx.types.has(t.name)) return name(t.name); break;
    }
    return fail(`unsupported type ${t.kind === "user" ? t.name : t.kind}`);
  }
  function fnType(f: TFunction): Ty { return { kind: "fn", params: f.params.map(p => p.ty), result: f.returnTy }; }
  function substitute(t: Ty, bindings: Map<string, Ty>): Ty {
    t = expand(t);
    if (t.kind === "user") return bindings.get(t.name) ?? t;
    if (t.kind === "array") return { ...t, elem: substitute(t.elem, bindings) };
    if (t.kind === "fn") return { ...t, params: t.params.map(p => substitute(p, bindings)), result: substitute(t.result, bindings) };
    return t;
  }
  function infer(pattern: Ty, actual: Ty, parameters: Set<string>, bindings: Map<string, Ty>): void {
    pattern = expand(pattern); actual = expand(actual);
    if (pattern.kind === "user" && parameters.has(pattern.name) && actual.kind !== "unknown") {
      if (!bindings.has(pattern.name)) bindings.set(pattern.name, actual);
    } else if (pattern.kind === "array" && actual.kind === "array") {
      infer(pattern.elem, actual.elem, parameters, bindings);
    } else if (pattern.kind === "fn" && actual.kind === "fn") {
      pattern.params.forEach((p, i) => { if (actual.kind === "fn" && actual.params[i]) infer(p, actual.params[i], parameters, bindings); });
      infer(pattern.result, actual.result, parameters, bindings);
    }
  }
  function typeOf(e: TExpr, ctx: Context): Ty {
    if (e.kind === "var") {
      if (ctx.vars.has(e.name)) return expand(ctx.vars.get(e.name)!);
      if (functions.has(e.name)) return fnType(functions.get(e.name)!);
      if (constants.has(e.name)) return expand(constants.get(e.name)!);
    }
    if (e.kind === "call" && e.fn.kind === "field") {
      const recv = typeOf(e.fn.obj, ctx);
      if (recv.kind === "array") {
        if (e.fn.field === "filter") return recv;
        if (e.fn.field === "every" || e.fn.field === "some") return { kind: "bool" };
        if (e.fn.field === "reduce" && e.args.length === 2) return typeOf(e.args[1], ctx);
        if (e.fn.field === "map" && e.args.length) {
          const cb = typeOf(e.args[0], ctx);
          if (cb.kind === "fn") return { kind: "array", elem: cb.result };
        }
      }
    }
    if (e.kind === "call") {
      const f = typeOf(e.fn, ctx);
      if (f.kind === "fn") {
        const decl = e.fn.kind === "var" && !ctx.vars.has(e.fn.name) ? functions.get(e.fn.name) : undefined;
        const bindings = new Map<string, Ty>();
        if (decl?.typeParams.length) f.params.forEach((p, i) => {
          if (e.args[i]) infer(p, typeOf(e.args[i], ctx), new Set(decl.typeParams), bindings);
        });
        return substitute(f.result, bindings);
      }
    }
    if (e.kind === "lambda" && e.ty.kind === "unknown") {
      const lc = bind(ctx, e.params.map(p => [p.name, p.ty]));
      const ret = e.body.at(-1);
      if (ret?.kind === "return") return { kind: "fn", params: e.params.map(p => p.ty), result: typeOf(ret.value, lc) };
    }
    return expand(e.ty);
  }
  function bind(ctx: Context, entries: [string, Ty][]): Context {
    return { ...ctx, vars: new Map([...ctx.vars, ...entries]) };
  }
  function integral(t: Ty): boolean { t = expand(t); return t.kind === "int" || t.kind === "nat"; }
  function bool(e: TExpr, ctx: Context): string {
    const t = typeOf(e, ctx);
    if (t.kind === "bool") return expr(e, ctx);
    if (integral(t)) return `(${expr(e, ctx)} <> 0)`;
    return fail(`unsupported condition of type ${t.kind}`);
  }
  function prop(e: TExpr, ctx: Context): string {
    if (e.kind === "forall" || e.kind === "exists") {
      return `(${e.kind} (${name(e.var)}:${type(e.varTy, ctx)}). ${prop(e.body, bind(ctx, [[e.var, e.varTy]]))})`;
    }
    if (e.kind === "binop") {
      const op = ({ "&&": "/\\", "||": "\\/", "==>": "==>", "<==>": "<==>" } as Record<string, string>)[e.op];
      if (op) return `(${prop(e.left, ctx)} ${op} ${prop(e.right, ctx)})`;
      if (["===", "!==", "==", "!="].includes(e.op)) {
        if (typeOf(e.left, ctx).kind === "fn" || typeOf(e.right, ctx).kind === "fn") fail("function identity equality is not modeled; use pointwise specifications");
        return `(${expr(e.left, ctx)} ${e.op.includes("!") ? "=!= " : "== "}${expr(e.right, ctx)})`;
      }
      if (e.op === "in") {
        const rhs = typeOf(e.right, ctx);
        if (rhs.kind !== "array") fail("membership requires an array");
        return `(FStar.List.Tot.memP ${expr(e.left, ctx)} ${expr(e.right, ctx)})`;
      }
    }
    if (e.kind === "unop" && e.op === "!") return `(not (${prop(e.expr, ctx)}))`;
    return bool(e, ctx);
  }
  function expr(e: TExpr, ctx: Context): string {
    switch (e.kind) {
      case "var": {
        if (e.name === "\\result" && ctx.vars.has(e.name)) return "ls_result";
        if (ctx.vars.has(e.name)) return name(e.name);
        if (functions.has(e.name) || constants.has(e.name)) {
          ctx.deps.add(e.name);
          return name(e.name);
        }
        return fail(`unbound value '${e.name}' (only verified functions, parameters, and constants are allowed)`);
      }
      case "num":
        if (!Number.isSafeInteger(e.value)) fail("number literals must be safe integers; use bigint for larger literals");
        return `(${exactIntegerLiteral(e)})`;
      case "bigint": return `(${e.value})`;
      case "bool": return String(e.value);
      case "binop": {
        if (e.op === "&&" || e.op === "||") {
          // JS && and || return operands; this subset admits boolean operands.
          if (typeOf(e.left, ctx).kind !== "bool" || typeOf(e.right, ctx).kind !== "bool") fail("&& and || require boolean operands");
          return `(${bool(e.left, ctx)} ${e.op} ${bool(e.right, ctx)})`;
        }
        if (["===", "!==", "==", "!="].includes(e.op)) {
          const l = typeOf(e.left, ctx), r = typeOf(e.right, ctx);
          if (!((integral(l) && integral(r)) || (l.kind === "bool" && r.kind === "bool"))) fail("runtime equality requires numbers or booleans; reference equality is not modeled");
          return `(${expr(e.left, ctx)} ${e.op.includes("!") ? "<>" : "="} ${expr(e.right, ctx)})`;
        }
        if (["+", "-", "*", "<", "<=", ">", ">="].includes(e.op)) {
          if (!integral(typeOf(e.left, ctx)) || !integral(typeOf(e.right, ctx))) fail(`operator '${e.op}' requires integers`);
          return `(${expr(e.left, ctx)} ${e.op} ${expr(e.right, ctx)})`;
        }
        return fail(`operator '${e.op}' is not supported`);
      }
      case "unop":
        if (e.op === "!") return `(not ${bool(e.expr, ctx)})`;
        if (e.op === "-" && integral(typeOf(e.expr, ctx))) return `(- ${expr(e.expr, ctx)})`;
        return fail(`unary operator '${e.op}' is not supported`);
      case "field":
        if (e.field === "length" && typeOf(e.obj, ctx).kind === "array") return `(FStar.List.Tot.length ${expr(e.obj, ctx)})`;
        return fail(`field '${e.field}' is not supported`);
      case "index":
        if (typeOf(e.obj, ctx).kind !== "array" || !integral(typeOf(e.idx, ctx))) fail("indexing requires an array and an integer index");
        return `(FStar.List.Tot.index ${expr(e.obj, ctx)} ${expr(e.idx, ctx)})`;
      case "arrayLiteral":
        if (e.ty.kind !== "array") fail("only homogeneous arrays are supported");
        return `[${e.elems.map(x => expr(x, ctx)).join("; ")}]`;
      case "conditional": return `(if ${bool(e.cond, ctx)} then ${expr(e.then, ctx)} else ${expr(e.else, ctx)})`;
      case "lambda": {
        const params = e.params.map(p => `(${name(p.name)}:${type(p.ty, ctx)})`).join(" ") || "()";
        return `(fun ${params} ->\n${indent(block(e.body, bind(ctx, e.params.map(p => [p.name, p.ty]))))})`;
      }
      case "call": {
        if (e.fn.kind === "field") return builtin(e, ctx);
        const ft = typeOf(e.fn, ctx);
        if (ft.kind !== "fn") return fail(`call target has unsupported type '${ft.kind}'`);
        if (ft.params.length !== e.args.length) fail(`expected ${ft.params.length} arguments, got ${e.args.length}; optional/rest arguments are not supported`);
        // Every operand occurs once. Evaluation order is immaterial within
        // this total, effect-free subset; avoid lets whose inferred refinement
        // types could let compiler-owned binders escape into enclosing calls.
        return apply(expr(e.fn, ctx), e.args.map(x => expr(x, ctx)));
      }
      default: return fail(`expression '${e.kind}' is not supported by the pure backend`);
    }
  }
  function apply(f: string, args: string[]): string {
    return `(${f} ${args.length ? args.map(a => `(${a})`).join(" ") : "()"})`;
  }
  function builtin(e: Extract<TExpr, { kind: "call" }>, ctx: Context): string {
    const fn = e.fn;
    if (fn.kind !== "field" || typeOf(fn.obj, ctx).kind !== "array") return fail("only supported array builtins may be called as methods");
    const methods: Record<string, [string, number, number]> = {
      map: ["ls_map", 1, 1], filter: ["ls_filter", 1, 1],
      every: ["FStar.List.Tot.for_all", 1, 1], some: ["FStar.List.Tot.existsb", 1, 1],
      reduce: ["FStar.List.Tot.fold_left", 2, 2],
    };
    const spec = methods[fn.field];
    if (!spec) return fail(`array method '${fn.field}' is not supported`);
    const [target, argc, arity] = spec;
    if (e.args.length !== argc) fail(`.${fn.field} expects ${argc} arguments; thisArg and omitted reduce initial values are not supported`);
    const cb = e.args[0];
    const cbType = typeOf(cb, ctx);
    const cbArity = cb.kind === "lambda" ? cb.params.length : cbType.kind === "fn" ? cbType.params.length : -1;
    if (cbArity !== arity) fail(`.${fn.field} requires a ${arity}-parameter callback; index/array callback arguments are not supported`);
    if (target === "ls_map" || target === "ls_filter") helpers.add(target);
    // Pure/total receiver and arguments, each occurring exactly once.
    const recv = expr(fn.obj, ctx);
    const args = e.args.map(a => expr(a, ctx));
    return apply(target, [...args, recv]);
  }
  function block(stmts: TStmt[], ctx: Context): string {
    if (!stmts.length) return fail("every control-flow path must return a value");
    const [first, ...rest] = stmts;
    switch (first.kind) {
      case "return": return expr(first.value, ctx);
      case "let": {
        if (first.mutable && first.ty.kind !== "array") fail(`mutable local '${first.name}' is not supported`);
        const value = expr(first.init, ctx);
        // The frontend marks even const arrays mutable; all mutation nodes and
        // mutating builtins are rejected, including those in nested lambdas.
        const inferred = typeOf(first.init, ctx);
        const t = inferred.kind === "unknown" ? first.ty : inferred;
        const annotation = t.kind === "unknown" ? "" : ` : ${type(t, ctx)}`;
        return `let ${name(first.name)}${annotation} = ${value} in\n${block(rest, bind(ctx, [[first.name, t]]))}`;
      }
      case "if": {
        // Concatenating a fallthrough branch's locals with the continuation
        // would extend their lexical scope. Only empty or returning branches
        // are supported until lowering has explicit continuation environments.
        if ((first.then.length && !returns(first.then)) || (first.else.length && !returns(first.else))) {
          fail("nonempty if branches must return; branch fallthrough is not supported yet");
        }
        return `if ${bool(first.cond, ctx)} then (\n${indent(block([...first.then, ...rest], ctx))}\n) else (\n${indent(block([...first.else, ...rest], ctx))}\n)`;
      }
      case "assert":
        if (first.assumed) fail("assume is not supported");
        return `assert (${prop(first.expr, ctx)});\n${block(rest, ctx)}`;
      default: return fail(`statement '${first.kind}' is not supported by the pure backend`);
    }
  }

  const declarations = new Map<string, { text: string; deps: Set<string>; fn: boolean }>();
  for (const c of mod.constants) {
    // Exported/escaped array constants can be mutated before a verified call.
    // Model arrays only as inputs and locals until module state is represented.
    if (!integral(c.ty) && expand(c.ty).kind !== "bool") fail("only scalar module constants are supported");
    const ctx: Context = { vars: new Map(), types: new Set(), deps: new Set() };
    declarations.set(c.name, { text: `let ${name(c.name)} : ${type(c.ty, ctx)} = ${expr(c.value, ctx)}\n`, deps: ctx.deps, fn: false });
  }
  for (const f of mod.functions) {
    if (f.typeParams.some(t => !/^[A-Za-z_$][\w$]*$/.test(t))) fail(`${f.name}: constrained type parameters are not supported`);
    if (f.typeParams.some(t => aliases.has(t))) fail(`${f.name}: generic parameters shadowing type aliases are not supported`);
    const ctx: Context = { vars: new Map(f.params.map(p => [p.name, p.ty])), types: new Set(f.typeParams), deps: new Set() };
    const tp = f.typeParams.map(t => `(#${name(t)}:Type)`).join(" ");
    const params = f.params.map(p => `(${name(p.name)}:${type(p.ty, ctx)})`).join(" ") || "()";
    const result = type(f.returnTy, ctx);
    const pre = f.requires.map(e => prop(e, ctx)).join(" /\\ ") || "True";
    const postCtx = bind(ctx, [["\\result", f.returnTy]]);
    const post = f.ensures.map(e => prop(e, postCtx)).join(" /\\ ") || "True";
    const comp = f.requires.length || f.ensures.length ? `Pure ${result}\n    (requires (${pre}))\n    (ensures (fun ls_result -> ${post}))` : `Tot ${result}`;
    const decreases = f.decreases ? `\n    (decreases ${expr(f.decreases, ctx)})` : "";
    const body = block(f.body, ctx);
    const recursive = ctx.deps.has(f.name);
    declarations.set(f.name, { text: `let ${recursive ? "rec " : ""}${name(f.name)} ${[tp, params].filter(Boolean).join(" ")}\n  : ${comp}${decreases} =\n${indent(body)}\n`, deps: ctx.deps, fn: true });
  }
  const ordered: string[] = [], done = new Set<string>(), active = new Set<string>();
  function visit(id: string): void {
    if (done.has(id)) return;
    if (active.has(id)) fail(`mutually recursive declarations involving '${id}' are not supported yet`);
    active.add(id);
    const d = declarations.get(id)!;
    for (const dep of d.deps) {
      if (dep === id && d.fn) continue;
      if (!declarations.has(dep)) fail(`missing declaration '${dep}'`);
      visit(dep);
    }
    active.delete(id); done.add(id); ordered.push(d.text);
  }
  for (const id of declarations.keys()) visit(id);
  return `// Generated by lsc. Program source: ${mod.file.split(/[\\/]/).pop()!.replace(/[\r\n]/g, " ")}\n// Add proofs in the .fst; regenerate with lsc regen --backend=fstar.\nmodule ${moduleName}\n\n${[helpers.has("ls_map") ? MAP : "", helpers.has("ls_filter") ? FILTER : "", ...ordered].filter(Boolean).join("\n")}`;
}

function indent(s: string): string { return s.split("\n").map(line => `  ${line}`).join("\n"); }

function returns(stmts: TStmt[]): boolean {
  return stmts.some(s => s.kind === "return" || (s.kind === "if" && returns(s.then) && returns(s.else)));
}
