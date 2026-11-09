import type { AsyncFunction, AsyncModule, AsyncTerm } from "./async-lower.js";
import type { TExpr, Ty } from "./typedir.js";
import { ASYNC_RUNTIME } from "./async-runtime.js";

export function emitAsyncModule(mod: AsyncModule, quote: (s: string) => string, moduleName: string): string {
  const functions = new Map(mod.functions.map(f => [f.name, f]));
  const fail = (why: string): never => { throw new Error(`async ${mod.file}: ${why}`); };
  const type = (ty: Ty): string => {
    switch (ty.kind) {
      case "nat": case "int": return "int";
      case "bool": return "bool";
      case "string": return "string";
      case "promise": return "Promise";
      case "void": case "unknown": return "Value";
      default: return fail(`unsupported async type '${ty.kind}'`);
    }
  };
  const tag = (ty: Ty): string => {
    switch (ty.kind) {
      case "nat": case "int": return ty.big ? "BigIntValue" : "NumberValue";
      case "bool": return "BooleanValue";
      case "string": return "StringValue";
      case "void": return "UndefinedValue";
      default: return fail(`unsupported fulfillment type '${ty.kind}'`);
    }
  };
  const payload = (v: string, ty: Ty): string => {
    switch (ty.kind) {
      case "nat": case "int": return `${v}.${ty.big ? "bigint" : "number"}`;
      case "bool": return `${v}.boolean`;
      case "string": return `${v}.text`;
      case "void": case "unknown": return v;
      default: return fail(`unsupported fulfillment type '${ty.kind}'`);
    }
  };
  const box = (e: TExpr, resultTy?: Ty): string => e.ty.kind === "unknown" ? expr(e, resultTy)
    : e.ty.kind === "void" ? "UndefinedValue" : `${tag(e.ty)}(${expr(e, resultTy)})`;
  const expr = (e: TExpr, resultTy?: Ty): string => {
    switch (e.kind) {
      case "var": return e.name === "undefined" ? "UndefinedValue" : e.name === "\\result"
        ? payload("outcome.value", resultTy ?? fail("result outside a postcondition")) : e.name;
      case "num":
        if (!Number.isSafeInteger(e.value)) return fail("async numeric literals must be safe integers");
        return `${e.value}`;
      case "bigint": return e.value;
      case "bool": return String(e.value);
      case "str": return quote(e.value);
      case "unop":
        if (e.op === "!" && e.expr.ty.kind === "bool" || e.op === "-" && ["nat", "int"].includes(e.expr.ty.kind))
          return `(${e.op}${expr(e.expr, resultTy)})`;
        return fail(`unsupported unary operator '${e.op}'`);
      case "binop": {
        const left = expr(e.left, resultTy), right = expr(e.right, resultTy);
        if (e.op === "===" || e.op === "!==") {
          const op = e.op === "===" ? "==" : "!=";
          if (e.left.ty.kind === "promise" && e.right.ty.kind === "promise") return `(${left}.id ${op} ${right}.id)`;
          if (e.left.ty.kind === "promise" && e.right.ty.kind === "unknown" || e.right.ty.kind === "promise" && e.left.ty.kind === "unknown")
            return fail("comparison with a caught unknown value may hide a promise identity");
          if (e.left.ty.kind === "promise" || e.right.ty.kind === "promise") return e.op === "===" ? "false" : "true";
          return `(${box(e.left, resultTy)} ${op} ${box(e.right, resultTy)})`;
        }
        if (["&&", "||", "==>", "<==>"].includes(e.op) && e.left.ty.kind === "bool" && e.right.ty.kind === "bool")
          return `(${left} ${e.op} ${right})`;
        const numeric = (ty: Ty) => ty.kind === "nat" || ty.kind === "int";
        if (["+", "-", "*"].includes(e.op) && numeric(e.left.ty) && numeric(e.right.ty)
            && !!(e.left.ty as { big?: boolean }).big !== !!(e.right.ty as { big?: boolean }).big)
          return fail("mixed bigint/number arithmetic is not supported");
        if (["+", "-", "*", "<", ">", "<=", ">="].includes(e.op) && numeric(e.left.ty) && numeric(e.right.ty))
          return `(${left} ${e.op} ${right})`;
        if (e.op === "+" && e.left.ty.kind === "string" && e.right.ty.kind === "string") return `(${left} + ${right})`;
        return fail(`operator '${e.op}' or its operands require additional async semantics`);
      }
      default: return fail(`unexpected '${e.kind}' after continuation lowering`);
    }
  };
  const roots = (args: TExpr[]) => `{${args.filter(a => a.ty.kind === "promise").map(a => expr(a)).join(", ")}}`;
  const vars = (f: AsyncFunction): TExpr[] => f.params.map(p => ({ kind: "var", name: p.name, ty: p.ty }));
  const args = (f: AsyncFunction) => f.params.map(p => p.name).join(", ");
  const params = (f: AsyncFunction) => f.params.map(p => `${p.name}: ${type(p.ty)}`).join(", ");
  const native = (p: TExpr) => p.ty.kind === "promise"
    ? `(forall o: Outcome :: ${expr(p)}.accepts(o) && o.Fulfilled? ==> o.value.${tag(p.ty.value)}?)` : "true";
  const pre = (f: AsyncFunction) => [...f.params.filter(p => p.ty.kind === "promise").map(p => native({ kind: "var", name: p.name, ty: p.ty })),
    ...f.requires.map(e => expr(e))].join(" && ") || "true";
  const term = (c: AsyncTerm, indent = 4, known: string[] = []): string => {
    const pad = " ".repeat(indent), nested = (n: AsyncTerm) => term(n, indent + 2, known);
    switch (c.kind) {
      case "done": return `Finished(${c.rejected ? "Rejected" : "Fulfilled"}(${box(c.value)}))`;
      case "adopt": return `Adopt(${expr(c.promise)})`;
      case "let": return `(var ${c.name}: ${type(c.ty)} := ${expr(c.value)};\n${pad}${term(c.next, indent, known)})`;
      case "if":
        if (c.cond.ty.kind !== "bool") return fail("async branch conditions must be boolean");
        return `(if ${expr(c.cond)} then\n${pad}  ${nested(c.then)}\n${pad}else\n${pad}  ${nested(c.else)})`;
      case "check": return `Check(${expr(c.cond)},\n${pad}  ${nested(c.next)})`;
      case "create": {
        const outcome = `${c.rejected ? "Rejected" : "Fulfilled"}(${box(c.value)})`;
        return `Create(${outcome},\n${pad}  (${c.name}: Promise) => `
          + `${term(c.next, indent + 2, [...known, c.name])})`;
      }
      case "wait": {
        const outcome = `outcome_${c.name}`;
        const never = c.ty.kind === "user" && c.ty.name === "never";
        const fulfilled = never ? "Fault" : `(if ${outcome}.Fulfilled? && ${outcome}.value.${tag(c.ty)}? then\n${pad}    `
          + `(var ${c.name}: ${type(c.ty)} := ${payload(`${outcome}.value`, c.ty)}; ${nested(c.next)})\n${pad}  else Fault)`;
        return `Suspend(${expr(c.promise)},\n${pad}  (${outcome}: Outcome) =>\n${pad}  if ${outcome}.Rejected? then\n${pad}    `
          + `(var ${c.errorName}: Value := ${outcome}.reason; ${nested(c.rejected)})\n${pad}  else ${fulfilled}, ${c.line})`;
      }
      case "call": {
        const f = functions.get(c.callee)!;
        const actual = c.args.map(a => expr(a)).join(", ");
        return `Check(${f.name}_requires(${actual}), Spawn(${f.name}_body(${actual}), ${f.name}_post(${actual}), ${roots(c.args)},\n${pad}  `
          + `(${c.name}: Promise) => ${term(c.next, indent + 2, [...known, c.name])}))`;
      }
    }
  };
  const emitted = mod.functions.map(f => {
    const input = args(f), ps = params(f), root = roots(vars(f));
    const post = [`outcome.value.${tag(f.valueTy)}?`, ...f.ensures.map(e => expr(e, f.valueTy))].join(" && ");
    let proofSerial = 0;
    const proof = (c: AsyncTerm, ref: string, known: string[], depth: number): string => {
      const pad = " ".repeat(depth), nextId = () => `proof${proofSerial++}`;
      const state = `{${known.join(", ")}}`, contract = `${f.name}_post(${input})`;
      const correct = (at: string, ks = state) => `Correct(${at}, ${contract}, ${ks})`;
      const lines: string[] = [];
      const add = (s: string) => lines.push(pad + s);
      const recurse = (n: AsyncTerm, at: string, ks = known, d = depth) => lines.push(proof(n, at, ks, d));
      switch (c.kind) {
        case "done": case "adopt": break;
        case "let":
          add(`var ${c.name}: ${type(c.ty)} := ${expr(c.value)};`);
          recurse(c.next, ref);
          return lines.join("\n");
        case "if":
          add(`if ${expr(c.cond)} {`); recurse(c.then, ref, known, depth + 2);
          add("} else {"); recurse(c.else, ref, known, depth + 2); add("}");
          break;
        case "check":
          add(`assert ${expr(c.cond)};`);
          add(`assert ${ref}.Check?;`);
          recurse(c.next, `${ref}.next`);
          break;
        case "create": {
          const outcome = `${c.rejected ? "Rejected" : "Fulfilled"}(${box(c.value)})`;
          const after = `${state} + {${c.name}}`;
          add(`assert ${ref}.Create?;`);
          add(`forall ${c.name}: Promise | ${c.name}.accepts == Exact(${outcome}) && NewTo(${c.name}, ${state})`);
          add(`  ensures ${correct(`${ref}.created(${c.name})`, after)}`);
          add("{");
          lines.push(`${pad}  assert ${after} == {${[...known, c.name].join(", ")}};`);
          const local = nextId();
          lines.push(`${pad}  var ${local} := ${ref}.created(${c.name});`);
          recurse(c.next, local, [...known, c.name], depth + 2);
          add("}");
          break;
        }
        case "call": {
          const callee = functions.get(c.callee)!, actual = c.args.map(a => expr(a)).join(", ");
          const childPost = `${callee.name}_post(${actual})`;
          const after = `${state} + {${c.name}}`;
          add(`assert ${callee.name}_requires(${actual});`);
          add(`${callee.name}_ensures(${actual});`);
          add(`assert ${ref}.Check? && ${ref}.next.Spawn?;`);
          add(`assert ${ref}.next.post == ${childPost};`);
          add(`forall ${c.name}: Promise | ${c.name}.accepts == ${ref}.next.post && NewTo(${c.name}, ${state})`);
          add(`  ensures ${correct(`${ref}.next.created(${c.name})`, after)}`);
          add("{");
          lines.push(`${pad}  assert ${after} == {${[...known, c.name].join(", ")}};`);
          const local = nextId();
          lines.push(`${pad}  var ${local} := ${ref}.next.created(${c.name});`);
          recurse(c.next, local, [...known, c.name], depth + 2);
          add("}");
          add(`FoldCorrect(${ref}.next, ${contract}, ${state});`);
          add(`assert ${correct(`${ref}.next`)};`);
          break;
        }
        case "wait": {
          const outcome = `outcome_${c.name}`, local = nextId();
          add(`// await at source line ${c.line}`);
          add(`assert ${ref}.Suspend?;`);
          add(`forall ${outcome}: Outcome | Accepted(${expr(c.promise)}, ${outcome})`);
          add(`  ensures ${correct(`${ref}.resume(${outcome})`)}`);
          add("{");
          lines.push(`${pad}  var ${local} := ${ref}.resume(${outcome});`);
          lines.push(`${pad}  if ${outcome}.Rejected? {`);
          lines.push(`${pad}    var ${c.errorName}: Value := ${outcome}.reason;`);
          recurse(c.rejected, local, known, depth + 4);
          lines.push(`${pad}  } else {`);
          if (c.ty.kind === "user" && c.ty.name === "never") lines.push(`${pad}    assert false;`);
          else {
            lines.push(`${pad}    assert ${outcome}.Fulfilled? && ${outcome}.value.${tag(c.ty)}?;`);
            lines.push(`${pad}    var ${c.name}: ${type(c.ty)} := ${payload(`${outcome}.value`, c.ty)};`);
            recurse(c.next, local, known, depth + 4);
          }
          lines.push(`${pad}  }`);
          add("}");
          break;
        }
      }
      add(`FoldCorrect(${ref}, ${contract}, ${state});`);
      return lines.join("\n");
    };
    const initialKnown = f.params.filter(p => p.ty.kind === "promise").map(p => p.name);
    return `// ${mod.file.split("/").pop()}:${f.line} — ${f.sourceName}\n`
      + `ghost predicate ${f.name}_requires(${ps}) { ${pre(f)} }\n\n`
      + `function ${f.name}_post(${ps}): Outcome -> bool {\n  (outcome: Outcome) => outcome.Rejected? || (outcome.Fulfilled? && ${post})\n}\n\n`
      + `function ${f.name}_body(${ps}): Computation {\n  ${term(f.body, 2, initialKnown)}\n}\n\n`
      + `lemma ${f.name}_ensures(${ps})\n  requires ${f.name}_requires(${input})\n`
      + `  ensures Correct(${f.name}_body(${input}), ${f.name}_post(${input}), ${root})\n{\n`
      + `  var computation := ${f.name}_body(${input});\n${proof(f.body, "computation", initialKnown, 2)}\n}\n\n`
      + `method ${f.name}_start(s: State${ps ? ", " + ps : ""}) returns (t: State, result: Promise)\n`
      + `  requires Valid(s) && Knows(s, ${root}) && ${f.name}_requires(${input})\n`
      + `  ensures Valid(t) && Known(t, result) && result.id == |s.outcomes|\n`
      + `  ensures result.accepts == ${f.name}_post(${input})\n  decreases *\n{\n`
      + `  ${f.name}_ensures(${input});\n`
      + `  t, result := Start(s, ${f.name}_body(${input}), ${f.name}_post(${input}), ${root});\n}`;
  });
  return `\nmodule ${moduleName} {\n${ASYNC_RUNTIME}\n${emitted.join("\n\n")}\n}\n`;
}
