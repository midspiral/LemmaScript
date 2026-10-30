/** Value dependencies of extracted code, including its proof annotations.
 * Walk the verification model so skipped/havoced code contributes no dependencies.
 * Keep binders in scope: a local named like a module constant does not use it. */
import type { RawExpr, RawFunction, RawStmt } from "./rawir.js";
import { parseExpr } from "./specparser.js";

class ValueReferences {
  readonly names = new Set<string>();
  readonly fields = new Set<string>();
  wholeThis = false;

  expr(e: RawExpr, bound: ReadonlySet<string> = new Set()): void {
    const visit = (expr: RawExpr) => this.expr(expr, bound);
    switch (e.kind) {
      case "var":
        // Compound assignments/increments can encode a path as a var name.
        if (e.name.includes(".") || e.name.includes("[")) {
          this.spec(e.name, bound);
        } else if (!bound.has(e.name)) {
          this.names.add(e.name);
          if (e.name === "this") this.wholeThis = true;
        }
        return;
      case "binop": visit(e.left); visit(e.right); return;
      case "unop": case "nonNull": visit(e.expr); return;
      case "call": visit(e.fn); e.args.forEach(visit); return;
      case "field":
        this.fields.add(e.field);
        // A direct field read does not require the whole receiver's shape.
        if (e.obj.kind !== "var" || e.obj.name !== "this") visit(e.obj);
        return;
      case "index":
        if (e.idx.kind === "str") this.fields.add(e.idx.value);
        visit(e.obj); visit(e.idx); return;
      case "record":
        if (e.spread) visit(e.spread);
        e.fields.forEach(f => visit(f.value));
        return;
      case "recordMerge": visit(e.base); visit(e.override); return;
      case "arrayLiteral": e.elems.forEach(visit); return;
      case "emptyCollection": e.initElems?.forEach(visit); return;
      case "conditional": visit(e.cond); visit(e.then); visit(e.else); return;
      case "nullish": visit(e.left); visit(e.right); return;
      case "optChain":
        visit(e.obj);
        for (const step of e.chain) {
          if (step.kind === "field") this.fields.add(step.name);
          if (step.kind === "call") step.args.forEach(visit);
          if (step.kind === "index") visit(step.idx);
        }
        return;
      case "lambda": {
        const scope = new Set([...bound, ...e.params.map(p => p.name)]);
        if (Array.isArray(e.body)) this.block(e.body, scope);
        else this.expr(e.body, scope);
        return;
      }
      case "forall": case "exists":
        this.expr(e.body, new Set([...bound, e.var]));
        return;
      case "num": case "bigint": case "str": case "bool": case "result": case "havoc":
        return;
    }
  }

  spec(text: string | null, bound: ReadonlySet<string>): void {
    if (text !== null) this.expr(parseExpr(text), bound);
  }

  block(stmts: RawStmt[], outer: ReadonlySet<string>): void {
    const bound = new Set(outer);
    for (const s of stmts) {
      switch (s.kind) {
        case "let":
          this.expr(s.init, bound);
          bound.add(s.name);
          break;
        case "ghostLet":
          // These constructors have type arguments but no value arguments;
          // resolve.ts handles them separately from the spec parser too.
          if (!/^new\s+(Set|Map)<(.+)>\(\)$/.test(s.init)) this.spec(s.init, bound);
          bound.add(s.name);
          break;
        case "assign":
          this.expr({ kind: "var", name: s.target }, bound);
          this.expr(s.value, bound);
          break;
        case "ghostAssign":
          this.expr({ kind: "var", name: s.target }, bound);
          this.spec(s.value, bound);
          break;
        case "return": this.expr(s.value, bound); break;
        case "expr": this.expr(s.expr, bound); break;
        case "assert": this.spec(s.expr, bound); break;
        case "if":
          this.expr(s.cond, bound);
          this.block(s.then, bound);
          this.block(s.else, bound);
          break;
        case "while":
          this.expr(s.cond, bound);
          s.invariants.forEach(spec => this.spec(spec, bound));
          this.spec(s.decreases, bound);
          this.spec(s.doneWith, bound);
          this.block(s.body, bound);
          break;
        case "forof": {
          this.expr(s.iterable, bound);
          const scope = new Set([...bound, ...s.names]);
          s.invariants.forEach(spec => this.spec(spec, scope));
          this.spec(s.doneWith, scope);
          this.block(s.body, scope);
          break;
        }
        case "switch":
          this.expr(s.expr, bound);
          s.cases.forEach(c => this.block(c.body, bound));
          this.block(s.defaultBody, bound);
          break;
        case "break": case "continue": case "throw": break;
      }
    }
  }
}

export function functionValueReferences(fn: Pick<RawFunction, "params" | "requires" | "ensures" | "decreases" | "body">) {
  const refs = new ValueReferences();
  const bound = new Set(fn.params.map(p => p.name));
  for (const spec of [...fn.requires, ...fn.ensures, fn.decreases]) refs.spec(spec, bound);
  refs.block(fn.body, bound);
  return refs;
}

export function expressionValueReferences(expr: RawExpr) {
  const refs = new ValueReferences();
  refs.expr(expr);
  return refs;
}
