import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import ts from "typescript";
import { guardedReturn, guardedConditional, type Box } from "../fixtures/optional-guard-order.ts";
import { conditionFacts, extractConjunct } from "../src/condition-facts.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import type { TExpr } from "../src/typedir.ts";

const atom = (name: string): TExpr => ({ kind: "var", name, ty: { kind: "bool" } });
const and = (left: TExpr, right: TExpr): TExpr => ({ kind: "binop", op: "&&", left, right, ty: { kind: "bool" } });
const [a, b, c, noise] = ["a", "b", "c", "noise"].map(atom);
const parse = (e: TExpr) => e.kind === "var" && e.name !== "noise" ? e.name : null;

for (const [name, condition, expected] of [
  ["left-associated", and(and(a, b), c), { check: "a", restCond: and(b, c) }],
  ["right-associated", and(a, and(b, c)), { check: "a", restCond: and(b, c) }],
  ["nested after an unrelated guard", and(and(noise, a), b), { check: "a", restCond: and(noise, b) }],
  ["right subtree", and(noise, and(a, b)), { check: "a", restCond: and(noise, b) }],
  ["right operand only", and(and(noise, noise), a), { check: "a", restCond: and(noise, noise) }],
  ["no matching conjunct", and(noise, noise), null],
] as const) {
  test(`extracts the first matching conjunct in source order: ${name}`, () => {
    assert.deepEqual(extractConjunct(condition, parse), expected);
  });
}

function fixture() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/optional-guard-order.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

test("dependent optional checks unwrap the root before its fields in code and specs", () => {
  const inputs: (Box | undefined)[] = [undefined, {}, { inner: {} }, { inner: { value: 0 } }, { inner: { value: -7 } }];
  for (const fn of [guardedReturn, guardedConditional]) {
    assert.deepEqual(inputs.map(value => fn(value)), [-1, -1, -1, 0, -7]);
  }
  for (const fn of fixture().functions) {
    const first = fn.body[0];
    const body = first.kind === "return" ? first.value : first;
    for (const match of [body, fn.ensures[3]]) {
      assert.equal(match.kind, "someMatch");
      if (match.kind !== "someMatch") continue;
      assert.equal(match.scrutinee.kind, "var", "the outer match must bind box before any field access");
      if (match.scrutinee.kind === "var") assert.equal(match.scrutinee.name, "box");
    }
  }
});

test("both backends keep dependent field reads inside the root's match", () => {
  const mod = fixture();
  const dafny = transformModuleDafny(mod);
  const dafnyText = emitDafnyFile({ ...dafny.defFile, decls: [...(dafny.typesFile?.decls ?? []), ...dafny.defFile.decls] });
  const lean = transformModuleLean(mod);
  assert.ok(lean.typesFile);
  resetLeanModule();
  const leanText = emitLeanFile(lean.typesFile);
  for (const output of [dafnyText, leanText]) {
    assert.match(output, /match box/);
    assert.doesNotMatch(output, /\bbox\.inner\b/, "box is optional; field reads must use its unwrapped binder");
  }
});

test("branch facts hold for both outcomes across presence, variants, membership and Boolean composition", () => {
  const conditions = [
    "x !== undefined", "x === undefined", "!(x === undefined)", "!!x", "!!!x",
    "x !== undefined && x > 0", "x === undefined || x <= 0",
    "x !== undefined || flag", "x === undefined && flag",
    "!(x === undefined || !flag)", "!(x !== undefined && flag)",
    "box?.n === undefined", "box?.n !== undefined", "box?.n === 0", "box?.n !== 0", "!box?.n",
    'choice.tag === "a"', 'choice.tag !== "a"', '"a" === choice.tag', '!(choice.tag !== "a")',
    'choice.tag === "a" || flag', 'choice.tag !== "a" && flag', '"extra" in choice',
    "key in map", "!(key in map)", "!(key in map) || flag", "key in map || flag",
    "Array.isArray(items)", "!Array.isArray(items)", 'typeof items === "string"',
  ];
  const text = `type Choice = { tag: "a"; extra?: number } | { tag: "b" };
    interface Box { n?: number }
    ${conditions.map((condition, i) => `export function guard${i}(
      x: number | undefined, box: Box | undefined, choice: Choice,
      map: Record<string, number>, key: string, flag: boolean, items: number[] | string,
    ): boolean { return ${condition}; }`).join("\n")}`;
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("/facts.ts", text);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  const mod = resolveModule(extractModule(file));
  const runtime: Record<string, (...args: any[]) => boolean> = {};
  new Function("exports", ts.transpileModule(text, { compilerOptions: {
    target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.CommonJS,
  } }).outputText)(runtime);

  function read(e: TExpr, values: Record<string, any>): any {
    if (e.kind === "var") return values[e.name];
    if (e.kind === "field") return read(e.obj, values)?.[e.field];
    throw new Error(`non-path fact: ${e.kind}`);
  }
  const seen = new Set<string>();
  for (const fn of mod.functions) {
    const statement = fn.body[0];
    assert.ok(statement.kind === "return");
    for (const truth of [false, true]) {
      const facts = conditionFacts(statement.value, truth, mod.typeDecls);
      for (const x of [undefined, 0, 1])
      for (const box of [undefined, {}, { n: 0 }, { n: 1 }])
      for (const choice of [{ tag: "a" }, { tag: "a", extra: 0 }, { tag: "b" }])
      for (const map of [{}, { key: 3 }])
      for (const flag of [false, true])
      for (const items of [[], "text"]) {
        const values = { x, box, choice, map, key: "key", flag, items };
        if (runtime[fn.name](x, box, choice, map, "key", flag, items) !== truth) continue;
        for (const fact of facts) {
          seen.add(fact.kind);
          const message = `${fn.name} = ${truth}: ${JSON.stringify(values)}`;
          if (fact.kind === "present") assert.notEqual(read(fact.scrutinee, values), undefined, message);
          else if (fact.kind === "in") assert.ok(read(fact.key, values) in read(fact.map, values), message);
          else {
            const value = read(fact.scrutinee, values);
            const decl = mod.typeDecls.find(d => d.name === fact.typeName)!;
            const tag = decl.discriminant === "__isArray__"
              ? Array.isArray(value) ? "ArrayBranch" : "NonArrayBranch"
              : value[decl.discriminant!];
            assert.equal(tag, fact.variant, message);
          }
        }
      }
    }
  }
  assert.deepEqual([...seen].sort(), ["in", "present", "variant"]);
});
