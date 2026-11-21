import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import ts from "typescript";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import type { Stmt } from "../src/ir.ts";

function sourceModule(text: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("comparison.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

function emit(text: string) {
  const { typesFile, defFile } = transformModuleDafny(sourceModule(text));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-optional-comparison-"));
  try {
    const path = join(dir, "comparison.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "10", path],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const helper = `
type Box = { val: number };
function firstValue(xs: number[]): number {
  //@ requires xs.length > 0
  return xs[0];
}
`;

const cases = [
  ["early return", "if (x?.val !== firstValue(xs)) return 1; return 2;"],
  ["reversed early return", "if (firstValue(xs) !== x?.val) return 1; return 2;"],
  ["OR comparison", "if (x?.val !== firstValue(xs) || false) return 1; return 2;"],
  ["later None detector", "if (x?.val !== firstValue(xs) || y === undefined) return 1; return 2;"],
  ["call before detector", "if (firstValue(xs) > 0 || x?.val !== 0) return 1; return 2;"],
  ["comparison expression", "return x?.val !== firstValue(xs) ? 1 : 2;"],
  ["reversed comparison expression", "return firstValue(xs) !== x?.val ? 1 : 2;"],
  ["equality expression", "return x?.val === firstValue(xs) ? 2 : 1;"],
  ["direct index", "if (x?.val !== xs[0]) return 1; return 2;"],
] as const;

function example(body: string, valid: boolean) {
  return `${helper}
export function compare(x: Box | undefined, y: number | undefined, xs: number[]): number {
  //@ requires x === undefined
  //@ requires y === undefined
  //@ requires xs.length ${valid ? "> 0" : "=== 0"}
  //@ ensures \\result === 1
  ${body}
}`;
}

test("the false-proof example returns 2 in JavaScript", async () => {
  const text = ts.transpileModule(example(cases[0][1], false), {
    compilerOptions: { target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.ESNext },
  }).outputText;
  const mod = await import(`data:text/javascript;base64,${Buffer.from(text).toString("base64")}`);
  assert.equal(mod.compare(undefined, undefined, []), 2);
  assert.equal(mod.compare(undefined, undefined, [7]), 1);
});

for (const [name, body] of cases) {
  test(`${name} retains evaluation obligations when the optional is absent`, () => {
    const good = verify(emit(example(body, true)));
    assert.equal(good.status, 0, good.output);
    const bad = verify(emit(example(body, false)));
    assert.notEqual(bad.status, 0, "an absent optional must not hide an invalid call or index");
    assert.match(bad.output, /precondition.*could not be proved|index out of range/);
  });
}

test("a plain optional comparison also checks the other operand", () => {
  const output = emit(`${helper}
export function compare(x: number | undefined, xs: number[]): boolean {
  //@ requires x === undefined
  //@ requires xs.length === 0
  return x !== firstValue(xs);
}`);
  const result = verify(output);
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /precondition.*could not be proved/);
});

test("OR short-circuiting still skips an unreachable invalid call", () => {
  const output = emit(`${helper}
export function compare(x: Box | undefined, xs: number[]): number {
  //@ requires x === undefined
  //@ ensures \\result === 1
  if (x === undefined || x.val !== firstValue(xs)) return 1;
  return 2;
}`);
  const result = verify(output);
  assert.equal(result.status, 0, result.output);
});

function calls(stmts: Stmt[], depth = 0): { name: string; id: number; depth: number }[] {
  return stmts.flatMap(s => {
    if (s.kind === "let-bind" && s.value.kind === "app" && ["optional", "value"].includes(s.value.fn)) {
      const id = s.value.args[0];
      assert.ok(id.kind === "num");
      return [{ name: s.value.fn, id: id.value, depth }];
    }
    if (s.kind === "if") return [...calls(s.then, depth + 1), ...calls(s.else, depth + 1)];
    if (s.kind === "match") return s.arms.flatMap(a => calls(a.body, depth + 1));
    return [];
  });
}

for (const [backend, transform] of [["Dafny", transformModuleDafny], ["Lean", transformModuleLean]] as const) {
  test(`${backend} evaluates both comparison operands once in source order`, () => {
    const mod = sourceModule(`
function optional(id: number): number | undefined { let n = id; n += 1; return n === 2 ? undefined : n; }
function value(id: number): number { let n = id; n += 1; return n; }
export function forward(): boolean { return optional(1) !== value(2); }
export function reversed(): boolean { return value(3) !== optional(4); }
`);
    const { defFile } = transform(mod);
    for (const [name, expected] of [
      ["forward", [{ name: "optional", id: 1, depth: 0 }, { name: "value", id: 2, depth: 0 }]],
      ["reversed", [{ name: "value", id: 3, depth: 0 }, { name: "optional", id: 4, depth: 0 }]],
    ] as const) {
      const method = defFile.decls.find(d => d.kind === "method" && d.name === name);
      assert.ok(method?.kind === "method", name);
      assert.deepEqual(calls(method.body), expected, name);
    }
  });
}
