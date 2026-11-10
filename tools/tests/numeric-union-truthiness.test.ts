import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { Project, ScriptTarget, ModuleResolutionKind } from "ts-morph";
import { zTruth, zNot } from "../fixtures/numeric-union-truthiness.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const fixture = readFileSync(new URL("../fixtures/numeric-union-truthiness.ts", import.meta.url), "utf8");

function typed(source = fixture, dependencies: Record<string, string> = {}) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, moduleResolution: ModuleResolutionKind.NodeJs,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  for (const [name, text] of Object.entries(dependencies)) project.createSourceFile(`/${name}`, text);
  const file = project.createSourceFile("/main.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

function assertNumericReads(mod: ReturnType<typeof typed>, kind = "int") {
  const truth = mod.functions.find(f => f.name === "zTruth")!.body[0];
  const not = mod.functions.find(f => f.name === "zNot")!.body[0];
  assert.ok(truth.kind === "return" && truth.value.kind === "conditional");
  assert.equal(truth.value.cond.ty.kind, kind);
  assert.ok(not.kind === "return" && not.value.kind === "unop");
  assert.equal(not.value.expr.ty.kind, kind);
}

test("zero is a runtime counterexample to both numeric-union contracts", () => {
  assert.equal(zTruth(0), 6);
  assert.equal(zNot(0), true);
  for (const z of [1, 2] as const) {
    assert.equal(zTruth(z), 5);
    assert.equal(zNot(z), false);
  }
});

test("Dafny retains the zero tests in numeric-union ternaries and negation", () => {
  const { typesFile, defFile } = transformModuleDafny(typed());
  const text = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.match(text, /type Z = int/);
  assert.match(text, /function zTruth\(z: Z\): int/);
  assert.match(text, /function zNot\(z: Z\): bool/);
  assert.match(text, /z != 0/);
  assert.match(text, /z == 0/);
  assert.doesNotMatch(text, /if true/);
});

test("Lean retains the zero tests in numeric-union ternaries and negation", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(typed());
  const text = [typesFile, defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  assert.match(text, /z : Z/);
  assert.match(text, /z ≠ 0/);
  assert.match(text, /z = 0/);
});

for (const declaration of [
  "type Z = -2 | 0 | 2;",
  "type Base = 0 | 1 | 2; type Z = Base;",
  "type Z = 0;",
  "type Z = number;",
]) {
  test(`numeric aliases retain numeric semantics: ${declaration}`, () => {
    const mod = typed(fixture.replace("type Z = 0 | 1 | 2;", declaration));
    for (const fn of mod.functions) assert.deepEqual(fn.params[0].ty, { kind: "user", name: "Z" });
    assertNumericReads(mod);
  });
}

test("inline numeric literal unions retain numeric semantics", () => {
  const mod = typed(fixture.replace("type Z = 0 | 1 | 2;", "").replaceAll("z: Z", "z: 0 | 1 | 2"));
  for (const fn of mod.functions) assert.equal(fn.params[0].ty.kind, "int");
  assertNumericReads(mod);
});

test("renamed imported numeric unions retain numeric semantics", () => {
  const mod = typed(fixture.replace("type Z = 0 | 1 | 2;", 'import { Level as Z } from "./model";'), {
    "model.ts": "export type Level = 0 | 1 | 2;",
  });
  for (const fn of mod.functions) assert.deepEqual(fn.params[0].ty, { kind: "user", name: "Z" });
  assertNumericReads(mod);
});

test("numeric union fields and optional values retain numeric semantics", () => {
  const mod = typed(`
type Z = 0 | 1 | 2;
interface Input { value: Z; values: Z[]; optional?: Z }
export function read(input: Input): boolean {
  //@ verify
  return !input.value && !input.values[0] && !input.optional;
}
export function absentOrZero(value?: Z): boolean {
  //@ verify
  return !value;
}`);
  assert.deepEqual(mod.typeDecls.find(d => d.name === "Input")!.fields!.map(f => f.type), [
    { kind: "user", name: "Z" },
    { kind: "array", elem: { kind: "user", name: "Z" } },
    { kind: "optional", inner: { kind: "user", name: "Z" } },
  ]);
  assert.deepEqual(mod.functions[1].params[0].ty, { kind: "optional", inner: { kind: "user", name: "Z" } });
  const ret = mod.functions[1].body[0];
  assert.ok(ret.kind === "return" && ret.value.kind === "unop");
  assert.deepEqual(ret.value.expr.ty, { kind: "optional", inner: { kind: "int" } });
});

test("numeric alias overrides still select the modeled numeric type", () => {
  const mod = typed(fixture.replace("type Z = 0 | 1 | 2;", "//@ type nat\ntype Z = 0 | 1 | 2;"));
  for (const fn of mod.functions) assert.deepEqual(fn.params[0].ty, { kind: "user", name: "Z" });
  assertNumericReads(mod, "nat");
});

test("numeric alias names remain in generated parameter and return types", () => {
  const mod = typed(`
type TaskId = number;
interface Task { title: string }
interface Model { tasks: Map<TaskId, Task> }
export function getTask(m: Model, taskId: TaskId): Task | undefined {
  //@ verify
  return m.tasks.get(taskId);
}
export function keepId(taskId: TaskId): TaskId {
  //@ verify
  return taskId;
}`);
  const { typesFile, defFile } = transformModuleDafny(mod);
  const dafny = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.match(dafny, /function getTask\(m: Model, taskId: TaskId\): Option<Task>/);
  assert.match(dafny, /function keepId\(taskId: TaskId\): TaskId/);
  resetLeanModule();
  const lean = transformModuleLean(mod);
  const text = [lean.typesFile, lean.defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  assert.match(text, /getTask \(m : Model\) \(taskId : TaskId\)/);
  assert.match(text, /keepId \(taskId : TaskId\) : TaskId/);
});
