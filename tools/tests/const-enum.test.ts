import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { Project, ScriptTarget, ModuleResolutionKind } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const fixture = readFileSync(new URL("../fixtures/const-enum.ts", import.meta.url), "utf8");

function extract(source: string, dependencies: Record<string, string> = {}) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, moduleResolution: ModuleResolutionKind.NodeJs,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  for (const [name, contents] of Object.entries(dependencies)) project.createSourceFile(`/${name}`, contents);
  const file = project.createSourceFile("/main.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return extractModule(file);
}

function typed(source: string, dependencies: Record<string, string> = {}) {
  return narrowModule(resolveModule(extract(source, dependencies)));
}

function emit(source: string, dependencies: Record<string, string> = {}) {
  const { typesFile, defFile } = transformModuleDafny(typed(source, dependencies));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

test("numeric const enum values agree in executable code and specifications", () => {
  const mod = typed(fixture);
  assert.equal(mod.functions[0].returnTy.kind, "int");
  const dafny = emit(fixture);
  assert.match(dafny, /type Phase = int/);
  assert.match(dafny, /active\(\) == 4/);
  assert.doesNotMatch(dafny, /Phase\.Active|Phase\.Idle|toExponential/);
  for (const name of ["active", "bracket"]) {
    const fn = mod.functions.find(f => f.name === name)!;
    assert.equal(fn.body[0].kind, "return");
    if (fn.body[0].kind === "return") {
      assert.equal(fn.body[0].value.kind, "num");
      if (fn.body[0].value.kind === "num") assert.equal(fn.body[0].value.value, 4);
    }
  }
});

test("both backends retain numeric truthiness for zero-valued enums", () => {
  const mod = typed(fixture);
  assert.equal(mod.functions.find(f => f.name === "isTruthy")!.params[0].ty.kind, "int");
  assert.match(emit(fixture), /phase != 0/);
  resetLeanModule();
  const lean = transformModuleLean(mod);
  const text = [lean.typesFile, lean.defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  assert.match(text, /phase : Int/);
  assert.doesNotMatch(text, /Phase\.Active|Phase\.Idle/);
});

test("numeric aliases and imported enum bindings preserve their own values", () => {
  const mod = typed(`
import { State as First } from "./first";
import { State as Second } from "./barrel";
export function first(): First {
  //@ verify
  //@ ensures \\result === First.Active
  return First.Active;
}
export function second(): Second.Active {
  //@ verify
  //@ ensures \\result === Second.Active
  return Second.Active;
}`, {
    "first.ts": "export const enum State { Active = 3 }",
    "second.ts": "export const enum State { Active = 7 }",
    "barrel.ts": 'export { State } from "./second";',
  });
  for (const [name, value] of [["first", 3], ["second", 7]] as const) {
    const fn = mod.functions.find(f => f.name === name)!;
    assert.equal(fn.returnTy.kind, "int");
    const spec = fn.ensures[0];
    assert.equal(spec.kind, "binop");
    if (spec.kind === "binop") assert.deepEqual(spec.right, { kind: "num", value, ty: { kind: "nat" } });
  }
});

test("a parameter shadowing the enum name remains an ordinary object", () => {
  const dafny = emit(`
const enum Phase { Active = 4 }
interface Input { Active: number }
export function read(Phase: Input): number {
  //@ verify
  //@ ensures \\result === Phase.Active
  return Phase.Active;
}`);
  assert.match(dafny, /Phase.Active/);
  assert.doesNotMatch(dafny, /read\(Phase\) == 4/);
});

test("enum types in class and optional record fields lower to integers", () => {
  const dafny = emit(`
const enum Phase { Idle, Active = 4 }
interface Input { phase?: Phase }
export class State {
  phase!: Phase;
  read(input: Input): number {
    //@ verify
    return input.phase ?? this.phase;
  }
}`);
  assert.match(dafny, /phase: Option<int>/);
  assert.match(dafny, /var phase: int/);
  assert.doesNotMatch(dafny, /toFixed|toExponential/);
});

test("type aliases of enum values retain numeric behavior", () => {
  const mod = typed(`
const enum Phase { Idle, Active = 4 }
type Alias = Phase;
export function truthy(value: Alias): boolean {
  //@ verify
  //@ ensures \\result === (value !== 0)
  if (value) return true;
  return false;
}`);
  assert.equal(mod.functions[0].params[0].ty.kind, "int");
});

test("a member type used only in a signature retains its enum dependency", () => {
  const mod = typed(`
const enum Phase { Active = 4 }
export function active(): Phase.Active {
  //@ verify
  //@ ensures \\result === 4
  return Phase.Active;
}`);
  assert.equal(mod.functions[0].returnTy.kind, "int");
});

for (const value of ['"active"', '0.5', '9007199254740992']) {
  test(`unsupported enum value ${value} is rejected explicitly`, () => {
    assert.throws(() => extract(`
const enum Phase { Active = ${value} }
export function active(): Phase {
  //@ verify
  return Phase.Active;
}`), /const enum.*safe integer/i);
  });
}

for (const [read, expected] of [
  ["Phase.Active", { kind: "field", obj: { kind: "var", name: "Phase" }, field: "Active" }],
  ['Phase["Active"]', { kind: "index", obj: { kind: "var", name: "Phase" }, idx: { kind: "str", value: "Active" } }],
] as const) {
  test(`runtime enum member ${read} falls through to ordinary access`, () => {
    const mod = extract(`
enum Phase { Active = 4 }
export function active(): number {
  //@ verify
  return ${read};
}`);
    const ret = mod.functions[0].body[0];
    assert.equal(ret.kind, "return");
    if (ret.kind === "return") assert.deepEqual(ret.value, expected);
  });
}
