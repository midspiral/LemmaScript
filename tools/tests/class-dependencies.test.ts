import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { Project, ScriptTarget, ModuleResolutionKind } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

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

function emit(source: string, dependencies: Record<string, string> = {}) {
  const typed = narrowModule(resolveModule(extract(source, dependencies)));
  const { typesFile, defFile } = transformModuleDafny(typed);
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

test("class-only selection retains fields, body/spec constants, and transitive dependencies", () => {
  const source = readFileSync(new URL("../fixtures/class-dependencies.ts", import.meta.url), "utf8");
  const raw = extract(source);
  assert.deepEqual(raw.functions, []);
  assert.deepEqual(raw.constants.map(c => c.name), ["PREFIX", "INACTIVE", "LIMIT"]);
  assert.ok(raw.typeDecls.some(d => d.name === "Runner"));
  assert.ok(!raw.typeDecls.some(d => d.name === "Unused"));
  assert.deepEqual(raw.classes[0].methods.map(m => m.name), ["active", "bounded"]);
  const dafny = emit(source);
  assert.match(dafny, /datatype Runner = Runner\(epoch: string\)/);
  assert.doesNotMatch(dafny, /type Runner\(==\)/);
  assert.match(dafny, /const INACTIVE/);
  assert.match(dafny, /this.runner.epoch != INACTIVE/);
});

test("class field discovery follows imported nested and optional record types", () => {
  const dafny = emit(`
import { Envelope } from "./model";
export class Reader {
  value!: Envelope;
  pending(): boolean {
    //@ verify
    return this.value.phase === "pending";
  }
}`, { "model.ts": `
import { Phase } from "./phase";
export interface Envelope { phase?: Phase; next?: Envelope }
`, "phase.ts": 'export type Phase = "pending" | "done";' });
  assert.match(dafny, /datatype Phase = pending \| done/);
  assert.match(dafny, /phase: Option<Phase>/);
  assert.match(dafny, /next: Option<Envelope>/);
  assert.doesNotMatch(dafny, /type (?:Envelope|Phase)\(==\)/);
});

test("constants referenced only in switch arms or proof annotations survive selection", () => {
  const raw = extract(`
const ARM = 1;
const DEFAULT = 2;
const ASSERTED = 3;
const BOUND = 4;
export class Reader {
  read(tag: string): number {
    //@ verify
    //@ assert ASSERTED === 3
    let count = 0;
    while (count < 0) {
      //@ invariant count <= BOUND
      count += 1;
    }
    switch (tag) {
      case "one": return ARM;
      default: return DEFAULT;
    }
  }
}`);
  assert.deepEqual(raw.constants.map(c => c.name), ["ARM", "DEFAULT", "ASSERTED", "BOUND"]);
});

test("class fields retain local generic and lowercase type dependencies", () => {
  const raw = extract(`
interface item { count: number }
interface Box<T> { value: T }
export class Reader {
  box!: Box<item>;
  count(): number {
    //@ verify
    return this.box.value.count;
  }
}`);
  assert.ok(raw.typeDecls.some(d => d.name === "Box"));
  assert.ok(raw.typeDecls.some(d => d.name === "item"));
});

test("selected method signatures discover imported parameter and return records", () => {
  const dafny = emit(`
import { Input, Output } from "./model";
export class Convert {
  read(input: Input): Output {
    //@ verify
    //@ ensures \\result.value === input.value
    return { value: input.value };
  }
}`, { "model.ts": `
export interface Input { value: number }
export interface Output { value: number }
` });
  assert.match(dafny, /datatype Input = Input\(value: int\)/);
  assert.match(dafny, /datatype Output = Output\(value: int\)/);
  assert.match(dafny, /return Output\(input.value\)/);
});

test("class field type overrides keep fields and hide their original dependencies", () => {
  const source = `
import { Complex } from "./model";
//@ declare-type RunnerView { epoch: string }
export class State {
  background!: Promise<Complex>; //@ type unknown
  runner!: Complex; //@ type RunnerView
  read(): string {
    //@ verify
    //@ ensures \\result === this.runner.epoch
    return this.runner.epoch;
  }
}`;
  const dependencies = { "model.ts": `
export interface Hidden { detail: string }
export interface Complex { epoch: string; other: Hidden }
` };
  const raw = extract(source, dependencies);
  assert.deepEqual(raw.classes[0].fields, [
    { name: "background", tsType: "unknown" },
    { name: "runner", tsType: "RunnerView" },
  ]);
  assert.deepEqual(raw.typeDecls.map(d => d.name), ["RunnerView"]);
  const dafny = emit(source, dependencies);
  assert.match(dafny, /var background: Unknown/);
  assert.match(dafny, /var runner: RunnerView/);
  assert.doesNotMatch(dafny, /Complex|Hidden|Promise/);
});

test("structural aliases in class fields resolve like ordinary record fields", () => {
  const dafny = emit(`
type Numbers = number[];
export class Values {
  values!: Numbers;
  size(): number {
    //@ verify
    //@ ensures \\result === this.values.length
    return this.values.length;
  }
}`);
  assert.match(dafny, /var values: seq<int>/);
  assert.match(dafny, /return \|this.values\|/);
});

test("a selected class is not also extracted as a record through its method signature", () => {
  const dafny = emit(`
export class State {
  self(): State {
    //@ verify
    return this;
  }
}`);
  assert.match(dafny, /class State/);
  assert.doesNotMatch(dafny, /datatype State|type State\(==\)/);
});

test("anonymous method return types are distinct across classes", () => {
  const dafny = emit(`
export class First {
  read() {
    //@ verify
    return { count: 1 };
  }
}
export class Second {
  read() {
    //@ verify
    return { text: "x" };
  }
}`);
  assert.match(dafny, /datatype FirstReadResult = FirstReadResult\(count: int\)/);
  assert.match(dafny, /datatype SecondReadResult = SecondReadResult\(text: string\)/);
});

test("class method selection honors declaration skips and ignores prose", () => {
  const raw = extract(`
//@ skip
class Skipped {
  read() {
    //@ verify
    throw new Error("not extracted");
  }
}
export class Kept {
  read() {
    //@ verify
    return 1;
  }
  //@ skip
  skipped() {
    //@ verify
    throw new Error("not extracted");
  }
  prose() {
    // This prose mentions //@ verify without selecting the method.
    throw new Error("not extracted");
  }
}`);
  assert.deepEqual(raw.classes.map(c => c.name), ["Kept"]);
  assert.deepEqual(raw.classes[0].methods.map(m => m.name), ["read"]);
});
