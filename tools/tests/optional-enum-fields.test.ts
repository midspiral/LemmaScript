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

const phase = 'export type Phase = "pending" | "executing" | "complete";';
const fixture = readFileSync(new URL("../fixtures/optional-enum-fields.ts", import.meta.url), "utf8");

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
  const dafny = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  resetLeanModule();
  const lean = transformModuleLean(typed);
  assert.ok(lean.typesFile);
  return { dafny, lean: emitLeanFile(lean.typesFile) };
}

test("both backends preserve the enum in every optional record field", () => {
  const { dafny, lean } = emit(fixture);
  for (const name of ["previous", "scheduled", "hint", "fallback", "retryHint"]) {
    assert.ok(dafny.includes(`${name}: Option<Phase>`), name);
    assert.ok(lean.includes(`${name} : Option Phase`), name);
  }
  assert.match(dafny, /current: Phase/);
  assert.match(dafny, /timeline: seq<Phase>/);
  assert.match(dafny, /isExecuting\(i_s_previous_val\)/);
  assert.doesNotMatch(dafny, /== "(?:pending|executing|complete)"/);
  const snapshot = extract(fixture).typeDecls.find(d => d.name === "Snapshot")!;
  assert.ok(snapshot.fields!.find(f => f.name === "hint")!.optionalKey);
  assert.equal(snapshot.fields!.find(f => f.name === "scheduled")!.optionalKey, undefined);
});

for (const [name, declaration] of [
  ["record alias", "type Envelope = { phase: Phase | null }"],
  ["inherited generic field", "interface Base<T> { phase: T | null }\ninterface Envelope extends Base<Phase> {}"],
  ["discriminated union", 'type Envelope = { tag: "live"; phase: Phase | null } | { tag: "archived"; phase?: Phase }'],
  ["single variant", 'type Envelope = | { tag: "live"; phase: Phase | null }'],
] as const) {
  test(`optional enums survive: ${name}`, () => {
    const { dafny, lean } = emit(`${phase}\n${declaration}
export function read(e: Envelope): boolean {
  //@ verify
  return true;
}`);
    assert.match(dafny, /phase: Option<Phase>/);
    assert.doesNotMatch(dafny, /Option<string>/);
    assert.match(lean, /Option Phase/);
  });
}

for (const importedRecord of [false, true]) {
  for (const declaration of [
    "export interface Envelope { phase?: Phase; next?: Envelope }",
    "export type Envelope = { phase: Phase | null; next?: Envelope }",
  ]) {
    test(`discover an enum used only in ${importedRecord ? "an imported" : "a local"} recursive ${declaration.includes("interface") ? "interface" : "record alias"}`, () => {
      const model = `import { Phase } from "./phase";\n${declaration}`;
      const source = `${importedRecord ? 'import { Envelope } from "./model";' : model}
export function read(e: Envelope): boolean {
  //@ verify
  return e.phase === "executing";
}`;
      const { dafny, lean } = emit(source, { "phase.ts": phase, "model.ts": model });
      assert.match(dafny, /datatype Phase = pending \| executing \| complete/);
      assert.match(dafny, /phase: Option<Phase>/);
      assert.match(dafny, /next: Option<Envelope>/);
      assert.match(lean, /inductive Phase/);
      assert.doesNotMatch(dafny, /type Phase\(==\)/);
    });
  }
}

test("equal enum member sets keep their own alias names; inline unions remain strings", () => {
  const { dafny } = emit(`${phase}
type Other = "pending" | "executing" | "complete";
interface Envelope {
  phase: Phase | null;
  other?: Other;
  inline: "pending" | "executing" | "complete" | null;
  text?: string;
  flag?: boolean;
}
export function read(e: Envelope): boolean {
  //@ verify
  return true;
}`);
  assert.match(dafny, /phase: Option<Phase>/);
  assert.match(dafny, /other: Option<Other>/);
  assert.match(dafny, /inline: Option<string>/);
  assert.match(dafny, /text: Option<string>/);
  assert.match(dafny, /flag: Option<bool>/);
});

test("uninstantiated generic fields keep their type parameter", () => {
  const typed = resolveModule(extract("interface Cell<T> { value: T | null; hint?: T }"));
  const cell = typed.typeDecls.find(d => d.name === "Cell")!;
  for (const field of cell.fields!) {
    assert.deepEqual(field.type, { kind: "optional", inner: { kind: "user", name: "T" } });
  }
});

for (const declaration of [
  "export interface Envelope { phase?: Phase }",
  "export type Envelope = { phase?: Phase }",
]) {
  test(`declare-type still hides the dependencies of an imported ${declaration.includes("interface") ? "interface" : "record alias"}`, () => {
    const raw = extract(`
import { Envelope } from "./model";
//@ declare-type Envelope { phase: string }
export function read(e: Envelope): boolean {
  //@ verify
  return true;
}`, { "model.ts": `${phase}\n${declaration}` });
    assert.deepEqual(raw.typeDecls.map(d => d.name), ["Envelope"]);
  });
}

test("field type overrides still hide the field's original dependencies", () => {
  const raw = extract(`
import { Phase } from "./phase";
interface Envelope {
  phase: Phase | null; //@ type string
}
export function read(e: Envelope): boolean {
  //@ verify
  return true;
}`, { "phase.ts": phase });
  assert.deepEqual(raw.typeDecls.map(d => d.name), ["Envelope"]);
  assert.equal(raw.typeDecls[0].fields![0].tsType, "string");
});

test("nullable alias discovery stops at a declared verification type", () => {
  const raw = extract(`
import { Envelope } from "./model";
//@ declare-type Envelope { phase: string }
export function read(e: Envelope | undefined): boolean {
  //@ verify
  return true;
}`, { "model.ts": `${phase}
interface Payload { phase?: Phase }
export type Envelope = { tag: "live"; payload: Payload } | { tag: "archived"; payload: Payload };
` });
  assert.deepEqual(raw.typeDecls.map(d => d.name), ["Envelope"]);
});
