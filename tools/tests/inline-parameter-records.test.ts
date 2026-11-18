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

const fixture = readFileSync(new URL("../fixtures/inline-parameter-records.ts", import.meta.url), "utf8");

function extract(source: string, strict = true, dependencies: Record<string, string> = {}) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict, target: ScriptTarget.ESNext, moduleResolution: ModuleResolutionKind.NodeJs,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  for (const [name, contents] of Object.entries(dependencies)) project.createSourceFile(`/${name}`, contents);
  const file = project.createSourceFile("/main.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return extractModule(file);
}

function emit(source: string, strict = true, dependencies: Record<string, string> = {}) {
  const mod = narrowModule(resolveModule(extract(source, strict, dependencies)));
  const { typesFile, defFile } = transformModuleDafny(mod);
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

test("inline parameter records retain optional fields through chained coalescing", () => {
  const raw = extract(fixture);
  assert.equal(raw.functions[0].params[0].tsType, "ChooseEntry | undefined");
  assert.deepEqual(raw.typeDecls.find(d => d.name === "ChooseEntry")?.fields, [
    { name: "x", tsType: "number" },
    { name: "y", tsType: "number | undefined", optionalKey: true },
  ]);
  const output = emit(fixture);
  assert.match(output, /datatype ChooseEntry = ChooseEntry\(x: int, y: Option<int>\)/);
  assert.doesNotMatch(output, /Unknown|__type|type \{/);
  // The workaround and inline form should differ only in the record's name.
  const named = "interface Entry { x: number; y?: number }\n" +
    fixture.replace("entry: { x: number; y?: number }", "entry: Entry");
  const namedOutput = emit(named);
  assert.equal(output.slice(output.indexOf("function choose")).replaceAll("ChooseEntry", "Entry"),
    namedOutput.slice(namedOutput.indexOf("function choose")));
});

test("single coalescing and direct field access work on a required inline parameter", () => {
  const output = emit(`
export function read(entry: { x: number; y?: number }): number {
  return entry.x + (entry.y ?? 0);
}`);
  assert.match(output, /function read\(entry: ReadEntry\): int/);
  assert.match(output, /match entry.y/);
  assert.doesNotMatch(output, /Unknown/);
});

test("parameter nullability comes from syntax in both strict and loose projects", () => {
  for (const strict of [true, false]) {
    for (const param of [
      "entry: { y?: number } | undefined",
      "entry: null | { y?: number }",
      "entry: ({ y?: number } | null) | undefined",
      "entry: (({ y?: number })) | null | undefined",
      "entry: ({ y?: number } | (undefined)) | (null)",
      "entry?: { y?: number }",
    ]) {
      const source = `export function read(${param}): number {
        if (entry) return entry.y ?? 0;
        return -1;
      }`;
      const raw = extract(source, strict);
      assert.equal(raw.functions[0].params[0].tsType, "ReadEntry | undefined", param);
      const output = emit(source, strict);
      assert.match(output, /entry: Option<ReadEntry>/, param);
      assert.match(output, /y: Option<int>/, param);
      assert.doesNotMatch(output, /Unknown|__type/, param);
    }
  }
});

test("nested inline fields keep optionality and imported dependencies", () => {
  const source = `import { Value } from "./model";
export function read(entry: { detail?: { value?: Value } | null }): number {
  //@ verify
  return entry.detail?.value?.count ?? 0;
}`;
  for (const strict of [true, false]) {
    const output = emit(source, strict, { "model.ts": "export interface Value { count: number }" });
    assert.match(output, /datatype Value = Value\(count: int\)/);
    assert.match(output, /datatype ReadEntryDetail = ReadEntryDetail\(value: Option<Value>\)/);
    assert.match(output, /datatype ReadEntry = ReadEntry\(detail: Option<ReadEntryDetail>\)/);
    assert.doesNotMatch(output, /Unknown|__type/);
  }
});

test("synthesized parent and nested record names cannot capture existing types", () => {
  const source = `
interface ReadEntry { existing: boolean }
interface ReadEntry2Detail { existing: string }
export function read(entry: { detail: { y?: number } }, old: ReadEntry, nested: ReadEntry2Detail): number {
  return entry.detail.y ?? 0;
}`;
  const raw = extract(source);
  assert.equal(raw.functions[0].params[0].tsType, "ReadEntry2");
  assert.deepEqual(raw.typeDecls.find(d => d.name === "ReadEntry2")?.fields,
    [{ name: "detail", tsType: "ReadEntry2Detail2" }]);
  assert.equal(new Set(raw.typeDecls.map(d => d.name)).size, raw.typeDecls.length);
  assert.equal(emit(source), emit(source), "allocation resets between modules");
  assert.match(emit(source), /datatype ReadEntry2Detail2 = ReadEntry2Detail2\(y: Option<int>\)/);
});

test("imported types and different fields with the same capitalized name stay distinct", () => {
  const source = `import { ReadEntry } from "./model";
export function read(entry: { a: { n: number }; A: { s: string }; imported: ReadEntry }): number {
  return entry.a.n;
}`;
  const raw = extract(source, true, { "model.ts": "export interface ReadEntry { flag: boolean }" });
  const fields = raw.typeDecls.find(d => d.name === "ReadEntry2")!.fields!;
  assert.notEqual(fields[0].tsType, fields[1].tsType);
  assert.equal(fields[2].tsType, "ReadEntry");
  assert.equal(new Set(raw.typeDecls.map(d => d.name)).size, raw.typeDecls.length);
});

test("type overrides and destructured parameters retain their existing representation", () => {
  const raw = extract(`
interface View { y?: number }
export function read(entry: { y?: number; omitted: { count: number } }): number {
  //@ type entry View
  return entry.y ?? 0;
}
export function destructured({ y }: { y?: number }): number { return y ?? 0; }
`);
  assert.equal(raw.functions[0].params[0].tsType, "{ y?: number; omitted: { count: number } }");
  assert.deepEqual(raw.typeDecls.map(d => d.name), ["View"]);
  assert.deepEqual(raw.functions[1].params, [{ name: "y", tsType: "undefined | number" }]);
});

test("arrow functions and class methods synthesize distinct parameter record types", () => {
  const raw = extract(`
//@ verify
export const read = (entry: { y?: number }): number => entry.y ?? 0;
export class First {
  read(entry: { y?: number }): number {
    //@ verify
    return entry.y ?? 0;
  }
}
export class Second {
  read(entry: { text: string }): string {
    //@ verify
    return entry.text;
  }
}`);
  assert.equal(raw.functions[0].params[0].tsType, "ReadEntry");
  assert.equal(raw.classes[0].methods[0].params[0].tsType, "FirstReadEntry");
  assert.equal(raw.classes[1].methods[0].params[0].tsType, "SecondReadEntry");
});

test("generic inline parameter records bind their type parameters, including nested fields", () => {
  const output = emit(`export function read<T>(entry: { detail: { value: T }; y?: number }): number {
    return entry.y ?? 0;
  }`);
  assert.match(output, /datatype ReadEntryDetail<T> = ReadEntryDetail\(value: T\)/);
  assert.match(output, /datatype ReadEntry<T> = ReadEntry\(detail: ReadEntryDetail<T>, y: Option<int>\)/);
  assert.match(output, /function read<T>\(entry: ReadEntry<T>\): int/);
  assert.doesNotMatch(output, /type T\(==\)/);
});

test("Lean generation uses the same synthesized parameter records", () => {
  const mod = narrowModule(resolveModule(extract(fixture)));
  const { typesFile } = transformModuleLean(mod);
  assert.ok(typesFile);
  resetLeanModule();
  const output = emitLeanFile(typesFile);
  assert.match(output, /ChooseEntry/);
  assert.match(output, /Option Int/);
  assert.doesNotMatch(output, /Unknown|__type|\{ x:/);
});
