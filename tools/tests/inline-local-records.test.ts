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

const example = readFileSync(new URL("../../examples/inlineLocalRecords.ts", import.meta.url), "utf8");

function extract(text: string, dependencies: Record<string, string> = {}) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, moduleResolution: ModuleResolutionKind.NodeJs,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  for (const [name, source] of Object.entries(dependencies)) project.createSourceFile(`/${name}`, source);
  const file = project.createSourceFile("/main.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return extractModule(file);
}

function emit(text: string, dependencies: Record<string, string> = {}) {
  const mod = narrowModule(resolveModule(extract(text, dependencies)));
  const { typesFile, defFile } = transformModuleDafny(mod);
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

function lean(text: string) {
  const { typesFile, defFile } = transformModuleLean(narrowModule(resolveModule(extract(text))));
  resetLeanModule();
  return { types: typesFile ? emitLeanFile(typesFile) : "", defs: emitLeanFile(defFile) };
}

test("inline parameter and local records use the same registration path", () => {
  const raw = extract(example);
  const local = raw.functions.find(f => f.name === "mk")!.body[0];
  assert.equal(local.kind, "let");
  if (local.kind !== "let") throw new Error("missing local");
  assert.equal(local.tsType, "MkR");
  assert.deepEqual(raw.typeDecls.find(d => d.name === "MkR")?.fields, [{ name: "k", tsType: "number" }]);
  const output = emit(example);
  assert.match(output, /datatype SumAP = SumAP\(x: int, y: int\)/);
  assert.match(output, /datatype MkR = MkR\(k: int\)/);
  assert.match(output, /var r := MkR\(n\)/);
  assert.doesNotMatch(output, /Unknown|__type|type \{/);
});

test("optional locals and optional fields keep their constructors and defaults", () => {
  const output = emit(example);
  assert.match(output, /datatype OptionalLocalR = OptionalLocalR\(k: int\)/);
  assert.match(output, /datatype LocalFallbackR = LocalFallbackR\(k: Option<int>\)/);
  assert.match(output, /Some\(OptionalLocalR\(n\)\)/);
  assert.match(output, /match r.k/);
});

test("local type dependencies survive opt-in extraction and nested construction", () => {
  const output = emit(`import { Payload } from "./payload";
export function read(n: number): number {
  //@ verify
  const r: { detail: { value: Payload } } = { detail: { value: { count: n } } };
  return r.detail.value.count;
}`, { "payload.ts": "export interface Payload { count: number }" });
  assert.match(output, /datatype Payload = Payload\(count: int\)/);
  assert.match(output, /datatype ReadRDetail = ReadRDetail\(value: Payload\)/);
  assert.match(output, /var r := ReadR\(ReadRDetail\(Payload\(n\)\)\)/);
});

test("same-line shadowed locals receive distinct types, avoiding user names", () => {
  const text = `
interface PickR { occupied: boolean }
export function pick(flag: boolean, n: number): number {
  if (flag) { const r: { k: number } = { k: n }; return r.k; } else { const r: { text: string } = { text: "x" }; return r.text.length; }
}`;
  const output = emit(text);
  assert.match(output, /datatype PickR2 = PickR2\(k: int\)/);
  assert.match(output, /datatype PickR3 = PickR3\(text: string\)/);
  assert.equal(emit(text), output, "registration resets between extractions");
});

test("loop-counter renaming preserves local declaration identity", () => {
  const output = emit(`export function loops(n: number): number {
    let total = 0;
    for (let i = 0; i < n; i++) {
      const r: { k: number } = { k: i };
      total += r.k;
    }
    for (let i = 0; i < n; i++) {
      const r: { text: string } = { text: "x" };
      total += r.text.length;
    }
    return total;
  }`);
  assert.match(output, /datatype LoopsR = LoopsR\(k: int\)/);
  assert.match(output, /datatype LoopsR2 = LoopsR2\(text: string\)/);
  assert.match(output, /var i_2/);
  assert.match(output, /var r := LoopsR2\("x"\)/);
});

test("switch fall-through registers a shared local declaration once", () => {
  const raw = extract(`export function pick(kind: "a" | "b", n: number): number {
    switch (kind) {
      case "a":
      case "b": { const r: { k: number } = { k: n }; return r.k; }
    }
  }`);
  assert.deepEqual(raw.typeDecls.filter(d => d.kind === "record").map(d => d.name), ["PickR"]);
});

test("callback locals are registered and keep their type in Lean let expressions", () => {
  const text = `export function mapped(ns: number[]): number[] {
    return ns.map(n => { const r: { k: number } = { k: n }; return r.k; });
  }`;
  assert.match(emit(text), /datatype MappedR = MappedR\(k: int\)/);
  assert.match(lean(text).types, /let r : MappedR := \{ k := n \}/);
});

test("local type overrides and explicitly typed havoc are preserved", () => {
  const raw = extract(`interface View { k: number }
export function overridden(n: number): number {
  //@ type r View
  const r: { k: number } = { k: n };
  return r.k;
}
export function sampled(): number {
  //@ havoc : View
  const r: { k: number } = JSON.parse("{}");
  return r.k;
}`);
  assert.deepEqual(raw.typeDecls.map(d => d.name), ["View"]);
  assert.doesNotMatch(emit(`export function sampled(): number {
    //@ havoc
    const r: { k: number } = JSON.parse("{}");
    return r.k;
  }`), /__type|Unknown/);
});

test("Lean ascribes record lets and avoids the built-in Pure.mk name", () => {
  const { types, defs } = lean(example);
  assert.match(types, /structure MkR where\n  k : Int/);
  assert.match(types, /namespace Pure'/);
  assert.match(types, /let r : MkR := \{ k := n \}/);
  assert.match(types, /let r : Option OptionalLocalR :=/);
  assert.match(defs, /return Pure'\.mk n/);
  assert.match(defs, /let r : LocalAfterAssignmentR := \{ k := value \}/);
  assert.doesNotMatch(types, /opaque \{|__type/);
});

test("Lean mirror namespace changes reach contracts, calls, and function arguments", () => {
  const { types, defs } = lean(`
export function mapped(ns: number[]): number[] { return ns.map(mk); }
export function mk(n: number): number { const r: { k: number } = { k: n }; return r.k; }
export function caller(n: number): number {
  //@ ensures \\result === mk(n)
  return mk(n);
}
`);
  assert.match(types, /namespace Pure'/);
  assert.match(types, /ns\.map Pure'\.mk/);
  assert.ok(types.indexOf("def mk ") < types.indexOf("def mapped "), "qualified calls order dependencies before use");
  assert.match(defs, /ensures .*Pure'\.mk n/);
  assert.doesNotMatch(types + defs, /Pure\.mk/);
  assert.match(lean("export function ordinary(n: number): number { return n; }").types, /namespace Pure\n/);
});
