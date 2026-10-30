import { test } from "node:test";
import assert from "node:assert/strict";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import type { RawModule } from "../src/rawir.ts";

function extract(text: string, checkTypes = true) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("selective.ts", text);
  if (checkTypes) assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), []);
  return extractModule(source);
}

function dafny(raw: RawModule) {
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(raw)));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

test("unused unsupported constants are excluded before extraction for both backends", () => {
  const raw = extract(`
    const UNUSED = /unused/;
    const BASE = 3, OTHER_UNUSED = /other/;
    const OFFSET = BASE + 4;
    function selected(n: number): number {
      //@ verify
      //@ ensures \\result === n + OFFSET
      return n + OFFSET;
    }
    function unrelated() { return /outside/; }
  `);
  assert.deepEqual(raw.constants.map(c => c.name), ["BASE", "OFFSET"]);
  assert.deepEqual(raw.functions.map(f => f.name), ["selected"]);
  const dafnyText = dafny(raw);
  const lean = transformModuleLean(narrowModule(resolveModule(raw)));
  resetLeanModule();
  const leanText = [lean.typesFile, lean.defFile].filter(f => f !== null).map(f => emitLeanFile(f!)).join("\n");
  for (const text of [dafnyText, leanText]) {
    assert.match(text, /BASE/);
    assert.match(text, /OFFSET/);
    assert.doesNotMatch(text, /UNUSED|unrelated/);
  }
});

test("a marked constant activates selective mode and retains its transitive dependencies", () => {
  const raw = extract(`
    const UNUSED = /unused/;
    const BASE = 2;
    //@ verify
    const CHOSEN = BASE + 1;
    function unrelated() { return /outside/; }
  `);
  assert.deepEqual(raw.constants.map(c => c.name), ["BASE", "CHOSEN"]);
  assert.deepEqual(raw.functions, []);
  assert.match(dafny(raw), /const CHOSEN: int := \(BASE \+ 1\)/);
});

for (const [name, text] of [
  ["direct dependency", `
    const BAD = /bad/;
    function selected(s: string) {
      //@ verify
      return BAD.test(s);
    }`],
  ["transitive dependency", `
    const BAD = /bad/;
    const ALIAS = BAD;
    function selected(s: string) {
      //@ verify
      return ALIAS.test(s);
    }`],
  ["explicit selection", `
    //@ verify
    const BAD = /bad/;`],
  ["whole-file mode", `
    const BAD = /bad/;
    function selected(n: number) { return n; }`],
] as const) {
  test(`unsupported selected constants still fail: ${name}`, () => {
    assert.throws(() => extract(text), /Failed to extract const 'BAD' at selective\.ts:\d+: Unsupported expression: \/bad\//);
  });
}

test("dependencies include every statement/spec position and collection elements", () => {
  const names = ["PRE", "POST", "DEC", "INV", "LOOP_DEC", "DONE", "ASSERTED", "ASSUMED", "GHOST", "UPDATE", "CASE", "DEFAULT", "ELEMENT"];
  const raw = extract(`
    ${names.map(name => `const ${name} = 1;`).join("\n")}
    const UNUSED = /unused/;
    function selected(n: number, tag: string): number {
      //@ verify
      //@ requires n >= PRE
      //@ ensures \\result >= POST
      //@ decreases DEC
      //@ ghost let g = GHOST
      //@ ghost g = UPDATE
      //@ ghost let seen = new Set<number>()
      //@ assert n >= ASSERTED
      //@ assume n >= ASSUMED
      let i = 0;
      while (i < n) {
        //@ invariant i <= n + INV
        //@ decreases n + LOOP_DEC - i
        //@ done_with i >= DONE
        i++;
      }
      const values = new Set([ELEMENT]);
      switch (tag) {
        case "a": return CASE;
        default: return DEFAULT;
      }
    }
  `);
  assert.deepEqual(raw.constants.map(c => c.name), names);
});

test("params, locals, loop/lambda/quantifier binders and property names do not select constants", () => {
  const raw = extract(`
    const param = /bad/, local = /bad/, item = /bad/, lambda = /bad/, q = /bad/;
    const field = /bad/, ghost = /bad/, text = /bad/;
    function selected(param: number, box: { field: number }, xs: number[]): number {
      //@ verify
      //@ requires forall(q, q === q)
      //@ ensures \\result >= param
      //@ contract mentions text without depending on it
      //@ ghost let ghost = 0
      //@ assert ghost === 0
      let local = param + box.field;
      for (const item of xs) {
        //@ invariant item === item
        local += item;
      }
      const mapped = xs.map(lambda => lambda + local);
      const label = "text";
      return local;
    }
  `);
  assert.deepEqual(raw.constants, []);
});

test("shadowing in one branch does not hide a dependency in another", () => {
  const raw = extract(`
    const LIMIT = 2;
    function selected(flag: boolean): number {
      //@ verify
      if (flag) {
        const LIMIT = 1;
        return LIMIT;
      }
      return LIMIT;
    }
  `);
  assert.deepEqual(raw.constants.map(c => c.name), ["LIMIT"]);
});

test("skipped and havoced statements do not retain their source dependencies", () => {
  const raw = extract(`
    const UNUSED = /unused/;
    //@ skip
    //@ verify
    const SKIPPED = /skipped/;
    function selected(s: string): boolean {
      //@ verify
      //@ skip
      UNUSED.test(s);
      //@ havoc
      const answer = UNUSED.test(s);
      return answer;
    }
  `);
  assert.deepEqual(raw.constants, []);
});

test("expression arrows and inline verified callbacks retain constant dependencies", () => {
  const raw = extract(`
    const UNUSED = /unused/;
    const ARROW = 1, CALLBACK = 2;
    //@ verify
    const selected = (n: number): number => n + ARROW;
    function register(f: (n: number) => number) {}
    register((n: number) => {
      //@ verify
      return n + CALLBACK;
    });
  `);
  assert.deepEqual(raw.constants.map(c => c.name), ["ARROW", "CALLBACK"]);
  assert.equal(raw.functions.length, 2);
});

test("constant cycles terminate during dependency selection", () => {
  const raw = extract(`
    const FIRST: number = SECOND;
    const SECOND: number = FIRST;
    function selected(): number {
      //@ verify
      return FIRST;
    }
  `, false); // Deliberately invalid TS: selection must terminate; verification rejects the cycle.
  assert.deepEqual(raw.constants.map(c => c.name), ["FIRST", "SECOND"]);
});

test("class methods select constants, written/read fields, and spec-only fields before lowering", () => {
  const raw = extract(`
    const UNUSED = /unused/;
    const BASE = 1, STEP = BASE + 1, LIMIT = 100;
    class Counter {
      count = 0;
      max = 10;
      written = 0;
      unused: (value: string) => RegExp = value => new RegExp(value);
      increment(): number {
        //@ verify
        //@ requires this.count + STEP <= this.max && this.max <= LIMIT
        //@ ensures this.count <= this.max
        this.written = 1;
        this.count = this.count + STEP;
        return this.count;
      }
      unrelated() { return /outside/; }
    }
  `);
  assert.deepEqual(raw.constants.map(c => c.name), ["BASE", "STEP", "LIMIT"]);
  assert.deepEqual(raw.classes[0].fields.map(f => f.name), ["count", "max", "written"]);
  assert.deepEqual(raw.classes[0].methods.map(f => f.name), ["increment"]);
  assert.doesNotMatch(dafny(raw), /unused|UNUSED|unrelated/);
});

test("using this as a whole retains the class shape", () => {
  const raw = extract(`
    class Counter {
      count = 0;
      other = 1;
      selected(): number {
        //@ verify
        const alias = this;
        return alias.count;
      }
    }
  `);
  assert.deepEqual(raw.classes[0].fields.map(f => f.name), ["count", "other"]);
});

test("types used only by selected constants are retained", () => {
  const raw = extract(`
    type Box = { count: number };
    type Boxes = Box[];
    //@ verify
    const BOXES: Boxes = [{ count: 1 }];
  `);
  assert.deepEqual(raw.typeDecls.map(d => d.name), ["Box", "Boxes"]);
  assert.match(dafny(raw), /datatype Box/);
});

test("a type reference does not select a same-named module constant", () => {
  const raw = extract(`
    const Box = /unused/;
    type Box = { count: number };
    function selected(box: Box): number {
      //@ verify
      return box.count;
    }
  `);
  assert.deepEqual(raw.constants, []);
  assert.match(dafny(raw), /datatype Box/);
});

test("same-file extern contracts retain constants without inspecting the extern body", () => {
  const raw = extract(`
    const UNUSED = /outside/;
    const LIMIT = 10;
    //@ extern
    function external(s: string): number {
      //@ ensures \\result <= LIMIT
      return UNUSED.test(s) ? 0 : 1;
    }
    function selected(s: string): number {
      //@ verify
      return external(s);
    }
  `);
  assert.deepEqual(raw.constants.map(c => c.name), ["LIMIT"]);
  assert.equal(raw.externs[0].qualified, "external");
});

test("selected constants resolve imported types and calls", () => {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext, types: [] } });
  project.createSourceFile("dependency.ts", `
    export type Box = { count: number };
    export function size(n: number): number { return n; }
  `);
  const source = project.createSourceFile("selective.ts", `
    import { type Box, size } from "./dependency";
    const UNUSED = /unused/;
    //@ verify
    const BOX: Box = { count: size(1) };
  `);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), []);
  const raw = extractModule(source);
  assert.deepEqual(raw.constants.map(c => c.name), ["BOX"]);
  assert.equal(raw.externs[0].qualified, "size");
  assert.deepEqual(raw.typeDecls.map(d => d.name), ["Box"]);
  assert.match(dafny(raw), /datatype Box/);
});
