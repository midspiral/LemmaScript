import { test } from "node:test";
import assert from "node:assert/strict";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { DEFAULT_OPTIONS, type LscOptions } from "../src/config.ts";

function extract(text: string, unread: LscOptions["unread-annotations"] = "error", fileName = "f.ts") {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  return extractModule(project.createSourceFile(fileName, text), { ...DEFAULT_OPTIONS, "unread-annotations": unread });
}

const inBody = (annotation: string) =>
  `export function f(x: number): number {\n  ${annotation}\n  return x;\n}\n`;
const g = "export function g(x: number): number {\n  //@ verify\n  return x;\n}\n";

for (const [name, text, line] of [
  ["a missing space", inBody(String.raw`//@ensures \result > x`), 2],
  ["extra spaces", inBody(String.raw`//@   ensures \result > x`), 2],
  ["a tab after the keyword", inBody(String.raw`//@ ensures` + "\t" + String.raw`\result > x`), 2],
  ["a missing expression", inBody("//@ ensures"), 2],
  ["a misspelled keyword", inBody(String.raw`//@ ensure \result > x`), 2],
  ["a block-body arrow", String.raw`//@ ensures \result > x` + "\nexport const f = (x: number): number => { return x; };\n", 1],
  ["a statement before the function", String.raw`//@ ensures \result > x` + "\nconst unrelated = 1;\n" + inBody(""), 1],
  ["a loop body requires", "export function f(n: number): number {\n  let i = 0;\n  while (i < n) {\n" +
    "    //@ invariant i <= n\n    //@ requires false\n    i = i + 1;\n  }\n  return i;\n}\n", 5],
  ["a second decreases", "export function f(n: number): number {\n  //@ decreases n\n  //@ decreases n + 1\n" +
    "  return n <= 0 ? 0 : f(n - 1);\n}\n", 3],
  ["a misspelled verify outside the selected functions", g + inBody("//@verify"), 6],
  ["a tab after a directive", inBody("//@ assert\tfalse"), 2],
  ["a selected arrow beside an unselected one", "export const a = (x: number): number => x,\n" +
    "  b = (x: number): number => {\n    //@ verify\n    const y = x;\n    //@ ensures false\n    return y;\n  };\n", 5],
] as const) {
  test(`an unread annotation with ${name} fails extraction`, () => {
    assert.throws(() => extract(text), new RegExp(`^Error: f\\.ts:${line}: lsc does not read this annotation`));
  });
}

for (const [name, text] of [
  ["a contract above a function", String.raw`//@ ensures \result > x` + "\nexport function f(x: number): number {\n  return x;\n}\n"],
  ["a contract above an expression-body arrow", String.raw`//@ ensures \result > x` + "\nexport const f = (x: number): number => x;\n"],
] as const) {
  test(`${name} is read`, () => {
    assert.deepEqual(extract(text).functions[0].ensures, [String.raw`\result > x`]);
  });
}

for (const [name, text] of [
  ["a contract in a function outside the selected ones", g + inBody(String.raw`//@ ensures \result > x`)],
  ["a skipped statement", "export function f(n: number): number {\n  //@ skip\n  while (n > 0) {\n    //@ requires false\n    n = n - 1;\n  }\n  return n;\n}\n"],
  ["a TypeScript directive", inBody("//@ts-ignore")],
  ["an option with extra spaces", "//@   option safe-slice true\n" + inBody("")],
  ["an option alias after a tab", "//@\tsafe-slice\n" + inBody("")],
  ["a type override on a field of a selected class", "export class C {\n  n: number = 0; //@ type nat\n" +
    "  //@ verify\n  get(): number {\n    return this.n;\n  }\n}\n"],
  ["a contract in a class outside the selected ones", "export class C {\n  m(): number {\n    //@ ensures false\n" +
    "    return 0;\n  }\n}\n"],
] as const) {
  test(`${name} still extracts`, () => {
    assert.doesNotThrow(() => extract(text));
  });
}

const unread = inBody(String.raw`//@ ensure \result > x`);

test("unread-annotations warn reports an unread annotation without failing", t => {
  const stderr = t.mock.method(console, "error", () => {});
  assert.doesNotThrow(() => extract(unread, "warn"));
  assert.deepEqual(stderr.mock.calls.map(call => call.arguments),
    [[String.raw`warning: f.ts:2: lsc does not read this annotation: //@ ensure \result > x`]]);
});

test("unread-annotations off ignores an unread annotation", t => {
  const stderr = t.mock.method(console, "error", () => {});
  assert.doesNotThrow(() => extract(unread, "off"));
  assert.equal(stderr.mock.callCount(), 0);
});

test("an unread annotation is named by its path relative to the current directory", () => {
  const file = join("src", "nested", "f.ts");
  assert.throws(() => extract(unread, "error", file),
    { message: String.raw`${file}:2: lsc does not read this annotation: //@ ensure \result > x` });
});
