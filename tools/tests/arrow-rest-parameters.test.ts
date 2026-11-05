import { test } from "node:test";
import assert from "node:assert/strict";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";

function extract(text: string) {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const source = project.createSourceFile("rest.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "input must be valid TypeScript");
  return extractModule(source);
}

test("map callbacks receive three arguments, rather than the array element's contents", () => {
  const counts = [[7]].map((...args: (number | number[] | number[][])[]) => args.length);
  assert.deepEqual(counts, [3]);
  assert.deepEqual([[7]].map(value => value.length), [1]);
});

for (const [name, source] of [
  ["map expression callback", `export function counts(): number[] {
    return [[7]].map((...args: (number | number[] | number[][])[]) => args.length);
  }`],
  ["map block callback", `export function counts(): number[] {
    return [[7]].map((...args: (number | number[] | number[][])[]) => { return args.length; });
  }`],
  ["some callback", `export function count(): boolean {
    return [[7]].some((...args: (number | number[] | number[][])[]) => args.length === 1);
  }`],
  ["fixed parameter followed by rest", `export function counts(): number[] {
    return [7].map((value, ...tail: (number | number[])[]) => tail.length);
  }`],
] as const) {
  test(`extraction rejects rest parameters in a lambda: ${name}`, () => {
    assert.throws(() => extract(source), /rest.*(lambda|arrow)|(lambda|arrow).*rest/i);
  });
}

test("ordinary array parameters and object bindings remain supported", () => {
  assert.doesNotThrow(() => extract(`
    export function lengths(xs: number[][]): number[] { return xs.map(value => value.length); }
    export function fields(xs: { value: number }[]): number[] { return xs.map(({value}) => value); }
    export function many(xs: number[]): number[] { return xs.map((value, index) => value + index); }
  `));
});

test("named variadic declarations retain their rest grouping metadata", () => {
  const module = extract(`
    export function named(...values: number[]): number { return values.length; }
    export const arrow = (...values: number[]): number => values.length;
  `);
  assert.equal(module.functions.length, 2);
  for (const fn of module.functions) {
    assert.deepEqual(fn.tsParams, [{kind: "rest", binds: ["values"]}]);
  }
});
