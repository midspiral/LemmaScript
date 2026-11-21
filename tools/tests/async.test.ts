import { test } from "node:test";
import assert from "node:assert/strict";
import { Project, ModuleResolutionKind } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function extract(source: string, dependencies: Record<string, string> = {}) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    moduleResolution: ModuleResolutionKind.NodeJs, strict: true, target: 9 /* ES2022 */, lib: ["lib.es2022.d.ts"],
  } });
  for (const [name, contents] of Object.entries(dependencies)) project.createSourceFile(`/${name}`, contents);
  return extractModule(project.createSourceFile("/main.ts", source));
}

function dafny(source: string, dependencies: Record<string, string> = {}): string {
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extract(source, dependencies))));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

const g = "async function g(n: number): Promise<number> { return n; }\n";

// ── Accepted fragment ───────────────────────────────────────

test("await is erased to the fulfillment value and Promise<T> unwraps to T", () => {
  const out = dafny(`${g}
async function f(p: Promise<number>): Promise<number> {
  const x = await p;
  const y = await g(x);
  return y + 1;
}`);
  assert.match(out, /function f\(p: int\): int/);
  assert.match(out, /var x := p;/);
  assert.match(out, /var y := g\(x\);/);
});

test("throw rejects in an async function but must be unreachable in a sync one", () => {
  const out = dafny(`
async function a(n: number): Promise<number> { if (n < 0) throw new Error("neg"); return n; }
function s(n: number): number { if (n < 0) throw new Error("neg"); return n; }`);
  assert.match(out, /method a\(n: int\) returns \(res: int\)[\s\S]*assume \{:axiom\} false;/);
  assert.match(out, /method s\(n: int\) returns \(res: int\)[\s\S]*assert false;/);
});

test("a plain-value await statement is only a suspension point", () => {
  const out = dafny("async function f(n: number): Promise<number> { await undefined; return n; }");
  assert.doesNotMatch(out, /None/);
});

test("async externs are modeled by their fulfillment value", () => {
  const out = dafny(`
//@ extern
//@ impure
//@ ensures \\result >= 0
async function io(): Promise<number> { return 0; }
async function f(): Promise<number> { const v = await io(); return v; }`);
  assert.match(out, /method \{:axiom\} io\(\) returns \(res: int\)/);
});

test("cross-file async functions are awaited through their contract", () => {
  const out = dafny('import { remote } from "./lib";\nasync function f(): Promise<number> { return await remote(1); }',
    { "lib.ts": "//@ ensures \\result > n\nexport async function remote(n: number): Promise<number> { return n + 1; }" });
  assert.match(out, /function \{:axiom\} remote\(n: int\): int/);
});

test("reads of reference values are allowed within one segment and on fresh copies", () => {
  assert.doesNotThrow(() => extract(`${g}
async function f(xs: readonly number[]): Promise<number> {
  const first = xs.length > 0 ? xs[0] : 0;
  const copy = [...xs];
  let total = await g(first);
  for (const x of copy) {
    const y = await g(x);
    total = total + y;
  }
  return total + copy.length;
}`));
});

// ── Rejected forms ──────────────────────────────────────────

const rejects: [string, string, RegExp][] = [
  ["an un-awaited promise in an async function",
    `${g}async function f(): Promise<number> { const p = g(1); return await p; }`, /must be awaited where it is created/],
  ["a sync function consuming a promise",
    `${g}function f(): number { g(1); return 0; }`, /a synchronous function cannot consume it/],
  ["a nested await",
    `${g}async function f(): Promise<number> { return (await g(1)) + 1; }`, /await must be a whole/],
  ["await in a condition",
    `${g}async function f(): Promise<number> { if (await g(1)) return 1; return 0; }`, /await must be a whole/],
  ["an async callback",
    `${g}async function f(xs: number[]): Promise<number> { xs.forEach(async x => { await g(x); }); return 0; }`, /async callbacks/],
  ["this in an async method",
    `class C {\n  n = 0;\n  async bump(): Promise<number> {\n    //@ verify\n    this.n = this.n + 1;\n    return this.n;\n  }\n}`, /cannot use 'this'/],
  ["awaiting an any value",
    `async function f(v: any): Promise<number> { const x = await v; return 0; }`, /may be a thenable/],
  ["a reference read after an await",
    `${g}async function f(xs: number[]): Promise<number> { await g(1); return xs.length; }`, /'xs' .* is read after an await/],
  ["a reference read in a later loop iteration",
    `${g}async function f(xs: number[]): Promise<number> { let i = 0; while (i < 3) { const n = xs.length; await g(n); i++; } return i; }`,
    /'xs' .* is read after an await/],
  ["iterating a live array while awaiting",
    `${g}async function f(xs: number[]): Promise<number> { for (const x of xs) { await g(x); } return 0; }`, /may not iterate 'xs' in place/],
  ["an escaping fresh copy",
    `${g}function keep(a: number[]): void {}\nasync function f(xs: number[]): Promise<number> { const c = [...xs]; keep(c); await g(1); return c.length; }`,
    /'c' .* is read after an await/],
  ["a promise parameter used as a value",
    `async function f(p: Promise<number>): Promise<boolean> { return p === p; }`, /promise parameter 'p' may only be awaited/],
];
for (const [name, source, error] of rejects) {
  test(`rejects ${name}`, () => assert.throws(() => extract(source), error));
}

test("await and async rejection are Dafny-only", () => {
  const typed = (src: string) => narrowModule(resolveModule(extract(src)));
  assert.throws(() => transformModuleLean(typed(`${g}async function f(): Promise<number> { return await g(1); }`)),
    /await is supported only by the Dafny backend/);
  assert.throws(() => transformModuleLean(typed("async function f(n: number): Promise<number> { if (n < 0) throw new Error(); return n; }")),
    /only by the Dafny backend/);
});
