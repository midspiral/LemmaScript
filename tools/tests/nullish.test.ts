import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { peepholeModule } from "../src/peephole.ts";
import { parseTsType } from "../src/types.ts";

function generate(code: string, backend: "dafny" | "lean" = "dafny") {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("nullish-regression.ts", code);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  const typed = narrowModule(resolveModule(extractModule(source)));
  const { typesFile, defFile } = (backend === "dafny" ? transformModuleDafny : transformModuleLean)(typed);
  const output = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, backend);
  resetLeanModule();
  return backend === "dafny" ? emitDafnyFile(output) : emitLeanFile({ comment: "", imports: [], options: [], decls: output.decls.filter(d => d.kind === "namespace") });
}

function verify(code: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-nullish-"));
  try {
    const path = join(dir, "test.dfy");
    const text = generate(code);
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--standard-libraries", "--verification-time-limit=10", path],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr, text };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

test("optional types retain and combine their nullish alternatives", () => {
  for (const [source, nullish] of [["number | null", "null"], ["number | undefined", "undefined"],
    ["number | null | undefined", "both"], ["number | (null | undefined)", "both"],
    ["(number | null) | undefined", "both"]] as const) {
    assert.deepEqual(parseTsType(source), { kind: "optional", inner: { kind: "int" }, nullish });
  }
  assert.deepEqual(parseTsType("null | undefined"), { kind: "nullish", nullish: "both" });
});

test("Dafny rejects a postcondition that confuses null with undefined", () => {
  const source = String.raw`export function isNull(x: number | null | undefined): boolean {
    //@ ensures \result === (x === undefined)
    return x === null;
  }`;
  const wrong = verify(source);
  assert.notEqual(wrong.status, 0, wrong.text);
  assert.match(wrong.output, /postcondition could not be proved/, wrong.output);
  const correct = verify(source.replace("result === (x === undefined)", "result === (x === null)"));
  assert.equal(correct.status, 0, correct.output + correct.text);
});

const narrowing = String.raw`
export function classify(x: number | null | undefined): number {
  //@ ensures x === undefined ==> \result === 1
  //@ ensures x === null ==> \result === 2
  //@ ensures x !== undefined && x !== null ==> \result === x
  if (x === undefined) return 1;
  if (x === null) return 2;
  return x;
}
export function reverse(x: number | null | undefined): number {
  //@ ensures x === null ==> \result === 2
  //@ ensures x === undefined ==> \result === 1
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x === null) return 2;
  if (x === undefined) return 1;
  return x;
}
export function disjunction(x: number | null | undefined): number {
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x === null || x === undefined) return 0;
  return x;
}
export function retainNull(x: number | null | undefined): number | null {
  //@ ensures x !== undefined ==> \result === x
  if (x === undefined) return null;
  return x;
}
export function retainUndefined(x: number | null | undefined): number | undefined {
  //@ ensures x !== null ==> \result === x
  if (x === null) return undefined;
  return x;
}
export function positive(x: number | null | undefined): boolean {
  //@ ensures x === null || x === undefined ==> !\result
  //@ ensures x !== null && x !== undefined ==> (\result === (x > 0))
  return x !== null && x !== undefined && x > 0;
}
export function absentOrPositive(x: number | null | undefined): boolean {
  //@ ensures x === null || x === undefined ==> \result
  //@ ensures x !== null && x !== undefined ==> (\result === (x > 0))
  return x === null || x === undefined || x > 0;
}
`;

test("partial narrowing, either check order, and disjunctive early returns verify", () => {
  const result = verify(narrowing);
  assert.equal(result.status, 0, result.output + result.text);
});

test("a method in a ternary guard keeps the selected value in its narrowed scope", () => {
  const result = verify(String.raw`
function positive(x: number): boolean {
  //@ ensures \result === (x > 0)
  let result = x > 0;
  return result;
}
function fallback(take: boolean): number {
  //@ requires take
  //@ ensures \result === 7
  let result = 7;
  return result;
}
export function choose(x: number | null | undefined): number {
  //@ ensures x === null || x === undefined ==> \result === 7
  //@ ensures x !== null && x !== undefined && x > 0 ==> \result === x
  //@ ensures x !== null && x !== undefined && x <= 0 ==> \result === 7
  const chosen = x !== undefined && x !== null && positive(x) ? x : 7;
  return chosen;
}
export function chooseCall(x: number | null | undefined): number {
  //@ ensures x === null || x === undefined ==> \result === 7
  //@ ensures x !== null && x !== undefined && x > 0 ==> \result === x
  const chosen = x !== undefined && x !== null && positive(x)
    ? x : fallback(x === undefined || x === null || x <= 0);
  return chosen;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("coalescing and optional chaining preserve the correct sentinel", () => {
  const result = verify(String.raw`
interface Box { value: number | null }
export function coalesce(x: number | null | undefined): number | null {
  //@ ensures x === undefined || x === null ==> \result === null
  //@ ensures x !== undefined && x !== null ==> \result === x
  return x ?? null;
}
export function chain(x: Box | null): number | null | undefined {
  //@ ensures x === null ==> \result === undefined
  //@ ensures x !== null ==> \result === x.value
  return x?.value;
}
export function truthy(x: number | null | undefined): boolean {
  //@ ensures x === null || x === undefined ==> !\result
  //@ ensures x !== null && x !== undefined ==> (\result === (x !== 0))
  return !!x;
}
export function nullFallback(x: number | null | undefined): number | null {
  //@ ensures x === undefined || x === null || x === 0 ==> \result === null
  //@ ensures x !== undefined && x !== null && x !== 0 ==> \result === x
  return x || null;
}
export function scalarFallback(x: number): number | null {
  //@ ensures x === 0 ==> \result === null
  //@ ensures x !== 0 ==> \result === x
  return x || null;
}
export function sentinels(flag: boolean): null | undefined {
  //@ ensures flag ==> \result === null
  //@ ensures !flag ==> \result === undefined
  return flag ? null : undefined;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("collection results, callback defaults and conversions preserve null", () => {
  const result = verify(String.raw`
export function lookup(m: Map<string, number | null>, key: string): number {
  //@ ensures !m.has(key) ==> \result === 0
  //@ ensures m.has(key) && m.get(key) === null ==> \result === 1
  const value = m.get(key);
  if (value === undefined) return 0;
  return value === null ? 1 : 2;
}
export function defaults(xs: (number | null | undefined)[]): (number | null)[] {
  //@ ensures \result.length === xs.length
  //@ ensures forall(i, 0 <= i && i < xs.length ==> (xs[i] === null ==> \result[i] === null))
  //@ ensures forall(i, 0 <= i && i < xs.length ==> (xs[i] === undefined ==> \result[i] === 7))
  return xs.map((x = 7) => x);
}
export function compare(a: number | null, b: number | undefined): boolean {
  //@ requires a === null && b === undefined
  //@ ensures !\result
  return a === b;
}
export function widen(x: number | null): number | null | undefined {
  //@ ensures \result === x
  return x;
}
export function absent(x?: number | null): boolean {
  return x === undefined;
}
export function omitted(): boolean {
  //@ ensures \result
  return absent();
}
export function nullOnly(x?: null): boolean {
  return x === undefined;
}
export function omittedNullOnly(): boolean {
  //@ ensures \result
  return nullOnly();
}
interface Marker { id: number; value?: null }
export function omittedField(): Marker {
  //@ ensures \result.value === undefined
  return { id: 1 };
}
export function anonymous(flag: boolean): { value: number | null } | undefined {
  //@ ensures !flag ==> \result === undefined
  //@ ensures flag ==> \result !== undefined && \result.value === null
  return flag ? { value: null } : undefined;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("array lookup, find and pop preserve stored sentinels and absence", () => {
  const result = verify(String.raw`
interface Box { value: number | null }
export function at(xs: (number | null | undefined)[], i: number): number {
  //@ ensures i < 0 || i >= xs.length ==> \result === 9
  //@ ensures 0 <= i && i < xs.length ==> ((xs[i] === null || xs[i] === undefined) ==> \result === 9)
  return xs[i] ?? 9;
}
export function fieldAt(xs: (Box | null)[], i: number): number | null | undefined {
  //@ ensures i < 0 || i >= xs.length ==> \result === undefined
  //@ ensures 0 <= i && i < xs.length ==> (xs[i] === null ==> \result === undefined)
  return xs[i]?.value;
}
export function findNull(): boolean {
  //@ ensures \result
  const xs: (number | null | undefined)[] = [undefined, null, 7];
  const value = xs.find((x): boolean => x === null);
  return value === null;
}
export function popUndefined(): boolean {
  //@ ensures \result
  let xs: (number | undefined)[] = [undefined];
  const value = xs.pop();
  return value === undefined && xs.length === 0;
}
export function popNull(): boolean {
  //@ ensures \result
  let xs: (number | null | undefined)[] = [null];
  const value = xs.pop();
  return value === null && xs.length === 0;
}
export function popWiden(): boolean {
  //@ ensures \result
  let xs: (number | undefined)[] = [undefined];
  let value: number | null | undefined = null;
  value = xs.pop();
  return value === undefined && xs.length === 0;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

const leanProbe = spawnSync("lean", ["--version"], { encoding: "utf8", timeout: 10_000 });
test("Lean evaluates both sentinels and partial narrowing independently", {
  skip: (leanProbe.error as NodeJS.ErrnoException | undefined)?.code === "ENOENT",
}, () => {
  const dir = mkdtempSync(join(tmpdir(), "lsc-nullish-lean-"));
  try {
    const text = generate(narrowing, "lean") + `
example : Pure.classify none = 1 := by decide
example : Pure.classify (some none) = 2 := by decide
example : Pure.classify (some (some 9)) = 9 := by decide
example : Pure.reverse none = 1 := by decide
example : Pure.reverse (some none) = 2 := by decide
example : Pure.reverse (some (some 9)) = 9 := by decide
example : Pure.disjunction (some (some 9)) = 9 := by decide
example : Pure.retainNull (some none) = none := by decide
example : Pure.retainUndefined none = none := by decide
example : Pure.positive (some (some 1)) = true := by decide
example : Pure.positive (some none) = false := by decide
example : Pure.absentOrPositive none = true := by decide
example : Pure.absentOrPositive (some (some (-1))) = false := by decide
`;
    const file = join(dir, "Nullish.lean");
    writeFileSync(file, text);
    const result = spawnSync("lean", [file], { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    assert.equal(result.status, 0, result.stdout + result.stderr + text);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
