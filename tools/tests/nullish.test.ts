import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { peepholeModule } from "../src/peephole.ts";
import { parseTsType } from "../src/types.ts";

function generate(code: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("nullish-regression.ts", code);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  const typed = narrowModule(resolveModule(extractModule(source)));
  const { typesFile, defFile } = transformModuleDafny(typed);
  const output = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny");
  return emitDafnyFile(output);
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

const narrowing = readFileSync(new URL("../../examples/nullish.ts", import.meta.url), "utf8");

test("three-case values use named cases while single-sentinel options retain their encoding", () => {
  const text = generate(narrowing);
  assert.match(text, /datatype Nullish<T> = Undefined \| Null \| Value\(value: T\)/);
  assert.match(text, /function isUndefined\(x: Nullish<int>\): bool\s*\{\s*x\.Undefined\?/);
  assert.match(text, /function isNull\(x: Nullish<int>\): bool\s*\{\s*x\.Null\?/);
  assert.match(text, /function widenUndefined\(x: Option<int>\): Nullish<int>/);
  assert.match(text, /function widenNull\(x: Option<int>\): Nullish<int>/);
});

test("a source type named Nullish does not collide with the generated carrier", () => {
  const result = verify(String.raw`
interface Nullish { value: number }
export function extract(x: Nullish | null | undefined): number {
  //@ ensures x === undefined ==> \result === 1
  //@ ensures x === null ==> \result === 2
  //@ ensures x !== undefined && x !== null ==> \result === x.value
  if (x === undefined) return 1;
  if (x === null) return 2;
  return x.value;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("partial narrowing, either check order, and disjunctive early returns verify", () => {
  const result = verify(narrowing);
  assert.equal(result.status, 0, result.output + result.text);
});

test("guarded specification lookups keep direct optional comparisons", () => {
  const result = verify(String.raw`
interface Row { value: number }
export function lookup(m: Map<string, number>, key: string): number | undefined {
  //@ ensures m.has(key) ==> \result === m.get(key)
  return m.get(key);
}
export function requireRows(rows: Row[], m: Record<string, number>, key: string): boolean {
  //@ requires forall(i: nat, i < rows.length ==> rows[i].value === m[key])
  return true;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
  assert.match(result.text, /i_value == m\[key\]/);
  assert.match(result.text, /i_value == rows\[i\]\.value/);
  assert.doesNotMatch(result.text, /var i_optional/);
});

test("absent operands cannot hide unguarded or shadowed lookup obligations", () => {
  for (const code of [String.raw`
export function absent(m: Map<string, number>, key: string): number | undefined {
  //@ requires !m.has(key)
  //@ ensures \result !== m.get(key)
  return undefined;
}
`, String.raw`
export function absent(xs: number[]): number | undefined {
  //@ requires xs.length === 0
  //@ ensures \result !== xs[0]
  return undefined;
}
`, String.raw`
export function shadowed(xs: number[], m: Record<string, number>, key: string): boolean {
  //@ requires xs.length === 1 && !(key in m)
  //@ ensures forall(i: nat, i < xs.length ==> forall(i: nat, xs[i] !== m[key]))
  return true;
}
`]) {
    const result = verify(code);
    assert.notEqual(result.status, 0, result.text);
    assert.match(result.output, /out of range|domain|index/, result.output);
  }
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

test("optional-chain exit guards narrow subsequent reads and disjunction operands", () => {
  const result = verify(String.raw`
interface Row { key: string; amount: number }
export function guarded(row: Row | undefined): number {
  //@ ensures row === undefined ==> \result === 0
  //@ ensures row !== undefined && row.key === "ok" ==> \result === row.amount
  if (row?.key !== "ok") return 0;
  return row.amount;
}
export function disjunction(row: Row | null | undefined): number {
  //@ ensures \result >= 0
  if (row?.key !== "ok" || row.amount <= 0) return 0;
  return row.amount;
}
export function undefinedGuard(row: Row | undefined): boolean {
  //@ ensures row === undefined ==> \result
  if (row?.key !== undefined) return false;
  return row === undefined;
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

const reassigned = String.raw`
export function absentBranch(init: number | undefined, other: number | undefined): number | undefined {
  //@ ensures init === undefined ==> \result === RESULT
  let x: number | undefined = init;
  if (x === undefined) { x = other; return x; }
  return x;
}
export function presentBranch(init: number | undefined, other: number | undefined): number | undefined {
  //@ ensures init !== undefined ==> \result === other
  let x: number | undefined = init;
  if (x !== undefined) { x = other; return x; }
  return x;
}
export function afterGuard(init: number | undefined, other: number | undefined, c: boolean): number | undefined {
  //@ ensures init !== undefined && c ==> \result === other
  //@ ensures init !== undefined && !c ==> \result === init
  let x: number | undefined = init;
  if (x === undefined) return 0;
  if (c) { x = other; }
  return x;
}
export function nullBranch(init: number | null | undefined, other: number | null | undefined): number | null | undefined {
  //@ ensures init === null ==> \result === other
  //@ ensures init !== null ==> \result === init
  let x: number | null | undefined = init;
  if (x === null) { x = other; return x; }
  return x;
}
export function inLoop(init: number | undefined, n: number): number | undefined {
  //@ requires n >= 0
  //@ ensures init !== undefined && n > 0 ==> \result === undefined
  let x: number | undefined = init;
  if (x === undefined) return 0;
  let i = 0;
  while (i < n) {
    //@ invariant 0 <= i && i <= n
    //@ invariant i > 0 ==> x === undefined
    x = undefined;
    i = i + 1;
  }
  return x;
}
`;

test("assigning a narrowed variable targets its declared type and ends the narrowing", () => {
  const stale = verify(reassigned.replace("RESULT", "undefined"));
  assert.notEqual(stale.status, 0, stale.text);
  assert.match(stale.output, /postcondition could not be proved/, stale.output);
  assert.doesNotMatch(stale.output, /resolution\/type errors/, stale.output);
  const correct = verify(reassigned.replace("RESULT", "other"));
  assert.equal(correct.status, 0, correct.output + correct.text);
});

test("writes invalidate field paths and branch joins without discarding terminating-branch facts", () => {
  const result = verify(String.raw`
interface Box { value: number | undefined }
export class FieldBox {
  value: number | undefined;
  update(other: number | undefined): number | undefined {
    //@ ensures \result === other
    if (this.value === undefined) {
      this.value = other;
      return this.value;
    }
    this.value = other;
    return this.value;
  }
}
export function parent(init: number | undefined, other: number | undefined, c: boolean): number | undefined {
  //@ ensures init !== undefined && c ==> \result === other
  //@ ensures init !== undefined && !c ==> \result === init
  let b: Box = { value: init };
  if (b.value === undefined) return 0;
  if (c) b = { value: other };
  return b.value;
}
export function exiting(init: number | undefined, c: boolean): number {
  //@ ensures init !== undefined && !c ==> \result === init
  let x: number | undefined = init;
  if (x === undefined) return 0;
  if (c) { x = undefined; return 0; }
  return x;
}
export function iterations(init: number | undefined, n: number): number | undefined {
  //@ requires n >= 0
  //@ ensures init !== undefined && n > 0 ==> \result === undefined
  let x: number | undefined = init;
  if (x === undefined) return 0;
  let i = 0;
  while (i < n) {
    //@ invariant 0 <= i && i <= n
    //@ invariant i > 0 ==> x === undefined
    if (i === 0) { x = undefined; i = i + 1; continue; }
    i = i + 1;
  }
  return x;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("inferred array types preserve union precedence through aliases and nested arrays", () => {
  const result = verify(String.raw`
type Values = (number | null)[];
export function aliases(xs: Values): number {
  //@ requires xs.length > 0
  //@ ensures xs[0] === null ==> \result === 0
  const value = xs[0];
  return value === null ? 0 : value;
}
export function nested(): boolean {
  //@ ensures \result
  const values = [[null, 7]];
  const row = values[0];
  return row[0] === null && row[1] === 7;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("a type-guard find keeps the element carried by its model result", () => {
  const result = verify(String.raw`
export function findNullish(xs: (number | null)[]): number {
  //@ ensures xs.length === 0 ==> \result === 0
  //@ ensures \result !== 2
  const v = xs.find(x => x === null);
  if (v === undefined) return 0;
  if (v === null) return 1;
  return 2;
}
export function findsNull(): boolean {
  //@ ensures \result
  return findNullish([null]) === 1 && findNullish([4]) === 0;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("filtering undefined out of three-case elements keeps null", () => {
  const result = verify(String.raw`
export function defined(xs: (number | null | undefined)[]): (number | null)[] {
  //@ ensures \result.length <= xs.length
  return xs.filter(x => x !== undefined);
}
export function keepsNull(): boolean {
  //@ ensures \result
  const xs: (number | null | undefined)[] = [undefined, null, 7];
  const ys = xs.filter(x => x !== undefined);
  return ys.length === 2 && ys[0] === null && ys[1] === 7;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("a conjunction of presence checks narrows the then-branch beside an else", () => {
  const result = verify(String.raw`
export function both(x: number | null | undefined): number {
  //@ ensures x === null || x === undefined ==> \result === 0
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x !== null && x !== undefined) { return x; } else { return 0; }
}
export function guarded(x: number | undefined, c: boolean): number {
  //@ ensures x !== undefined && c ==> \result === x
  if (x !== undefined && c) { return x; } else { return 0; }
}
export function effects(x: number | null | undefined, c: boolean): number {
  //@ ensures !c ==> \result === 0
  let r = 1;
  if (x !== undefined && c && x !== null) { r = x; } else { r = 0; }
  return r;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("Lean sentinel tests do not require decidable equality on the payload", () => {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("nullish-lean.ts", String.raw`
export function isNull(x: Map<number, number> | null | undefined): boolean {
  return x === null;
}
export function isDefined(x: Map<number, number> | null | undefined): boolean {
  return x !== undefined;
}
`);
  const { typesFile } = transformModuleLean(narrowModule(resolveModule(extractModule(source))));
  resetLeanModule();
  const text = emitLeanFile(peepholeModule(typesFile!, "lean"));
  assert.match(text, /match x with[\s\S]*\| \.Null =>\s+true/);
  assert.match(text, /match x with[\s\S]*\| \.Undefined =>\s+false/);
  assert.doesNotMatch(text, /[=≠] LemmaScript\.Nullish\./);
});

test("copied else branches retain optional returns, initializers, and call arguments", () => {
  const result = verify(String.raw`
export function reviewed(x: number | undefined, c: boolean): number | undefined {
  //@ ensures c ==> \result === undefined
  //@ ensures !c ==> \result === x
  if (x !== undefined && c) return x === undefined ? 0 : undefined;
  else return x;
}
function identity(x: number | null | undefined): number | null | undefined {
  return x;
}
export function partial(x: number | null | undefined, c: boolean): number | null | undefined {
  //@ ensures \result === x
  if (x !== undefined && c) { return x; }
  else { const value = x; return identity(value); }
}
export function nullable(x: number | null, c: boolean): number | null {
  //@ ensures \result === x
  if (x !== null && c) { return x; } else { return x; }
}
interface Box { value: number | null | undefined }
export function field(box: Box, c: boolean): number | null | undefined {
  //@ ensures \result === box.value
  if (box.value !== null && c) { return box.value; }
  else { return identity(box.value); }
}
export function reassignedElse(init: number | null | undefined, other: number | null | undefined, c: boolean): number | null | undefined {
  //@ ensures init !== undefined && c ==> \result === init
  //@ ensures init === undefined || !c ==> \result === other
  let x = init;
  if (x !== undefined && c) { return x; }
  else { x = other; return x; }
}
export function nested(x: number | null | undefined, c: boolean): number {
  //@ ensures x === null || x === undefined ==> \result === 0
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x !== undefined && c) { return x ?? 0; }
  else {
    if (x === undefined) return 0;
    if (x === null) return 0;
    return x;
  }
}
export function coalesced(x: number | null | undefined, c: boolean): number {
  //@ ensures x === null || x === undefined ==> \result === 0
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x !== undefined && c) { return x ?? 0; } else { return x ?? 0; }
}
export function callCoalesced(x: number | null | undefined, c: boolean): number {
  //@ ensures x === null || x === undefined ==> \result === 0
  //@ ensures x !== null && x !== undefined ==> \result === x
  if (x !== undefined && c) { return x ?? 0; } else { return identity(x) ?? 0; }
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});
