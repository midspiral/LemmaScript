import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function compile(source: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("narrowing.ts", source);
  const diags = project.getPreEmitDiagnostics();
  assert.equal(diags.length, 0, project.formatDiagnosticsWithColorAndContext(diags));
  const typed = narrowModule(resolveModule(extractModule(file)));
  const d = transformModuleDafny(typed);
  const dafnyMod = peepholeModule({ ...d.defFile, decls: [...(d.typesFile?.decls ?? []), ...d.defFile.decls] }, "dafny");
  const dafny = emitDafnyFile(dafnyMod);
  resetLeanModule();
  const l = transformModuleLean(typed);
  const leanTypes = l.typesFile ? emitLeanFile(peepholeModule(l.typesFile, "lean")) : "";
  const leanDef = emitLeanFile(peepholeModule(l.defFile, "lean"));
  return { dafny, leanTypes, leanDef };
}

function verifyDafny(dafny: string, symbol?: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-coercion-narrowing-"));
  try {
    const file = join(dir, "narrowing.dfy");
    writeFileSync(file, dafny);
    const res = spawnSync("dafny", [
      "verify", "--verification-time-limit=15",
      ...(symbol ? [`--filter-symbol=${symbol}`] : []),
      file,
    ], { encoding: "utf8", timeout: 120_000 });
    assert.ifError(res.error);
    return { status: res.status, output: res.stdout + res.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const ALL_ISSUES_SOURCE = `
export interface Box { tag: number; inner?: number; }
export interface Deep { b?: Box; }
export interface Leaf { value?: number; }
export interface Holder { inner?: Leaf; }
export interface Bag { items: number[]; }
export type Shape = { kind: "circle"; r: number } | { kind: "square"; s: number };

function idn(k: number): number { return k; }

// #354: optChain early return + nested optional field
//@ ensures b !== undefined && b.tag === 1 && b.inner !== undefined ==> \\result === b.inner
export function optChainGuardThenNestedOpt(b: Box | undefined): number {
  if (b?.tag !== 1) return 0;
  if (b.inner !== undefined) return b.inner;
  return 0;
}

// #354: field path early return + bind + nested optional
//@ ensures d.b !== undefined && d.b.inner !== undefined ==> \\result === d.b.inner
export function fieldGuardThenBindNestedOpt(d: Deep): number {
  if (d.b === undefined) return 0;
  const x = d.b;
  if (x.inner !== undefined) return x.inner;
  return 0;
}

// #353: lambda & while decreases read narrowed optional
//@ ensures o !== undefined ==> \\result.length === xs.length
export function closureReadsNarrowed(o: number | undefined, xs: number[]): number[] {
  if (o !== undefined) return xs.map((x) => x + o);
  return [];
}

//@ ensures o !== undefined && o >= 0 ==> \\result === o
export function whileDecreasesNarrowed(o: number | undefined): number {
  if (o !== undefined && o >= 0) {
    let i = 0;
    while (i < o) {
      //@ invariant 0 <= i && i <= o
      //@ decreases o - i
      i = i + 1;
    }
    return i;
  }
  return 0;
}

// #352 / #258: ?? and ?. on non-optional / narrowed values
//@ ensures \\result === x
export function nullishOnNonOpt(x: number): number { return x ?? 0; }

//@ ensures o !== undefined ==> \\result === o
export function nullishOnNarrowed(o: number | undefined): number {
  if (o !== undefined) return o ?? 0;
  return -1;
}

//@ ensures b !== undefined ==> \\result === b.tag
export function optChainOnNarrowed(b: Box | undefined): number {
  if (b !== undefined) return b?.tag ?? 0;
  return -1;
}

// #351: shadowing inside narrowed block
//@ ensures p === 99 ==> \\result === 1
export function shadowLetDirect(p: number | undefined): number {
  if (p !== undefined) { const p = 1; return p; }
  return 0;
}

// #350: mutating methods on narrowed optionals and their fields
//@ ensures p !== undefined && p.length === 0 ==> \\result === 1
export function pushOnNarrowed(p: number[] | undefined): number {
  let a = p;
  if (a !== undefined) { a.push(99); }
  return a !== undefined ? a.length : -1;
}

//@ ensures b !== undefined && b.items.length === 0 ==> \\result === 1
export function pushOnNarrowedField(b: Bag | undefined): number {
  let c = b;
  if (c !== undefined) { c.items.push(9); }
  return c !== undefined ? c.items.length : -1;
}

// #342: reassignment inside narrowed block
//@ ensures q.inner === 1 ==> \\result === false
export function reassignFieldParent(q: Box): boolean {
  let b: Box = q;
  if (b.inner !== undefined) { b = { tag: b.tag, inner: 7 }; return b.inner === 1; }
  return true;
}

//@ ensures p !== undefined ==> \\result === 5
export function reassignLocalInside(p: number | undefined): number {
  let o = p;
  if (o !== undefined) { o = 5; return o; }
  return 0;
}

// #341: parameter reassigned inside narrowed block & DU arm
//@ ensures o !== undefined ==> \\result === p + o
export function paramReassignOpt(p: number, o?: number): number {
  if (o !== undefined) { p = p + o; }
  return p;
}

export function paramReassignDU(p: number, sh: Shape): number {
  if (sh.kind === "circle") { p = p + sh.r; }
  return p;
}

// #340: assignment narrowing
//@ ensures \\result === 5
export function assignDirect(p?: number): number { let o = p; o = 5; return o; }

//@ ensures p !== undefined ==> \\result === p
//@ ensures p === undefined ==> \\result === 5
export function assignOutside(p?: number): number {
  let o = p;
  if (o === undefined) { o = 5; }
  return o;
}

//@ ensures p !== undefined ==> \\result === p
//@ ensures p === undefined ==> \\result === 5
export function assignNullish(p?: number): number { let o = p; o = o ?? 5; return o; }

// #339: while presence narrowing
export function whileIdx(a: number[], i?: number): number {
  let s = 0;
  while (i !== undefined && i >= 0 && i < a.length) {
    //@ invariant true
    //@ decreases i !== undefined ? 1 : 0
    s = a[i];
    i = undefined;
  }
  return s;
}

// #338: loose null checks and negated strict check
//@ ensures i !== undefined && i >= 0 && i < a.length ==> \\result === a[i]
export function looseIdx(a: number[], i?: number): number {
  if (i != null && i >= 0 && i < a.length) return a[i];
  return 0;
}

//@ ensures i !== undefined ==> \\result === i + 1
export function negatedStrictCheck(i?: number): number {
  if (!(i === undefined)) return i + 1;
  return 0;
}

// #304: null vs undefined distinctness (Nullish<T>)
//@ ensures x === undefined ==> \\result === 1
//@ ensures x === null ==> \\result === 2
//@ ensures x !== undefined && x !== null ==> \\result === x
export function classifyNullish(x: number | null | undefined): number {
  if (x === undefined) return 1;
  if (x === null) return 2;
  return x;
}

//@ ensures x === undefined ==> \\result === null
//@ ensures x === null ==> \\result === null
//@ ensures x != null ==> \\result === x
export function excludeUndefKeepNull(x: number | null | undefined): number | null {
  if (x === undefined) return null;
  return x;
}

// #268: && / || chains as values with calls and nested paths
//@ ensures o !== undefined ==> \\result === (o > x)
//@ ensures o === undefined ==> \\result === false
export function andChainCall(o: number | undefined, x: number): boolean {
  return o !== undefined && idn(o) > x;
}

export function andChainNestedPath(a: Holder, x: number): boolean {
  return a.inner !== undefined && a.inner.value !== undefined && idn(a.inner.value) > x;
}

//@ ensures o === undefined ==> \\result === true
//@ ensures o !== undefined ==> \\result === (o + 1 > x)
export function orChainArith(o: number | undefined, x: number): boolean {
  return o === undefined || o + 1 > x;
}

// Narrowed optional callback call
export function callNarrowedFn(cb: ((n: number) => number) | undefined, x: number): number {
  if (cb !== undefined) return cb(x);
  return x;
}

// Stateful Nullish method (exercises LemmaScript.nullishValue in Lean Velvet)
//@ ensures x === undefined ==> \\result === 1
//@ ensures x === null ==> \\result === 2
//@ ensures x != null ==> \\result === x + 1
export function statefulNullish(x: number | null | undefined): number {
  let out = 0;
  if (x === undefined) { out = 1; }
  else if (x === null) { out = 2; }
  else { out = x + 1; }
  return out;
}

// Phase 2: Optional discriminated union (narrowed in both optionality and variant)
//@ ensures sh !== undefined && sh.kind === "circle" ==> \\result === sh.r
//@ ensures sh !== undefined && sh.kind === "square" ==> \\result === sh.s
export function optDiscriminatedUnion(sh: Shape | undefined): number {
  if (sh === undefined) return 0;
  if (sh.kind === "circle") return sh.r;
  return sh.s;
}

// Phase 2: "field" in union check
//@ ensures sh.kind === "circle" ==> \\result === sh.r
export function inOperatorDU(sh: Shape): number {
  if ("r" in sh) return sh.r;
  return sh.s;
}

// Phase 2: switch on discriminated union (pure & stateful)
//@ ensures sh.kind === "circle" ==> \\result === sh.r + 1
//@ ensures sh.kind === "square" ==> \\result === sh.s + 2
export function switchDUStateful(sh: Shape): number {
  let out = 0;
  switch (sh.kind) {
    case "circle": out = sh.r + 1; break;
    case "square": out = sh.s + 2; break;
  }
  return out;
}

// Phase 2: Array.isArray + typeof + push on narrowed synth array-union
//@ ensures Array.isArray(v) ==> \\result === v.length + 1
//@ ensures !Array.isArray(v) ==> \\result === v.length
export function synthArrayUnionPush(v: string | number[]): number {
  let cur = v;
  if (Array.isArray(cur)) {
    cur.push(42);
    return cur.length;
  }
  return typeof cur === "string" ? cur.length : 0;
}
`;

test("coercion narrowing verifies all 14 narrowing/nullish issues + Phase 2 DU/Array.isArray in Dafny and emits clean Lean", () => {
  const { dafny, leanTypes, leanDef } = compile(ALL_ISSUES_SOURCE);
  assert.match(dafny, /datatype Nullish<T> = Undefined \| Null \| Value\(value: T\)/);
  assert.match(leanTypes, /LemmaScript\.Nullish Int/);
  assert.match(leanTypes, /x\.excludeUndefined \(by grind\)/);
  assert.match(leanTypes, /attribute \[grind cases\] Shape/);
  assert.match(leanTypes, /Shape\.is_circle/);
  assert.match(leanTypes, /Shape\.proj_circle_r/);
  assert.match(leanDef, /LemmaScript\.optionValue/);
  assert.match(leanDef, /LemmaScript\.nullishValue/);
  const res = verifyDafny(dafny);
  assert.equal(res.status, 0, res.output);
});

const SOUNDNESS_NEGATIVE_CASES: [string, string][] = [
  ["#349 optional comparison must check RHS call precondition even when LHS is undefined", `
    //@ requires 0 <= i && i < xs.length
    function at(xs: number[], i: number): number { return xs[i]; }
    //@ requires x !== undefined ==> 0 <= i && i < xs.length
    //@ ensures x === undefined ==> \\result === true
    export function bug(x: number | undefined, xs: number[], i: number): boolean {
      return x !== at(xs, i);
    }
  `],
  ["#349 optChain early return must check RHS call precondition when receiver is undefined", `
    type Box = { val: number };
    //@ requires 0 <= i && i < xs.length
    function at(xs: number[], i: number): number { return xs[i]; }
    //@ requires x !== undefined ==> 0 <= i && i < xs.length
    export function bug(x: Box | undefined, xs: number[], i: number): number {
      if (x?.val !== at(xs, i)) return 1;
      return 2;
    }
  `],
  ["#349 or-chain early return must check middle call precondition when later disjunct is undefined", `
    type Box = { val: number };
    //@ requires 0 <= i && i < xs.length
    function at(xs: number[], i: number): number { return xs[i]; }
    //@ requires (x !== undefined && y !== undefined) ==> 0 <= i && i < xs.length
    export function bug(x: Box | undefined, y: Box | undefined, xs: number[], i: number): number {
      if (x === undefined || at(xs, i) > 0 || y === undefined) return 0;
      return x.val + y.val;
    }
  `],
  ["#342 field parent reassignment cannot retain stale narrowed value", `
    interface OptBox { v?: number }
    //@ ensures q.v === 1 ==> \\result === true
    export function bug(q: OptBox): boolean {
      let b: OptBox = q;
      if (b.v !== undefined) { b = { v: 7 }; return b.v === 1; }
      return true;
    }
  `],
  ["#350 push on narrowed optional cannot leave storage unchanged", `
    //@ ensures p !== undefined && p.length === 0 ==> \\result === 0
    export function bug(p: number[] | undefined): number {
      let a = p;
      if (a !== undefined) { a.push(99); }
      return a !== undefined ? a.length : -1;
    }
  `],
  ["#351 shadowing inside narrowed block cannot return outer narrowed value", `
    //@ ensures p === 99 ==> \\result === 99
    export function bug(p: number | undefined): number {
      if (p !== undefined) { const p = 1; return p; }
      return 0;
    }
  `],
  ["#304 null cannot match undefined check on T | null | undefined", `
    //@ ensures x === null ==> \\result === 1
    export function bug(x: number | null | undefined): number {
      if (x === undefined) return 1;
      return 0;
    }
  `],
];

for (const [label, source] of SOUNDNESS_NEGATIVE_CASES) {
  test(`soundness: Dafny rejects false proof (${label})`, () => {
    const { dafny } = compile(source);
    const res = verifyDafny(dafny);
    assert.notEqual(res.status, 0, `expected Dafny verification failure for ${label}\n${dafny}`);
  });
}
