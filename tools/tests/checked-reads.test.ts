import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile } from "../src/lean-emit.ts";
import {
  createImperativeCounts,
  evaluateImperativeProgram,
  type ImperativeProgram,
} from "../fuzz/imperative-oracle.ts";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

test("Milestone 4 (#52): #349 precondition preservation across ===, !==, and relational comparisons without pi comparison-temp churn", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m4-349-"));
  const guardDef = [
    "//@ requires ok",
    "export function guard(ok: boolean, v: number): number { return v; }",
  ].join("\n");

  const programs: ImperativeProgram[] = [
    {
      family: "guard-eval",
      label: "eq-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x === guard(false, 1); }`,
      inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
    },
    {
      family: "guard-eval",
      label: "neq-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x !== guard(false, 1); }`,
      inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
    },
    {
      family: "guard-eval",
      label: "lt-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x !== undefined && x < guard(false, 1); }`,
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 0 }] },
      ],
    },
    {
      family: "guard-eval",
      label: "le-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x !== undefined && x <= guard(false, 1); }`,
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 1 }] },
      ],
    },
  ];

  try {
    for (const prog of programs) {
      const out = evaluateImperativeProgram(prog, {
        project,
        workDir,
        counts: createImperativeCounts(),
        timeoutSec: 15,
        stages: ["pre", "opt"],
      });
      assert.equal(out.ok, true, `${prog.label} failed (${out.oracle}): ${out.detail}`);
    }

    // Pure comparison (`x === "bytes"`) emits zero `i_compare` temporary churn.
    const sf = project.createSourceFile(
      "pi_pure_cmp.ts",
      `export function isBytes(truncatedBy?: string): boolean { return truncatedBy === "bytes"; }`,
      { overwrite: true },
    );
    const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(sf))));
    const dfy = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "pi_pure_cmp.ts");
    assert.ok(!dfy.includes("i_compare"), `unexpected comparison temp churn:\n${dfy}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("Milestone 4 (#52): #340 definite assignment narrowing, #339 while presence narrowing, and #268 &&/|| chains verify in Dafny and emit clean Lean", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m4-reads-"));
  const programs: ImperativeProgram[] = [
    {
      family: "reassign",
      label: "issue-340-if-undefined-assign",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(x?: number): number {",
        "  let v: number | undefined = x;",
        "  if (v === undefined) {",
        "    v = 6;",
        "  }",
        "  return v + 3;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 4 }] },
      ],
    },
    {
      family: "reassign",
      label: "issue-340-direct-assign-clear-reassign",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(x?: number): number {",
        "  let v: number | undefined = x;",
        "  v = 6;",
        "  const first = v + 1;",
        "  v = undefined;",
        "  return v !== undefined ? v : first;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 9 }] },
      ],
    },
    {
      family: "reassign",
      label: "issue-268-return-and-and-or-chains",
      fnName: "target",
      returnKind: "boolean",
      tsText: [
        "export function target(x: number, o?: number): boolean {",
        "  return o !== undefined && x < o;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "int", value: 3 }, { kind: "opt-int", value: undefined }] },
        { args: [{ kind: "int", value: 3 }, { kind: "opt-int", value: 5 }] },
        { args: [{ kind: "int", value: 7 }, { kind: "opt-int", value: 5 }] },
      ],
    },
  ];

  try {
    for (const prog of programs) {
      const out = evaluateImperativeProgram(prog, {
        project,
        workDir,
        counts: createImperativeCounts(),
        timeoutSec: 15,
        stages: ["pre", "opt"],
      });
      assert.equal(out.ok, true, `${prog.label} failed (${out.oracle}): ${out.detail}`);
    }

    // #339 while presence narrowing with contract verified end-to-end via `lsc check --backend=dafny`.
    const whileSrc = [
      "export function target(start?: number): number {",
      "  //@ ensures \\result >= 0",
      "  let cur: number | undefined = start;",
      "  let steps = 0;",
      "  let total = 0;",
      "  while (cur !== undefined && cur >= 0 && steps < 3) {",
      "    //@ invariant steps >= 0 && total >= 0",
      "    //@ decreases 3 - steps",
      "    total = total + cur;",
      "    steps = steps + 1;",
      "    cur = cur > 0 ? cur - 1 : undefined;",
      "  }",
      "  return total;",
      "}",
    ].join("\n");
    const whileFile = path.join(workDir, "while_presence.ts");
    writeFileSync(whileFile, whileSrc);
    const whileRes = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", whileFile], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    });
    assert.equal(whileRes.status, 0, `${whileRes.stdout}\n${whileRes.stderr}`);

    // Lean emission uses `.get (by grind)` for pure `checkedUnwrap` without removing Pure companions.
    const sf = project.createSourceFile(
      "lean_checked.ts",
      `export function cmpAnd(x: number, o?: number): boolean { return o !== undefined && x < o; }`,
      { overwrite: true },
    );
    const leanMod = transformModuleLean(narrowModule(resolveModule(extractModule(sf))));
    const leanTypes = leanMod.typesFile ? emitLeanFile(leanMod.typesFile) : "";
    const leanDef = emitLeanFile(leanMod.defFile);
    assert.match(leanTypes, /\.get \(by grind\)/, `expected Lean checked Option.get in typesFile:\n${leanTypes}`);
    assert.match(leanDef, /Pure\.cmpAnd/, `expected Pure companion preserved in Lean defFile:\n${leanDef}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("Milestone 4 (#52): upstream reproductions #342, #352, #353, #354 verify cleanly via lsc check --backend=dafny", () => {
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m4-upstream-"));
  const cases: Array<{ name: string; code: string }> = [
    {
      name: "issue_342.ts",
      code: [
        "interface C { v: number }",
        "export function f1(a?: number): number {",
        "  //@ ensures \\result === 10",
        "  if (a !== undefined) { a = 10; return a; }",
        "  return 10;",
        "}",
        "export function f2(c?: C): number {",
        "  //@ ensures c !== undefined ==> \\result === 1",
        "  if (c !== undefined) { c.v = 1; }",
        "  return c !== undefined ? c.v : 0;",
        "}",
        "export function f3(a?: number): number {",
        "  //@ ensures \\result === 0",
        "  if (a !== undefined) { a = undefined; return a !== undefined ? a : 0; }",
        "  return 0;",
        "}",
      ].join("\n"),
    },
    {
      name: "issue_352.ts",
      code: [
        "export function nullishPlain(x: number): number {",
        "  //@ ensures \\result === x",
        "  return x ?? 0;",
        "}",
        "export function nullishNarrowed(o?: number): number {",
        "  //@ ensures o !== undefined ==> \\result === o",
        "  if (o !== undefined) { return o ?? 0; }",
        "  return -1;",
        "}",
        "export function optChainPlain(s: string): number {",
        "  //@ ensures \\result === s.length",
        "  return s?.length;",
        "}",
      ].join("\n"),
    },
    {
      name: "issue_353.ts",
      code: [
        "export function f1(xs: number[], o?: number): number[] {",
        "  if (o !== undefined) { return xs.map(x => x + o); }",
        "  return xs;",
        "}",
        "export function f2(n?: number): number {",
        "  if (n !== undefined && n >= 0) {",
        "    let i = 0;",
        "    while (i < n) {",
        "      //@ invariant 0 <= i && i <= n",
        "      //@ decreases n - i",
        "      i = i + 1;",
        "    }",
        "    return i;",
        "  }",
        "  return 0;",
        "}",
      ].join("\n"),
    },
    {
      name: "issue_354.ts",
      code: [
        "export interface Box { tag: number; inner?: number }",
        "export interface Deep { b?: Box }",
        "export function f1(b?: Box): number {",
        "  //@ ensures b !== undefined && b.tag === 1 && b.inner !== undefined ==> \\result === b.inner",
        "  if (b?.tag !== 1) return 0;",
        "  if (b.inner !== undefined) return b.inner;",
        "  return 0;",
        "}",
        "export function f2(d: Deep): number {",
        "  //@ ensures d.b !== undefined && d.b.inner !== undefined ==> \\result === d.b.inner",
        "  if (d.b === undefined) return 0;",
        "  if (d.b.inner !== undefined) return d.b.inner;",
        "  return 0;",
        "}",
      ].join("\n"),
    },
  ];
  try {
    for (const c of cases) {
      const f = path.join(workDir, c.name);
      writeFileSync(f, c.code);
      const res = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", f], {
        cwd: repoRoot,
        encoding: "utf8",
        env: { ...process.env, LSC_RUN_LOG: "false" },
        timeout: 60_000,
      });
      assert.equal(res.status, 0, `${c.name} failed:\n${res.stdout}\n${res.stderr}`);
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("Milestone 4 (#52): review regressions — Lean dependent checkedUnwrap & nested _cmp, control-flow invalidation, nested someMatch/tagMatch/push, clearing guards, and non-optional ?./??", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m4-review-"));
  try {
    // Findings 1 & 7: Lean dependent `if _h :` for `&&`/`||`/`?:` containing checkedUnwrap,
    // plus parenthesized `(let _cmp0 := ...; ...)` inside function calls. Verify with real `lean` CLI!
    const leanSf = project.createSourceFile(
      "lean_checked_regressions.ts",
      [
        "//@ pure",
        "export function myGuard(ok: boolean, v: number): number {",
        "  //@ requires ok",
        "  return v;",
        "}",
        "//@ pure",
        "export function idb(b: boolean): boolean { return b; }",
        "//@ pure",
        "export function cmpAnd(a: number | undefined, b: number | undefined): boolean {",
        "  return a !== undefined && b !== undefined && a < b;",
        "}",
        "//@ pure",
        "export function cmpOr(a: number | undefined): boolean {",
        "  return a === undefined || a + 1 > 0;",
        "}",
        "//@ pure",
        "export function nestedCmp(x: number | undefined): boolean {",
        "  return idb(x === myGuard(true, 1));",
        "}",
      ].join("\n"),
      { overwrite: true },
    );
    const leanMod = transformModuleLean(narrowModule(resolveModule(extractModule(leanSf))));
    const leanTypes = leanMod.typesFile ? emitLeanFile(leanMod.typesFile) : "";
    const pureMatch = leanTypes.match(/namespace Pure[\s\S]*?end Pure/);
    assert.ok(pureMatch, `expected Pure namespace in Lean output:\n${leanTypes}`);
    assert.match(pureMatch[0], /if _h\d+ : /, `expected dependent if _hN : guard for Lean checkedUnwrap:\n${pureMatch[0]}`);
    assert.match(pureMatch[0], /\(let _cmp\d+ := /, `expected parenthesized (let _cmpN := ...; ...) in Lean:\n${pureMatch[0]}`);
    const leanProbe = spawnSync("lean", ["--version"], { encoding: "utf8", timeout: 10_000 });
    if (leanProbe.status === 0) {
      const leanFile = path.join(workDir, "lean_checked_regressions.lean");
      writeFileSync(leanFile, pureMatch[0] + "\n");
      const leanRes = spawnSync("lean", [leanFile], { encoding: "utf8", timeout: 60_000 });
      assert.equal(leanRes.status, 0, `Lean failed to check emitted Pure defs:\n${pureMatch[0]}\n${leanRes.stdout}\n${leanRes.stderr}`);
    }

    // Findings 2–6: Dafny end-to-end verification via compiled CLI
    const dafnyCases: Array<{ name: string; code: string; expectPass: boolean }> = [
      {
        name: "f2_invalidation_and_presence.ts",
        expectPass: true,
        code: [
          "export function f2a(a: number | undefined): number {",
          "  let x: number | undefined = a;",
          "  x = 1;",
          "  if (x === undefined) { return 0; }",
          "  return x + 1;",
          "}",
          "export function f2b(a: number | undefined, flag: boolean): number {",
          "  let x: number | undefined = a;",
          "  x = 1;",
          "  if (flag) { x = undefined; }",
          "  if (x !== undefined) { return x; }",
          "  return 0;",
          "}",
          "export function f2c(a: number | undefined, n: number): number {",
          "  //@ requires n >= 0",
          "  let x: number | undefined = a;",
          "  x = 1;",
          "  let i = 0;",
          "  while (i < n) {",
          "    //@ invariant i >= 0",
          "    //@ decreases n - i",
          "    if (x !== undefined) { x = undefined; }",
          "    i = i + 1;",
          "  }",
          "  return x !== undefined ? x : 0;",
          "}",
        ].join("\n"),
      },
      {
        name: "f3_checked_unwrap_paths_and_push.ts",
        expectPass: true,
        code: [
          "interface Node { inner: number | undefined; }",
          "type Shape = { kind: 'a'; v: number } | { kind: 'b'; w: number };",
          "export function f3a(n: Node | undefined): number {",
          "  let cur: Node | undefined = n;",
          "  let total = 0;",
          "  let steps = 0;",
          "  while (cur !== undefined && steps < 1) {",
          "    //@ invariant steps >= 0",
          "    //@ decreases 1 - steps",
          "    if (cur.inner !== undefined) { total = total + cur.inner; }",
          "    cur = undefined;",
          "    steps = steps + 1;",
          "  }",
          "  return total;",
          "}",
          "export function f3b(s: Shape | undefined): number {",
          "  let cur: Shape | undefined = s;",
          "  let out = 0;",
          "  let steps = 0;",
          "  while (cur !== undefined && steps < 1) {",
          "    //@ invariant steps >= 0",
          "    //@ decreases 1 - steps",
          "    if (cur.kind === 'a') { out = cur.v; } else { out = cur.w; }",
          "    cur = undefined;",
          "    steps = steps + 1;",
          "  }",
          "  return out;",
          "}",
          "export function f3c(xs: number[] | undefined): number {",
          "  let a: number[] | undefined = xs;",
          "  let i = 0;",
          "  while (a !== undefined && i < 1) {",
          "    //@ invariant i >= 0",
          "    //@ decreases 1 - i",
          "    a.push(2);",
          "    i = i + 1;",
          "  }",
          "  return a !== undefined ? a.length : 0;",
          "}",
        ].join("\n"),
      },
      {
        name: "f4_f5_f6_assign_clear_nonopt.ts",
        expectPass: true,
        code: [
          "interface Box { v: number; }",
          "export function f4a(flag: boolean): number {",
          "  let x: number | undefined = undefined;",
          "  if (x === undefined) {",
          "    x = 1;",
          "    if (flag) { x = undefined; }",
          "  }",
          "  return x !== undefined ? x : 0;",
          "}",
          "export function f4b(b: Box | undefined): number {",
          "  let cur: Box | undefined = b;",
          "  if (cur === undefined) { cur = { v: 7 }; }",
          "  return cur.v;",
          "}",
          "export function f5(a: number | undefined, b: number): number {",
          "  let x: number | undefined = a;",
          "  if (x !== undefined && b > 0) {",
          "    x = undefined;",
          "    return x !== undefined ? x : -1;",
          "  }",
          "  return 0;",
          "}",
          "export function f6(b: Box): number {",
          "  const x = b?.v;",
          "  const y = x ?? 0;",
          "  return x + y;",
          "}",
        ].join("\n"),
      },
      {
        name: "f7_relational_guard_rejected.ts",
        expectPass: false,
        code: [
          "//@ pure",
          "export function guard(ok: boolean, v: number): number {",
          "  //@ requires ok",
          "  return v;",
          "}",
          "export function badRel(x: number | undefined): boolean {",
          "  return x < guard(false, 1);",
          "}",
        ].join("\n"),
      },
    ];
    for (const c of dafnyCases) {
      const f = path.join(workDir, c.name);
      writeFileSync(f, c.code);
      const res = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", f], {
        cwd: repoRoot,
        encoding: "utf8",
        env: { ...process.env, LSC_RUN_LOG: "false" },
        timeout: 60_000,
      });
      if (c.expectPass) {
        assert.equal(res.status, 0, `${c.name} should verify:\n${res.stdout}\n${res.stderr}`);
      } else {
        assert.notEqual(res.status, 0, `${c.name} must be rejected by Dafny:\n${res.stdout}\n${res.stderr}`);
      }
    }

    // Brownfield zero-drift checks:
    // 1. Spec-clause optional comparison (`ensures`) must not emit `_cmp` temporaries.
    // 2. Single-optional comparison with independent LHS (`excludeTag === undefined || getTagId(t) !== excludeTag`)
    //    must keep native `match` lowering instead of `.value`.
    const driftSf = project.createSourceFile(
      "brownfield_zero_drift.ts",
      [
        "interface Tag { id: number; }",
        "export function getTagId(t: Tag): number { return t.id; }",
        "export function specNoCmp(arr: number[], x: number | undefined): boolean {",
        "  //@ requires arr.length > 0",
        "  //@ ensures \\result === (x === arr[0])",
        "  return x === arr[0];",
        "}",
        "export function orNativeMatch(t: Tag, excludeTag?: number): boolean {",
        "  return excludeTag === undefined || getTagId(t) !== excludeTag;",
        "}",
      ].join("\n"),
      { overwrite: true },
    );
    const dafnyMod = transformModuleDafny(narrowModule(resolveModule(extractModule(driftSf))));
    const dafnyOut = emitDafnyFile(dafnyMod.defFile);
    const specLine = dafnyOut.split("\n").find(l => l.includes("ensures"));
    assert.ok(specLine && !specLine.includes("_cmp"), `spec clause must not introduce _cmp:\n${dafnyOut}`);
    assert.doesNotMatch(dafnyOut, /excludeTag\.value/, `single-opt comparison with independent call must keep native match:\n${dafnyOut}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
