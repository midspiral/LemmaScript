import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import fc from "fast-check";
import { Project, ScriptTarget } from "ts-morph";
import { compileDafnyVariants } from "../fuzz/narrowing-fuzz.ts";
import {
  IMPERATIVE_FAMILIES,
  IMPERATIVE_SCHEMA,
  createImperativeCounts,
  evaluateImperativeProgram,
  executeImperativeInNode,
  imperativeArgToDafny,
  imperativeProgramArb,
  replaySavedImperativeCase,
  runBatchedDafnyFastScreen,
  runImperativeCampaign,
  saveImperativeCase,
  type ImperativeProgram,
} from "../fuzz/imperative-oracle.ts";

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

test("generator produces 100 valid TypeScript modules across all 7 imperative/mutation/nullish/union/alias/guard families (#46)", () => {
  const project = makeProject();
  const samples = fc.sample(imperativeProgramArb(IMPERATIVE_FAMILIES), { seed: 42, numRuns: 100 });
  assert.equal(samples.length, 100);

  const seenFamilies = new Set<string>();
  for (let i = 0; i < samples.length; i++) {
    const prog = samples[i];
    seenFamilies.add(prog.family);
    const sf = project.createSourceFile(`smoke_${i}.ts`, prog.tsText, { overwrite: true });
    const diags = sf.getPreEmitDiagnostics();
    project.removeSourceFile(sf);
    assert.equal(diags.length, 0, `invalid TS in ${prog.family}/${prog.label}:\n${prog.tsText}`);

    // Every input must execute cleanly in Node (either a valid value or intentional precondition-violated).
    for (const inp of prog.inputs) {
      const res = executeImperativeInNode(prog.tsText, prog.fnName, inp, prog.returnKind);
      assert.notEqual(res.kind, "runtime-error", `runtime error in ${prog.family}/${prog.label}: ${res.kind === "runtime-error" ? res.detail : ""}`);
    }
  }
  for (const fam of IMPERATIVE_FAMILIES) {
    assert.ok(seenFamilies.has(fam), `expected family ${fam} to appear in 100-module smoke sample`);
  }
});

test("negated-postcondition refutation oracle verifies #304 and #350 fixed and rejects live-alias mutation (#46, #49, #50, #304)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-imp-refute-"));
  try {
    // 1. #350 is now fixed by Milestone 3a Place write-back: reading arr.length after
    //    `if (arr !== undefined) { arr.push(9); }` observes the pushed element (3).
    const fixed350: ImperativeProgram = {
      family: "mutation",
      label: "issue-350-opt-array-push",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(arr?: number[]): number {",
        "  if (arr !== undefined) {",
        "    arr.push(9);",
        "  }",
        "  return arr !== undefined ? arr.length : 0;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "opt-int-array", value: [1, 2] }] }],
    };
    const counts350 = createImperativeCounts();
    const res350 = evaluateImperativeProgram(fixed350, { project, workDir, counts: counts350, timeoutSec: 15 });
    assert.equal(res350.ok, true, `expected #350 to pass after Milestone 3a, got ${res350.oracle}: ${res350.detail}`);
    assert.equal(counts350.passed, 1);

    // 2. Milestone 5 (#304): null vs undefined stay distinct via Nullish<T> in `number | null | undefined`.
    const fixed304: ImperativeProgram = {
      family: "nullish-falsy",
      label: "issue-304-null-vs-undefined",
      fnName: "target",
      returnKind: "boolean",
      tsText: [
        "export function target(x: number | null | undefined): boolean {",
        "  return x === null;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "nullish-int", value: undefined }] },
        { args: [{ kind: "nullish-int", value: null }] },
        { args: [{ kind: "nullish-int", value: 0 }] },
      ],
    };
    const counts304 = createImperativeCounts();
    const res304 = evaluateImperativeProgram(fixed304, { project, workDir, counts: counts304, timeoutSec: 15 });
    assert.equal(res304.ok, true, `expected #304 to pass after Milestone 5, got ${res304.oracle}: ${res304.detail}`);
    assert.equal(counts304.soundnessRefuted, 0);
    assert.equal(counts304.passed, 1);

    // 3. Sound function: refutation fails and positive check succeeds.
    const soundProg: ImperativeProgram = {
      family: "aliasing",
      label: "dead-source-move",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(a: number[]): number {",
        "  const b = a;",
        "  b.push(7);",
        "  return b.length;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "int-array", value: [1, 2] }] }],
    };
    const countsSound = createImperativeCounts();
    const resSound = evaluateImperativeProgram(soundProg, { project, workDir, counts: countsSound, timeoutSec: 15 });
    assert.equal(resSound.ok, true, `${resSound.signature}\n${resSound.detail}`);
    assert.equal(countsSound.passed, 1);

    // 3b. Map parameter (`map<string, int>`) and discriminated union constructors (`a`/`b`) parse and verify cleanly.
    const mapProg: ImperativeProgram = {
      family: "mutation",
      label: "map-set-delete-control",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(m: Map<string, number>): number {",
        '  m.set("k", 4);',
        '  if (m.has("del")) { m.delete("del"); }',
        '  const got = m.get("k");',
        '  return got !== undefined && !m.has("del") ? got : -1;',
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "int-map", value: [["del", 1]] }] }],
    };
    const resMap = evaluateImperativeProgram(mapProg, { project, workDir, counts: createImperativeCounts(), timeoutSec: 15 });
    assert.equal(resMap.ok, true, `${resMap.signature}\n${resMap.detail}`);

    const unionProg: ImperativeProgram = {
      family: "union",
      label: "union-if-read-control",
      fnName: "target",
      returnKind: "number",
      tsText: [
        'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
        "export function target(u: Item): number {",
        '  if (u.kind === "a") return u.v + 2;',
        "  return u.items.length;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "union-ab", value: { kind: "a", v: 5 } }] },
        { args: [{ kind: "union-ab", value: { kind: "b", items: [1, 2, 3] } }] },
      ],
    };
    const resUnion = evaluateImperativeProgram(unionProg, { project, workDir, counts: createImperativeCounts(), timeoutSec: 15 });
    assert.equal(resUnion.ok, true, `${resUnion.signature}\n${resUnion.detail}`);

    // 4. Lossless .semantic.json save & replay verifies fixed #304 and reproduces live-alias rejection without reshrinking.
    const fixed304Path = path.join(workDir, "fixed304.semantic.json");
    const saved304 = saveImperativeCase(fixed304Path, fixed304, res304);
    assert.equal(saved304.schema, IMPERATIVE_SCHEMA);
    const replayed304 = replaySavedImperativeCase(fixed304Path, { timeoutSec: 15 });
    assert.equal(replayed304.ok, true);

    const liveAliasProg: ImperativeProgram = {
      family: "aliasing",
      label: "live-alias-mutation",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(a: number[]): number {",
        "  const b = a;",
        "  b.push(7);",
        "  return a.length;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "int-array", value: [1, 2] }] }],
    };
    const resAlias = evaluateImperativeProgram(liveAliasProg, { project, workDir, counts: createImperativeCounts(), timeoutSec: 15 });
    assert.equal(resAlias.ok, false);
    assert.equal(resAlias.oracle, "rejected");
    const aliasPath = path.join(workDir, "live-alias.semantic.json");
    saveImperativeCase(aliasPath, liveAliasProg, resAlias);
    const replayedAlias = replaySavedImperativeCase(aliasPath, { timeoutSec: 15 });
    assert.equal(replayedAlias.ok, false);
    assert.equal(replayedAlias.oracle, "rejected");
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("precondition-drop oracle verifies #349 fixed (x === guard(false, 1) caught by Dafny) and short-circuited guard(false) accepted (#46, #52)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-imp-guard-"));
  try {
    const guardDef = [
      "//@ requires ok",
      "export function guard(ok: boolean, v: number): number {",
      "  return v;",
      "}",
    ].join("\n");

    // 1. #349 is now fixed by Milestone 4: `x === guard(false, 1)` lowers to `x == Some(guard(false, 1))`,
    //    so Dafny catches the violated precondition even when x is Option.None -> oracle passes!
    const fixed349: ImperativeProgram = {
      family: "guard-eval",
      label: "issue-349-eq-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: [
        guardDef,
        "export function target(x?: number): boolean {",
        "  return x === guard(false, 1);",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
    };
    const c1 = createImperativeCounts();
    const r1 = evaluateImperativeProgram(fixed349, { project, workDir, counts: c1, timeoutSec: 15 });
    assert.equal(r1.ok, true, `expected #349 to pass after Milestone 4, got ${r1.oracle}: ${r1.detail}`);
    assert.equal(c1.preconditionDropped, 0);

    // 1b. Negative control on the precondition-drop oracle itself: a synthetic postEmit hook
    //     that drops the guard call in emitted Dafny is caught as `precondition-dropped`.
    const cDrop = createImperativeCounts();
    const rDrop = evaluateImperativeProgram(
      fixed349,
      { project, workDir, counts: cDrop, timeoutSec: 15, stages: ["opt"] },
      { postEmitOptimized: (optDfy) => optDfy.replace(/function target\(x: Option<int>\): bool[\s\S]*$/, "function target(x: Option<int>): bool\n{\n  false\n}\n") },
    );
    assert.equal(rDrop.ok, false);
    assert.equal(rDrop.oracle, "precondition-dropped", `expected precondition-dropped control, got ${rDrop.oracle}: ${rDrop.detail}`);
    assert.equal(cDrop.preconditionDropped, 1);

    // 2. Short-circuited `false && guard(false, 1) > 0`: JS skips guard(false), Dafny agrees!
    const shortCircuitOk: ImperativeProgram = {
      family: "guard-eval",
      label: "and-short-circuit-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: [
        guardDef,
        "export function target(flag: boolean): boolean {",
        "  return flag && guard(false, 1) > 0;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "bool", value: false }] }],
    };
    const c2 = createImperativeCounts();
    const r2 = evaluateImperativeProgram(shortCircuitOk, { project, workDir, counts: c2, timeoutSec: 15 });
    assert.equal(r2.ok, true, `${r2.signature}\n${r2.detail}`);
    assert.equal(c2.passed, 1);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("batched dafny run fast screening detects runtime divergence alongside matching cases (#46)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-imp-batch-"));
  try {
    const goodTs = [
      "export function target(a: number[]): number {",
      "  const b = a;",
      "  b.push(5);",
      "  return b.length;",
      "}",
    ].join("\n");
    const nullishBugTs = [
      "export function target(x: number | null | undefined): boolean {",
      "  return x === null;",
      "}",
    ].join("\n");
    const unionTs = [
      'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
      "export function target(u: Item): number {",
      '  if (u.kind === "a") return u.v + 2;',
      "  return u.items.length;",
      "}",
    ].join("\n");

    const goodCompiled = compileDafnyVariants(goodTs, project);
    const badCompiled = compileDafnyVariants(nullishBugTs, project);
    const unionCompiled = compileDafnyVariants(unionTs, project);
    assert.equal(goodCompiled.ok, true);
    assert.equal(badCompiled.ok, true);
    assert.equal(unionCompiled.ok, true);

    const arg = { kind: "int-array" as const, value: [1, 2] };
    const nullishArg = { kind: "nullish-int" as const, value: undefined };
    const unionArg = { kind: "union-ab" as const, value: { kind: "a" as const, v: 5 } };
    const goodNode = executeImperativeInNode(goodTs, "target", { args: [arg] }, "number");
    const badNode = executeImperativeInNode(nullishBugTs, "target", { args: [nullishArg] }, "boolean");
    const unionNode = executeImperativeInNode(unionTs, "target", { args: [unionArg] }, "number");
    assert.equal(goodNode.kind, "value");
    assert.equal(badNode.kind, "value");
    assert.equal(unionNode.kind, "value");

    const screen = runBatchedDafnyFastScreen(
      [
        {
          id: "dead-source-move",
          dfy: goodCompiled.compiled.optDfy,
          fnName: "target",
          dafnyArgs: [imperativeArgToDafny(arg, goodCompiled.compiled.optDfy)],
          expectedJs: goodNode.value,
        },
        {
          id: "union-if-read",
          dfy: unionCompiled.compiled.optDfy,
          fnName: "target",
          dafnyArgs: [imperativeArgToDafny(unionArg, unionCompiled.compiled.optDfy)],
          expectedJs: unionNode.value,
        },
        {
          id: "issue-304-null-vs-undefined",
          dfy: badCompiled.compiled.optDfy,
          fnName: "target",
          dafnyArgs: [imperativeArgToDafny(nullishArg, badCompiled.compiled.optDfy)],
          expectedJs: badNode.value,
        },
        {
          id: "synthetic-divergence-control",
          dfy: badCompiled.compiled.optDfy,
          fnName: "target",
          dafnyArgs: [imperativeArgToDafny(nullishArg, badCompiled.compiled.optDfy)],
          expectedJs: !(badNode.value as boolean),
        },
      ],
      workDir,
      45,
    );
    assert.equal(screen.error, undefined, screen.error);
    assert.equal(screen.ok, false);
    assert.equal(screen.matched, 3);
    assert.equal(screen.divergences.length, 1);
    assert.equal(screen.divergences[0].id, "synthetic-divergence-control");
    assert.equal(screen.divergences[0].expected, "true");
    assert.equal(screen.divergences[0].actual, "false");
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("imperative campaign exercises --fast-run screening with zero nullish-falsy or aliasing false proofs (#46, #50, #304)", () => {
  const outFast = mkdtempSync(path.join(tmpdir(), "lsc-imp-fastrun-"));
  const outShrink = mkdtempSync(path.join(tmpdir(), "lsc-imp-shrink-"));
  const outAlias = mkdtempSync(path.join(tmpdir(), "lsc-imp-alias-"));
  try {
    // 1. fastRun mode on nullish-falsy: after Milestone 5 (#304), all runs match with 0 soundness-refuted.
    const fastSummary = runImperativeCampaign({
      seed: 1,
      runs: 12,
      families: ["nullish-falsy"],
      out: outFast,
      timeoutSec: 15,
      fastRun: true,
    });
    assert.ok((fastSummary.fastRunScreened ?? 0) >= 1, "expected fastRunScreened >= 1");
    assert.equal(fastSummary.counts.soundnessRefuted, 0, "Milestone 5 must eliminate #304 soundness-refuted");
    assert.equal(fastSummary.counts.dafnyResolve, 0);

    // 2. Standard campaign on loop-shadow exercises stage-locked fc.check shrinking.
    const shrinkSummary = runImperativeCampaign({
      seed: 1,
      runs: 6,
      families: ["loop-shadow"],
      out: outShrink,
      timeoutSec: 15,
    });
    assert.equal(shrinkSummary.counts.soundnessRefuted, 0);
    assert.equal(shrinkSummary.counts.dafnyResolve, 0);

    // 3. Aliasing family: live-alias-mutation is explicitly rejected (zero soundness-refuted).
    const aliasSummary = runImperativeCampaign({
      seed: 1,
      runs: 12,
      families: ["aliasing"],
      out: outAlias,
      timeoutSec: 15,
      fastRun: true,
    });
    assert.equal(aliasSummary.counts.soundnessRefuted, 0, "Milestone 3b must eliminate live-alias soundness-refuted");
    assert.ok(aliasSummary.classes.some(c => c.oracle === "rejected" && c.label === "live-alias-mutation"));
  } finally {
    rmSync(outFast, { recursive: true, force: true });
    rmSync(outShrink, { recursive: true, force: true });
    rmSync(outAlias, { recursive: true, force: true });
  }
});
