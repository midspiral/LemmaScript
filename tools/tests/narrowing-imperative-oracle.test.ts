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

test("negated-postcondition refutation oracle catches #304 false proof, verifies #350 fixed, and rejects live-alias mutation (#46, #49, #50)", () => {
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

    // 2. Known false proof #304 (deferred to Milestone 5): null vs undefined conflation in `number | null | undefined`.
    const bug304: ImperativeProgram = {
      family: "nullish-falsy",
      label: "issue-304-null-vs-undefined",
      fnName: "target",
      returnKind: "boolean",
      tsText: [
        "export function target(x: number | null | undefined): boolean {",
        "  return x === null;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "nullish-int", value: undefined }] }],
    };
    const counts304 = createImperativeCounts();
    const res304 = evaluateImperativeProgram(bug304, { project, workDir, counts: counts304, timeoutSec: 15 });
    assert.equal(res304.ok, false);
    assert.equal(res304.oracle, "soundness-refuted", `expected soundness-refuted for #304, got ${res304.oracle}: ${res304.detail}`);
    assert.equal(counts304.soundnessRefuted, 1);

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

    // 4. Lossless .semantic.json save & replay reproduces #304 soundness-refuted without reshrinking.
    const casePath = path.join(workDir, "bug304.semantic.json");
    const saved = saveImperativeCase(casePath, bug304, res304);
    assert.equal(saved.schema, IMPERATIVE_SCHEMA);
    const replayed = replaySavedImperativeCase(casePath, { timeoutSec: 15 });
    assert.equal(replayed.ok, false);
    assert.equal(replayed.oracle, "soundness-refuted");
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("precondition-drop oracle detects skipped guard(false) (#349) and accepts short-circuited guard(false) (#46)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-imp-guard-"));
  try {
    const guardDef = [
      "//@ requires ok",
      "export function guard(ok: boolean, v: number): number {",
      "  return v;",
      "}",
    ].join("\n");

    // 1. #349 shape: `x === guard(false, 1)` evaluates RHS in JS even when x is undefined.
    const bug349: ImperativeProgram = {
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
    const r1 = evaluateImperativeProgram(bug349, { project, workDir, counts: c1, timeoutSec: 15 });
    assert.equal(r1.ok, false);
    assert.equal(r1.oracle, "precondition-dropped", `expected precondition-dropped for #349, got ${r1.oracle}: ${r1.detail}`);
    assert.equal(c1.preconditionDropped, 1);

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
      ],
      workDir,
      45,
    );
    assert.equal(screen.error, undefined, screen.error);
    assert.equal(screen.ok, false);
    assert.equal(screen.matched, 2);
    assert.equal(screen.divergences.length, 1);
    assert.equal(screen.divergences[0].id, "issue-304-null-vs-undefined");
    assert.equal(screen.divergences[0].expected, "false");
    assert.equal(screen.divergences[0].actual, "true");
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("imperative campaign exercises --fast-run screening and stage-locked shrinking with pre/opt attribution (#46, #50)", () => {
  const outFast = mkdtempSync(path.join(tmpdir(), "lsc-imp-fastrun-"));
  const outShrink = mkdtempSync(path.join(tmpdir(), "lsc-imp-shrink-"));
  const outAlias = mkdtempSync(path.join(tmpdir(), "lsc-imp-alias-"));
  try {
    // 1. fastRun mode on nullish-falsy (#304): screens batch and confirms
    //    soundness-refuted divergence via `dafny verify` on both pre and opt stages.
    const fastSummary = runImperativeCampaign({
      seed: 1,
      runs: 12,
      families: ["nullish-falsy"],
      out: outFast,
      timeoutSec: 15,
      fastRun: true,
    });
    assert.ok((fastSummary.fastRunScreened ?? 0) >= 1, "expected fastRunScreened >= 1");
    assert.ok(fastSummary.classes.some(c => c.oracle === "soundness-refuted" && c.stage === "both"));

    // 2. Standard campaign shrinks #304 soundness-refuted via stage-locked fc.check.
    const shrinkSummary = runImperativeCampaign({
      seed: 1,
      runs: 10,
      families: ["nullish-falsy"],
      out: outShrink,
      timeoutSec: 15,
    });
    const cls = shrinkSummary.classes.find(c => c.oracle === "soundness-refuted");
    assert.ok(cls, "expected shrunk #304 soundness-refuted class");
    assert.equal(cls.stage, "both");

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
