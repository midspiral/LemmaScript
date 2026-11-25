import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

test("Milestone 5 (#304): Nullish<T> rejects false null/undefined conflation and verifies strict, loose, narrowing, coercion, ??/?., and mutation patterns in Dafny", () => {
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m5-nullish-dafny-"));
  try {
    // 1. Original #304 false proof MUST fail verification.
    const badFile = path.join(workDir, "bad304.ts");
    writeFileSync(badFile, [
      "//@ backend dafny",
      "export function label(x: string | null | undefined): string {",
      "  //@ verify",
      '  //@ ensures x === null ==> \\result === "unset"',
      '  return x === undefined ? "unset" : "set";',
      "}",
    ].join("\n"));
    const badRes = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", badFile], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    });
    assert.notEqual(badRes.status, 0, `false #304 ensures must be rejected:\n${badRes.stdout}\n${badRes.stderr}`);

    // 2. Comprehensive valid Nullish<T> suite MUST verify cleanly in Dafny.
    const goodFile = path.join(workDir, "good304.ts");
    writeFileSync(goodFile, [
      "//@ backend dafny",
      "export interface Box { v: number; inner?: number | null }",
      "",
      "export function labelGood(x: string | null | undefined): string {",
      "  //@ verify",
      '  //@ ensures x === undefined ==> \\result === "unset"',
      '  //@ ensures x === null ==> \\result === "set"',
      '  return x === undefined ? "unset" : "set";',
      "}",
      "",
      "export function kindTernary(x: string | null | undefined): number {",
      "  //@ verify",
      "  //@ ensures x === null ==> \\result === 1",
      "  //@ ensures x === undefined ==> \\result === 2",
      "  //@ ensures x !== null && x !== undefined ==> \\result === 3",
      "  return x === null ? 1 : x === undefined ? 2 : 3;",
      "}",
      "",
      "export function kindEarlyReturn(x: number | null | undefined): number {",
      "  //@ verify",
      "  //@ ensures x === null ==> \\result === 1",
      "  //@ ensures x === undefined ==> \\result === 2",
      "  //@ ensures x != null ==> \\result === x + 10",
      "  if (x === null) return 1;",
      "  if (x === undefined) return 2;",
      "  return x + 10;",
      "}",
      "",
      "export function looseChecks(x: number | null | undefined): number {",
      "  //@ verify",
      "  //@ ensures x == null ==> \\result === 0",
      "  //@ ensures x != undefined ==> \\result === x + 1",
      "  if (x == null) return 0;",
      "  return x + 1;",
      "}",
      "",
      "export function orChainEarlyReturn(x: number | null | undefined): number {",
      "  //@ verify",
      "  //@ ensures x == null ==> \\result === -1",
      "  //@ ensures x != null ==> \\result === x * 2",
      "  if (x === null || x === undefined) return -1;",
      "  return x * 2;",
      "}",
      "",
      "export function andChainGuard(x: number | null | undefined): boolean {",
      "  //@ verify",
      "  return x !== null && x !== undefined && x > 0;",
      "}",
      "",
      "export function truthinessGuard(x: number | null | undefined): number {",
      "  //@ verify",
      "  //@ ensures x == null ==> \\result === -1",
      "  if (x) return x;",
      "  if (x === null) return -1;",
      "  if (x === undefined) return -1;",
      "  return 0;",
      "}",
      "",
      "export function coalesceAndOptChain(x: number | null | undefined, b: Box | null | undefined): number {",
      "  //@ verify",
      "  const a = x ?? 5;",
      "  const c = b?.v ?? 0;",
      "  return a + c;",
      "}",
      "",
      "export function coalesceToUndefined(x: number | null | undefined): number | undefined {",
      "  //@ verify",
      "  return x ?? undefined;",
      "}",
      "",
      "export function narrowToOptional(x: number | null | undefined): number | undefined {",
      "  //@ verify",
      "  if (x === null) return undefined;",
      "  return x;",
      "}",
      "",
      "export function widenPairwise(a: number | null, b: number | undefined, flag: boolean): number | null | undefined {",
      "  //@ verify",
      "  //@ ensures flag && a === null ==> \\result === null",
      "  //@ ensures !flag && b === undefined ==> \\result === undefined",
      "  if (flag) return a;",
      "  return b;",
      "}",
      "",
      "export function oppositeSentinelCheck(a: number | undefined, b: number | null): boolean {",
      "  //@ verify",
      "  //@ ensures \\result === false",
      "  return a === null || b === undefined;",
      "}",
      "",
      "export function definiteAssignAndMutate(xs: number[] | null | undefined): number {",
      "  //@ verify",
      "  let cur: number[] | null | undefined = xs;",
      "  if (cur == null) { cur = [1]; }",
      "  cur.push(2);",
      "  return cur.length;",
      "}",
      "",
      "export function nullishWhile(x: number | null | undefined): number {",
      "  //@ verify",
      "  let cur: number | null | undefined = x;",
      "  let steps = 0;",
      "  while (cur !== null && cur !== undefined && steps < 1) {",
      "    //@ invariant 0 <= steps && steps <= 1",
      "    //@ decreases 1 - steps",
      "    cur = cur > 0 ? null : undefined;",
      "    steps = steps + 1;",
      "  }",
      "  return steps;",
      "}",
    ].join("\n"));
    const goodRes = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", goodFile], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 120_000,
    });
    assert.equal(goodRes.status, 0, `valid Nullish<T> suite failed:\n${goodRes.stdout}\n${goodRes.stderr}`);

    // 3. Single-sentinel `T | undefined` and `T | null` stay on `Option<T>` (no `Nullish` emitted).
    const project = makeProject();
    const optSf = project.createSourceFile(
      "single_sentinel.ts",
      [
        "export function optUndef(x?: number): number { return x !== undefined ? x : 0; }",
        "export function optNull(x: number | null): number { return x !== null ? x : 0; }",
      ].join("\n"),
      { overwrite: true },
    );
    const optDafny = emitDafnyFile(transformModuleDafny(narrowModule(resolveModule(extractModule(optSf)))).defFile);
    assert.doesNotMatch(optDafny, /datatype Nullish/, `single-sentinel optionals must stay Option<T>:\n${optDafny}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("Milestone 5 (#304): Nullish<T> emits clean Lean with on-demand LemmaScript.Nullish and typechecks with grind", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m5-nullish-lean-"));
  try {
    const sf = project.createSourceFile(
      "nullish_lean.ts",
      [
        "//@ pure",
        "export function kind(x: number | null | undefined): number {",
        "  return x === null ? 1 : x === undefined ? 2 : x + 10;",
        "}",
        "//@ pure",
        "export function kindEarly(x: number | null | undefined): number {",
        "  if (x === null) return 1;",
        "  if (x === undefined) return 2;",
        "  return x + 10;",
        "}",
        "//@ pure",
        "export function loose(x: number | null | undefined): number {",
        "  return x == null ? 0 : x + 1;",
        "}",
        "//@ pure",
        "export function andGuard(x: number | null | undefined): boolean {",
        "  return x !== null && x !== undefined && x > 0;",
        "}",
        "//@ pure",
        "export function coalesce(x: number | null | undefined): number {",
        "  return x ?? 42;",
        "}",
      ].join("\n"),
      { overwrite: true },
    );
    resetLeanModule();
    const leanMod = transformModuleLean(narrowModule(resolveModule(extractModule(sf))));
    const leanTypes = leanMod.typesFile ? emitLeanFile(leanMod.typesFile) : "";
    assert.match(leanTypes, /import LemmaScript\.Nullish/, `expected on-demand LemmaScript.Nullish import:\n${leanTypes}`);
    const pureMatch = leanTypes.match(/namespace Pure[\s\S]*?end Pure/);
    assert.ok(pureMatch, `expected Pure namespace in Lean output:\n${leanTypes}`);

    // Verify directly with the `lean` CLI when installed.
    const leanProbe = spawnSync("lean", ["--version"], { encoding: "utf8", timeout: 10_000 });
    if (leanProbe.status === 0) {
      mkdirSync(path.join(workDir, "LemmaScript"), { recursive: true });
      writeFileSync(
        path.join(workDir, "LemmaScript", "Nullish.lean"),
        readFileSync(new URL("../../LemmaScript/Nullish.lean", import.meta.url)),
      );
      const env = { ...process.env, LEAN_PATH: workDir };
      const helper = spawnSync(
        "lean",
        ["--root", workDir, "-o", path.join(workDir, "LemmaScript", "Nullish.olean"), path.join(workDir, "LemmaScript", "Nullish.lean")],
        { env, encoding: "utf8", timeout: 60_000 },
      );
      assert.equal(helper.status, 0, `Nullish.lean failed to compile:\n${helper.stdout}\n${helper.stderr}`);

      const leanFile = path.join(workDir, "NullishCheck.lean");
      writeFileSync(
        leanFile,
        `import LemmaScript.Nullish\n\n${pureMatch[0]}\n\n` +
        `theorem t_null : Pure.kind .null = 1 := rfl\n` +
        `theorem t_undef : Pure.kind .undefined = 2 := rfl\n` +
        `theorem t_val : Pure.kind (.value 5) = 15 := rfl\n` +
        `theorem t_early : Pure.kindEarly (.value 5) = 15 := rfl\n` +
        `theorem t_loose_null : Pure.loose .null = 0 := rfl\n` +
        `theorem t_loose_undef : Pure.loose .undefined = 0 := rfl\n` +
        `theorem t_loose_val : Pure.loose (.value 7) = 8 := rfl\n` +
        `theorem t_coal_null : Pure.coalesce .null = 42 := rfl\n` +
        `theorem t_coal_undef : Pure.coalesce .undefined = 42 := rfl\n` +
        `theorem t_coal_val : Pure.coalesce (.value 9) = 9 := rfl\n`,
      );
      const res = spawnSync("lean", ["--root", workDir, leanFile], { env, encoding: "utf8", timeout: 60_000 });
      assert.equal(res.status, 0, `Lean check failed:\n${pureMatch[0]}\n${res.stdout}\n${res.stderr}`);
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("Milestone 5 (#304): review regressions — alias check on Nullish, two-sided/loose comparisons, paren/alias flattening, filterSome, Lean Inhabited + dependent implies, field paths, switch, mutations, ||, record/union literals", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m5-review-"));
  try {
    // Finding 1 (CRITICAL): alias-check must reject live-alias mutations through Nullish<T> & widening coercions.
    const aliasBypassCases = [
      [
        "export function aliasBypass1(a: number[] | null | undefined): boolean {",
        "  //@ verify",
        "  const b: number[] | null | undefined = a;",
        "  if (a != null && b != null) {",
        "    const before = a.length;",
        "    b.push(99);",
        "    return a.length === before;",
        "  }",
        "  return true;",
        "}",
      ].join("\n"),
      [
        "export function aliasBypass2(a: number[]): boolean {",
        "  //@ verify",
        "  const b: number[] | null | undefined = a;",
        "  const before = a.length;",
        "  if (b != null) b.push(99);",
        "  return a.length === before;",
        "}",
      ].join("\n"),
    ];
    for (let i = 0; i < aliasBypassCases.length; i++) {
      const f = path.join(workDir, `alias_bypass_${i}.ts`);
      writeFileSync(f, aliasBypassCases[i]!);
      const res = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", f], {
        cwd: repoRoot,
        encoding: "utf8",
        env: { ...process.env, LSC_RUN_LOG: "false" },
        timeout: 60_000,
      });
      assert.notEqual(res.status, 0, `aliasBypass${i + 1} must be rejected`);
      assert.match(res.stdout + res.stderr, /Live-alias mutation/i, `expected live-alias rejection for aliasBypass${i + 1}:\n${res.stdout}\n${res.stderr}`);
    }

    // Findings 2, 3, 4 (CRITICAL): false postconditions MUST FAIL verification!
    const falseProofCases: Array<{ name: string; code: string }> = [
      {
        name: "bad_opp_sentinels.ts",
        code: [
          "export function cmpOppSentinels(a: number | null, b: number | undefined): boolean {",
          "  //@ verify",
          "  //@ ensures a === null && b === undefined ==> \\result === true",
          "  return a === b;",
          "}",
        ].join("\n"),
      },
      {
        name: "bad_loose_nullish_pair.ts",
        code: [
          "export function cmpLooseNullishPair(a: number | null | undefined, b: number | null | undefined): boolean {",
          "  //@ verify",
          "  //@ ensures a === null && b === undefined ==> \\result === false",
          "  return a == b;",
          "}",
        ].join("\n"),
      },
      {
        name: "bad_opt_loose_neq.ts",
        code: [
          "export function cmpOptLooseNeq(a: number | undefined): boolean {",
          "  //@ verify",
          "  //@ ensures a === undefined ==> \\result === false",
          "  return a != 5;",
          "}",
        ].join("\n"),
      },
      {
        name: "bad_paren_nullish.ts",
        code: [
          "export function parenNullish(x: (number | null) | undefined): boolean {",
          "  //@ verify",
          "  //@ ensures \\result === false",
          "  return x === null;",
          "}",
        ].join("\n"),
      },
      {
        name: "bad_filter_null_with_undef.ts",
        code: [
          "export function filterNullWithUndef(): number {",
          "  //@ verify",
          "  //@ ensures \\result === 1",
          "  const xs: (number | null)[] = [null, 1];",
          "  return xs.filter(x => x !== undefined).length;",
          "}",
        ].join("\n"),
      },
    ];
    for (const c of falseProofCases) {
      const f = path.join(workDir, c.name);
      writeFileSync(f, c.code);
      const res = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", f], {
        cwd: repoRoot,
        encoding: "utf8",
        env: { ...process.env, LSC_RUN_LOG: "false" },
        timeout: 60_000,
      });
      assert.notEqual(res.status, 0, `${c.name} false proof must fail Dafny verification:\n${res.stdout}\n${res.stderr}`);
    }

    // Findings 2–4 & 7–14: comprehensive positive Dafny suite MUST verify with 0 errors!
    const goodReviewFile = path.join(workDir, "good_review_regressions.ts");
    writeFileSync(goodReviewFile, [
      "//@ backend dafny",
      'export type Phase = "idle" | "busy";',
      "export type MaybeNum = number | null;",
      'export type U = { kind: "a"; x: number; opt?: number | null } | { kind: "b"; y: string };',
      "export interface Box { v: number; inner?: number | null; optNull: number | null }",
      "export interface InnerBox { inner: number | null }",
      "",
      "export function cmpOppSentinelsOk(a: number | null, b: number | undefined): boolean {",
      "  //@ verify",
      "  //@ ensures a === null && b === undefined ==> \\result === false",
      "  return a === b;",
      "}",
      "export function cmpLooseNullishPairOk(a: number | null | undefined, b: number | null | undefined): boolean {",
      "  //@ verify",
      "  //@ ensures a === null && b === undefined ==> \\result === true",
      "  return a == b;",
      "}",
      "export function cmpOptLooseNeqOk(a: number | undefined): boolean {",
      "  //@ verify",
      "  //@ ensures a === undefined ==> \\result === true",
      "  return a != 5;",
      "}",
      "export function cmpNullishOptOk(a: number | null | undefined, b: number | undefined): boolean {",
      "  //@ verify",
      "  //@ ensures a === undefined && b === undefined ==> \\result === true",
      "  //@ ensures a === null && b === undefined ==> \\result === false",
      "  return a === b;",
      "}",
      "export function parenAndAliasNullish(x: (number | null) | undefined, y: MaybeNum | undefined): number {",
      "  //@ verify",
      "  //@ ensures x === null ==> \\result === 1",
      "  if (x === null) return 1;",
      "  if (y === null) return 2;",
      "  return 0;",
      "}",
      "export function filterNullKeepAll(): number {",
      "  //@ verify",
      "  const xs: (number | null)[] = [null, 1];",
      "  return xs.filter(x => x !== undefined).length;",
      "}",
      "export function filterNullDropNull(): number {",
      "  //@ verify",
      "  //@ ensures \\result === 1",
      "  const xs: (number | null)[] = [null, 1];",
      "  return xs.filter(x => x !== null).length;",
      "}",
      "export function fFieldTwoStep(b: Box): number {",
      "  //@ verify",
      "  if (b.inner !== null && b.inner !== undefined) return b.inner + 1;",
      "  return 0;",
      "}",
      "export function fFieldSeq(b: Box): number {",
      "  //@ verify",
      "  if (b.inner === null) return 0;",
      "  if (b.inner === undefined) return 0;",
      "  return b.inner + 1;",
      "}",
      "export function partialTernary(x: number | null | undefined, flag: boolean): number | undefined {",
      "  //@ verify",
      "  if (x === null) return undefined;",
      "  return flag ? x : undefined;",
      "}",
      "export function partialCoalesceExpr(x: number | null | undefined, flag: boolean): number {",
      "  //@ verify",
      "  if (x === null) return 0;",
      "  return (flag ? x : undefined) ?? 42;",
      "}",
      "export function optChainToNullish(b: InnerBox | undefined): number | null | undefined {",
      "  //@ verify",
      "  return b?.inner;",
      "}",
      "export function tagMatchNullish(v: number[] | number): number | null | undefined {",
      "  //@ verify",
      "  return Array.isArray(v) ? (v.length > 0 ? v[0] : null) : undefined;",
      "}",
      "export function switchNullishPhase(p: Phase | null | undefined): number {",
      "  //@ verify",
      "  if (p == null) return 0;",
      "  switch (p) {",
      '    case "idle": return 1;',
      '    case "busy": return 2;',
      "  }",
      "}",
      "export function switchNullishUnion(u: U | null | undefined): number {",
      "  //@ verify",
      "  if (u == null) return 0;",
      "  switch (u.kind) {",
      '    case "a": return u.x;',
      '    case "b": return u.y.length;',
      "  }",
      "}",
      "export function mutateNullishIndex(xs: number[] | null | undefined): number {",
      "  //@ verify",
      "  if (xs == null || xs.length === 0) return 0;",
      "  xs[0] = 99;",
      "  return xs[0];",
      "}",
      "export function mutateNullishPop(xs: number[] | null | undefined): number {",
      "  //@ verify",
      "  if (xs == null || xs.length === 0) return 0;",
      "  const last = xs.pop();",
      "  return xs.length + (last ?? 0);",
      "}",
      "export function fieldAssignNullish(b: Box, x: number): Box {",
      "  //@ verify",
      "  b.inner = x;",
      "  return b;",
      "}",
      "export function fieldAssignNullishClear(b: Box): Box {",
      "  //@ verify",
      "  b.inner = null;",
      "  return b;",
      "}",
      "export function fieldAssignOptNullClear(b: Box): Box {",
      "  //@ verify",
      "  b.optNull = null;",
      "  return b;",
      "}",
      "export function mutateFieldOnNullishRecord(b: Box | null | undefined): number {",
      "  //@ verify",
      "  if (b == null) return 0;",
      "  b.v = 10;",
      "  return b.v;",
      "}",
      "export function optOrNull(x: number | null): number | null {",
      "  //@ verify",
      "  return x || null;",
      "}",
      "export function orNullishPair(a: number | null | undefined, b: number | null | undefined): number | null | undefined {",
      "  //@ verify",
      "  return a || b;",
      "}",
      "export function takeNullishBox(b: InnerBox | null | undefined): number {",
      "  //@ verify",
      "  return b != null ? (b.inner ?? 0) : 0;",
      "}",
      "export function callWithRecordLit(): number {",
      "  //@ verify",
      "  return takeNullishBox({ inner: 7 });",
      "}",
      "export function unionOmittedNullish(): U {",
      "  //@ verify",
      '  return { kind: "a", x: 1 };',
      "}",
      "export function afterSomeMatch(x: number | undefined): boolean {",
      "  //@ verify",
      "  //@ ensures \\result === false",
      "  if (x === undefined) return false;",
      "  return x === null;",
      "}",
    ].join("\n"));
    const goodRes = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", goodReviewFile], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 120_000,
    });
    assert.equal(goodRes.status, 0, `review regression Dafny suite failed:\n${goodRes.stdout}\n${goodRes.stderr}`);

    // Findings 5 & 6: Lean `Inhabited (Nullish α)` on structures + dependent `∀ (_hN : ...)` for `implies` with `checkedUnwrap`!
    const leanSf = project.createSourceFile(
      "lean_review_regressions.ts",
      [
        "export interface Box { v: number; inner?: number | null }",
        "export function impNullishSpec(x: number | null | undefined): number {",
        "  //@ verify",
        "  //@ ensures x != null ==> \\result === x + 10",
        "  if (x === null) return 1;",
        "  if (x === undefined) return 2;",
        "  return x + 10;",
        "}",
      ].join("\n"),
      { overwrite: true },
    );
    resetLeanModule();
    const leanMod = transformModuleLean(narrowModule(resolveModule(extractModule(leanSf))));
    const leanTypes = leanMod.typesFile ? emitLeanFile(leanMod.typesFile) : "";
    const leanDef = emitLeanFile(leanMod.defFile);
    assert.match(leanDef, /∀ \(_h\d+ : /, `expected dependent ∀ (_hN : ...) for Lean implies with checkedUnwrap:\n${leanDef}`);

    const leanProbe = spawnSync("lean", ["--version"], { encoding: "utf8", timeout: 10_000 });
    if (leanProbe.status === 0) {
      mkdirSync(path.join(workDir, "LemmaScript"), { recursive: true });
      writeFileSync(
        path.join(workDir, "LemmaScript", "Nullish.lean"),
        readFileSync(new URL("../../LemmaScript/Nullish.lean", import.meta.url)),
      );
      const env = { ...process.env, LEAN_PATH: workDir };
      const helper = spawnSync(
        "lean",
        ["--root", workDir, "-o", path.join(workDir, "LemmaScript", "Nullish.olean"), path.join(workDir, "LemmaScript", "Nullish.lean")],
        { env, encoding: "utf8", timeout: 60_000 },
      );
      assert.equal(helper.status, 0, `Nullish.lean failed:\n${helper.stdout}\n${helper.stderr}`);
      // Verify `structure Box ... deriving Inhabited` AND dependent `∀ (_h0 : (x).isValue = true), ...` typecheck in Lean!
      const structBlock = leanTypes.replace(/^import LemmaScript\n/m, "");
      const leanCheckFile = path.join(workDir, "LeanReviewCheck.lean");
      writeFileSync(
        leanCheckFile,
        `import LemmaScript.Nullish\n\n` +
        `${structBlock}\n` +
        `theorem dep_imp_check (x : Nullish Int) : ∀ (_h0 : (x).isValue = true), Pure.impNullishSpec x = ((x).get (by grind)) + 10 := by\n` +
        `  intro h; cases x <;> simp [Pure.impNullishSpec, Nullish.isValue, Nullish.isNull, Nullish.isUndefined, Nullish.get] at h ⊢\n`,
      );
      const leanRes = spawnSync("lean", ["--root", workDir, leanCheckFile], { env, encoding: "utf8", timeout: 60_000 });
      assert.equal(leanRes.status, 0, `Lean review check failed:\n${leanRes.stdout}\n${leanRes.stderr}`);
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
