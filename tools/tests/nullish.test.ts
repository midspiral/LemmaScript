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
