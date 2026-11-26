import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  compileDafnyVariants,
  createCounts,
  evaluateModule,
  renderModule,
  runCampaign,
  type FnSpec,
} from "../fuzz/narrowing-fuzz.ts";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");
const fuzzCli = path.join(repoRoot, "tools/fuzz/narrowing-fuzz.ts");

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

test("optimized fuzzer output matches compiled CLI output and visibly applies peephole (#12)", () => {
  // `flag ? b : false` lowers to `if flag then b else false` pre-peephole,
  // which peepholeModule simplifies to `(flag && b)` on midspiral/main.
  const tsText = [
    "export function f0(flag: boolean, b: boolean): boolean {",
    "  return flag ? b : false;",
    "}",
    "export function f1(x: number, o?: number): number {",
    "  if (o !== undefined) return x + o;",
    "  return x;",
    "}",
  ].join("\n");
  const project = makeProject();
  const compiled = compileDafnyVariants(tsText, project, { sourceName: "sample.ts" });
  assert.equal(compiled.ok, true);
  assert.equal(compiled.compiled.optChanged, true, "expected peephole to visibly change emitted Dafny");
  assert.notEqual(compiled.compiled.preDfy, compiled.compiled.optDfy);

  // Compare against the compiled production CLI (`tools/dist/lsc.js gen --backend=dafny`).
  const dir = mkdtempSync(path.join(tmpdir(), "lsc-fuzz12-cli-"));
  try {
    const tsFile = path.join(dir, "sample.ts");
    writeFileSync(tsFile, tsText);
    const res = spawnSync(process.execPath, [compiledCli, "gen", "--backend=dafny", tsFile], {
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 30_000,
    });
    assert.ifError(res.error);
    assert.equal(res.status, 0, res.stdout + res.stderr);
    const cliDfy = readFileSync(path.join(dir, "sample.dfy.gen"), "utf8");
    assert.equal(compiled.compiled.optDfy, cliDfy);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});

test("malformed optimized-output control fails as dafny-opt while pre-optimization passes (#12)", () => {
  const tsText = renderModule([
    { targets: [0], truthy: [false, false, false, false, false, false], position: "ifValue", use: 0, ensures: false },
  ]);
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-fuzz12-optctrl-"));
  try {
    const project = makeProject();
    const counts = createCounts();
    const outcome = evaluateModule(tsText, { project, workDir, counts }, {
      postEmitOptimized: (optDfy) => optDfy + "\nfunction BrokenOpt(): int { unresolved_ident_xyz }\n",
    });
    assert.equal(outcome.ok, false);
    assert.equal(outcome.oracle, "dafny-opt");
    assert.equal(outcome.stage, "opt");
    assert.match(outcome.signature, /^dafny-opt:/);
    assert.ok(outcome.preDfy && !outcome.preDfy.includes("BrokenOpt"));
    assert.ok(outcome.optDfy && outcome.optDfy.includes("BrokenOpt"));
    assert.equal(counts.pre.attempted, 1);
    assert.equal(counts.pre.completed, 1);
    assert.equal(counts.opt.attempted, 1);
    assert.equal(counts.opt.completed, 1);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("shrinking preserves dafny-opt stage, saves both variants, and supports saved-source replay (#12)", () => {
  const outDir = mkdtempSync(path.join(tmpdir(), "lsc-fuzz12-shrink-"));
  try {
    const summary = runCampaign({
      seed: 1,
      runs: 15,
      classes: 1,
      positions: ["ifThen", "ifValue"],
      minutes: 2,
      out: outDir,
      hooks: {
        postEmitOptimized: (optDfy, _preDfy, tsText) =>
          tsText.includes("if (") ? optDfy + "\nfunction BrokenOpt(): int { unresolved_ident_xyz }\n" : optDfy,
      },
    });
    assert.equal(summary.failureClasses, 1);
    assert.equal(summary.saved.length, 1);
    const saved = summary.saved[0];
    assert.equal(saved.oracle, "dafny-opt");
    assert.equal(saved.stage, "opt");
    assert.ok(existsSync(path.join(outDir, "1.ts")));
    assert.ok(existsSync(path.join(outDir, "1.pre.dfy")));
    assert.ok(existsSync(path.join(outDir, "1.opt.dfy")));
    assert.ok(existsSync(path.join(outDir, "1.meta.json")));
    const preText = readFileSync(path.join(outDir, "1.pre.dfy"), "utf8");
    const optText = readFileSync(path.join(outDir, "1.opt.dfy"), "utf8");
    assert.ok(!preText.includes("BrokenOpt"));
    assert.ok(optText.includes("BrokenOpt"));

    // Replay saved source via CLI `--file` (without broken hook, it should now pass both stages).
    const replay = spawnSync(
      process.execPath,
      ["--import", "tsx", fuzzCli, "--file", path.join(outDir, "1.ts")],
      { cwd: path.join(repoRoot, "tools"), encoding: "utf8", timeout: 60_000 },
    );
    assert.ifError(replay.error);
    assert.equal(replay.status, 0, replay.stdout + replay.stderr);
    assert.match(replay.stdout, /dafny resolve accepts both pre-optimization and optimized Dafny/);
  } finally {
    rmSync(outDir, { recursive: true, force: true });
  }
});

test("timeouts are reported as timeout failures and not counted as completed checks (#12)", () => {
  const tsText = renderModule([
    { targets: [0], truthy: [false, false, false, false, false, false], position: "ifValue", use: 0, ensures: false },
  ]);
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-fuzz12-timeout-"));
  try {
    const project = makeProject();
    const counts = createCounts();
    const outcome = evaluateModule(tsText, { project, workDir, counts }, {
      resolveDafny: (_dfy, stage) =>
        stage === "opt"
          ? { status: "timeout", detail: "dafny resolve (opt) timed out" }
          : { status: "ok", detail: null },
    });
    assert.equal(outcome.ok, false);
    assert.equal(outcome.oracle, "timeout");
    assert.equal(outcome.stage, "opt");
    assert.equal(counts.pre.attempted, 1);
    assert.equal(counts.pre.completed, 1);
    assert.equal(counts.opt.attempted, 1);
    assert.equal(counts.opt.completed, 0);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
