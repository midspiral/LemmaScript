import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { chmodSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { delimiter, join } from "node:path";
import { dafnyCheckDiff, dafnyRegen } from "../src/dafny-commands.ts";
import { RunLog, readRecords } from "../src/run-log.ts";

class ExitSignal extends Error {
  constructor(readonly code: number | undefined) { super(`process.exit(${code})`); }
}
const generation = (n: number): string => `method M() {\n  var value := ${n};\n}\n`;
const addition = "\nlemma AddedProof() {}\n";
type Fixture = { gen: string; proof: string; base: string; dir: string };

function fixture(run: (f: Fixture) => void): void {
  const dir = mkdtempSync(join(tmpdir(), "lsc-regen-review-"));
  const bin = join(dir, "bin");
  const originalExit = process.exit;
  const originalPath = process.env.PATH;
  try {
    mkdirSync(bin);
    const verifier = join(bin, "dafny");
    writeFileSync(verifier, "#!/bin/sh\nexit 1\n");
    chmodSync(verifier, 0o755);
    process.env.PATH = `${bin}${delimiter}${originalPath ?? ""}`;
    process.exit = ((code?: number) => { throw new ExitSignal(code); }) as typeof process.exit;
    const f = { gen: join(dir, "x.dfy.gen"), proof: join(dir, "x.dfy"), base: join(dir, "x.dfy.base"), dir };
    writeFileSync(f.gen, generation(0));
    writeFileSync(f.proof, generation(0) + addition);
    run(f);
  } finally {
    process.exit = originalExit;
    if (originalPath === undefined) delete process.env.PATH; else process.env.PATH = originalPath;
    rmSync(dir, { recursive: true, force: true });
  }
}
function fails(run: () => void): void {
  assert.throws(run, (e) => e instanceof ExitSignal && e.code === 1);
}
const posixOnly = { skip: process.platform === "win32" };

// Intercept selected merge calls, forwarding everything else (including the
// additions-only check) to real Git. Record calls to catch accidental retries.
function installGit(f: Fixture, script: string): void {
  const bin = join(f.dir, "bin");
  const realPath = process.env.PATH!.split(delimiter).filter(p => p !== bin).join(delimiter);
  const git = join(bin, "git");
  writeFileSync(git, `#!${process.execPath}
const { appendFileSync, writeFileSync } = require("node:fs");
const { spawnSync } = require("node:child_process");
const args = process.argv.slice(2);
const proof = ${JSON.stringify(f.proof)};
appendFileSync(${JSON.stringify(join(f.dir, "git-calls.jsonl"))}, JSON.stringify(args) + "\\n");
${script}
const result = spawnSync("git", args, {
  stdio: "inherit", env: { ...process.env, PATH: ${JSON.stringify(realPath)} },
});
if (result.error) throw result.error;
if (result.signal) process.kill(process.pid, result.signal);
process.exit(result.status ?? 1);
`);
  chmodSync(git, 0o755);
}

function mergeCalls(f: Fixture): string[][] {
  return readFileSync(join(f.dir, "git-calls.jsonl"), "utf8").trim().split("\n")
    .map(line => JSON.parse(line) as string[]).filter(args => args[0] === "merge-file");
}

function runLog(f: Fixture): RunLog {
  const sourcePath = join(f.dir, "x.ts");
  writeFileSync(sourcePath, "");
  return new RunLog({ logDir: f.dir, cmd: "regen", sourcePath, lscVersion: "test" });
}

const oldGit = `
if (args[0] === "merge-file" && args.includes("--diff-algorithm=minimal")) {
  console.error("error: unknown option 'diff-algorithm=minimal'");
  process.exit(129);
}
`;

test("a generated change after a large proof block preserves every other byte", posixOnly, t => fixture(f => {
  const help = spawnSync("git", ["merge-file", "-h"], { encoding: "utf8", env: { ...process.env, LC_ALL: "C" } });
  assert.ifError(help.error);
  if (!(help.stdout + help.stderr).includes("--diff-algorithm")) {
    t.skip("the large-proof fix requires Git 2.44 or later; older Git uses the tested fallback");
    return;
  }
  const base = readFileSync(new URL("../fixtures/regen-large-proof/base.txt", import.meta.url), "utf8");
  const proof = readFileSync(new URL("../fixtures/regen-large-proof/proof.txt", import.meta.url), "utf8");
  const old = "below(candidate.node.path, kept.node.path)";
  const next = "below(kept.node.path, candidate.node.path)";
  assert.equal(base.split(old).length, 2);
  assert.equal(proof.split(old).length, 2);
  writeFileSync(f.gen, base);
  writeFileSync(f.proof, proof);
  assert.equal(dafnyCheckDiff(f.gen, f.proof), true);
  dafnyRegen(f.gen, f.proof, f.base, base.replace(old, next), f.dir, undefined, undefined, true);
  assert.equal(readFileSync(f.proof, "utf8"), proof.replace(old, next));
  assert.equal(existsSync(f.base), false);
  assert.equal(existsSync(f.proof + ".merged"), false);
}));

test("older Git retries once without the option and warns about false conflicts", posixOnly, t => fixture(f => {
  installGit(f, oldGit);
  const warnings: string[] = [];
  t.mock.method(console, "warn", (message: string) => warnings.push(message));
  dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true);
  assert.equal(readFileSync(f.proof, "utf8"), generation(1) + addition);
  assert.equal(existsSync(f.base), false);
  assert.equal(existsSync(f.proof + ".merged"), false);
  const calls = mergeCalls(f);
  assert.equal(calls.length, 2);
  assert.ok(calls[0].includes("--diff-algorithm=minimal"));
  assert.ok(!calls[1].includes("--diff-algorithm=minimal"));
  assert.equal(warnings.length, 1);
  assert.match(warnings[0], /Git 2\.44.*false conflicts/);
}));

test("a genuine conflict on older Git still saves the merge and restores the proof", posixOnly, t => fixture(f => {
  installGit(f, oldGit.replace("unknown option '", "unknown option `"));
  t.mock.method(console, "warn", () => {});
  const original = generation(99) + addition;
  writeFileSync(f.proof, original);
  const log = runLog(f);
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true, log));
  assert.equal(readFileSync(f.proof, "utf8"), original);
  assert.equal(readFileSync(f.base, "utf8"), generation(0));
  assert.match(readFileSync(f.proof + ".merged", "utf8"), /<<<<<<</);
  assert.equal(mergeCalls(f).length, 2);
  assert.deepEqual(readRecords(f.dir).map(r => r.stage), ["conflict"]);
}));

for (const failure of [
  { name: "fatal error", status: 128, detail: "fatal: cannot merge" },
  { name: "unrelated usage error", status: 129, detail: "error: unknown option 'unrelated'" },
  { name: "missing input", status: 255, detail: "error: Could not stat missing.dfy" },
  { name: "signal", signal: "SIGTERM", detail: "merge interrupted" },
  { name: "error after falling back", status: 255, detail: "error: Could not stat missing.dfy", legacy: true },
]) {
  test(`Git ${failure.name} restores recovery state without recording a conflict`, posixOnly, t => fixture(f => {
    installGit(f, (failure.legacy ? oldGit : "") + `
if (args[0] === "merge-file") {
  writeFileSync(proof, "partial merge output\\n");
  console.error(${JSON.stringify(failure.detail)});
  ${failure.signal ? `process.kill(process.pid, ${JSON.stringify(failure.signal)});` : `process.exit(${failure.status});`}
}
`);
    const errors: string[] = [];
    const warnings: string[] = [];
    t.mock.method(console, "error", (message: string) => errors.push(message));
    t.mock.method(console, "warn", (message: string) => warnings.push(message));
    // An existing recovery anchor must win over the last generated file.
    writeFileSync(f.base, generation(0));
    writeFileSync(f.gen, generation(9));
    const priorMerge = "previous conflict for manual inspection\n";
    if (failure.legacy) writeFileSync(f.proof + ".merged", priorMerge);
    const log = runLog(f);
    fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true, log));
    assert.equal(readFileSync(f.proof, "utf8"), generation(0) + addition);
    assert.equal(readFileSync(f.base, "utf8"), generation(0));
    assert.equal(readFileSync(f.gen, "utf8"), generation(1));
    if (failure.legacy) assert.equal(readFileSync(f.proof + ".merged", "utf8"), priorMerge);
    else assert.equal(existsSync(f.proof + ".merged"), false);
    assert.equal(mergeCalls(f).length, failure.legacy ? 2 : 1);
    assert.equal(warnings.length, failure.legacy ? 1 : 0);
    assert.equal(errors.length, 1);
    assert.match(errors[0], /^ERROR: could not run `git merge-file`/);
    assert.ok(errors[0].includes(failure.detail));
    assert.ok(errors[0].includes(failure.signal ?? `git exited ${failure.status}`));
    assert.deepEqual(readRecords(f.dir), []);
  }));
}

test("a missing Git executable is an error and leaves the proof and anchor intact", posixOnly, t => fixture(f => {
  process.env.PATH = join(f.dir, "bin");
  const errors: string[] = [];
  t.mock.method(console, "error", (message: string) => errors.push(message));
  const log = runLog(f);
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true, log));
  assert.equal(readFileSync(f.proof, "utf8"), generation(0) + addition);
  assert.equal(readFileSync(f.base, "utf8"), generation(0));
  assert.equal(existsSync(f.proof + ".merged"), false);
  assert.match(errors.join("\n"), /^ERROR:.*git not found on PATH/);
  assert.deepEqual(readRecords(f.dir), []);
}));

test("Git's capped conflict count still saves the conflicted result", posixOnly, () => fixture(f => {
  const conflicted = "<<<<<<< proof\nours\n=======\ntheirs\n>>>>>>> gen\n";
  installGit(f, `
if (args[0] === "merge-file") {
  writeFileSync(proof, ${JSON.stringify(conflicted)});
  process.exit(127);
}
`);
  const log = runLog(f);
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true, log));
  assert.equal(readFileSync(f.proof, "utf8"), generation(0) + addition);
  assert.equal(readFileSync(f.base, "utf8"), generation(0));
  assert.equal(readFileSync(f.proof + ".merged", "utf8"), conflicted);
  assert.equal(mergeCalls(f).length, 1);
  assert.deepEqual(readRecords(f.dir).map(r => r.stage), ["conflict"]);
}));

test("failed verification anchors the generation already merged into the proof", posixOnly, () => fixture(f => {
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir));
  assert.equal(readFileSync(f.base, "utf8"), generation(1));
  assert.equal(readFileSync(f.proof, "utf8"), generation(1) + addition);
}));

test("repeated failure and a subsequent source change preserve each declaration once", posixOnly, () => fixture(f => {
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir));
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir));
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(2), f.dir));
  assert.equal(readFileSync(f.base, "utf8"), generation(2));
  assert.equal(readFileSync(f.proof, "utf8"), generation(2) + addition);
  dafnyRegen(f.gen, f.proof, f.base, generation(2), f.dir, undefined, undefined, true);
  assert.equal(existsSync(f.base), false);
  assert.equal(readFileSync(f.proof, "utf8"), generation(2) + addition);
}));

test("conflicts preserve the original proof and pre-merge anchor", posixOnly, () => fixture(f => {
  const original = generation(99) + addition;
  writeFileSync(f.proof, original);
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir));
  assert.equal(readFileSync(f.proof, "utf8"), original);
  assert.equal(readFileSync(f.base, "utf8"), generation(0));
  assert.match(readFileSync(f.proof + ".merged", "utf8"), /<<<<<<</);
}));

test("additions-only failure does not advance an unaccepted anchor", posixOnly, () => fixture(f => {
  writeFileSync(f.base, generation(0));
  writeFileSync(f.proof, generation(99));
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(0), f.dir));
  assert.equal(readFileSync(f.base, "utf8"), generation(0));
  assert.equal(readFileSync(f.proof, "utf8"), generation(99));
}));

test("a failed first verification can be followed by a clean generation", posixOnly, () => fixture(f => {
  rmSync(f.proof);
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir));
  assert.equal(readFileSync(f.proof, "utf8"), generation(1));
  dafnyRegen(f.gen, f.proof, f.base, generation(2), f.dir, undefined, undefined, true);
  assert.equal(readFileSync(f.proof, "utf8"), generation(2));
  assert.equal(existsSync(f.base), false);
}));
