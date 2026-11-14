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

// A git that runs `body` first, then defers to the real git.
function fakeGit(f: Fixture, body: string): void {
  const real = spawnSync("sh", ["-c", "command -v git"], { encoding: "utf8" }).stdout.trim();
  const git = join(f.dir, "bin", "git");
  writeFileSync(git, `#!/bin/sh\n${body}\nexec "${real}" "$@"\n`);
  chmodSync(git, 0o755);
}

function runLog(f: Fixture): RunLog {
  const sourcePath = join(f.dir, "x.ts");
  writeFileSync(sourcePath, "");
  return new RunLog({ logDir: f.dir, cmd: "regen", sourcePath, lscVersion: "test" });
}

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

test("Git before 2.44 merges with the default algorithm and warns", posixOnly, t => fixture(f => {
  fakeGit(f, `case "$*" in *--diff-algorithm*) echo "error: unknown option" >&2; exit 129;; esac`);
  const warnings: string[] = [];
  t.mock.method(console, "warn", (message: string) => warnings.push(message));
  dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true);
  assert.equal(readFileSync(f.proof, "utf8"), generation(1) + addition);
  assert.equal(existsSync(f.proof + ".merged"), false);
  assert.match(warnings.join("\n"), /Git 2\.44/);
}));

test("a Git failure that is not a conflict leaves the proof unchanged and records no conflict", posixOnly, t => fixture(f => {
  fakeGit(f, `if [ "$1" = merge-file ]; then echo "error: Could not stat x" >&2; exit 255; fi`);
  const errors: string[] = [];
  t.mock.method(console, "error", (message: string) => errors.push(message));
  const log = runLog(f);
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true, log));
  assert.equal(readFileSync(f.proof, "utf8"), generation(0) + addition);
  assert.equal(readFileSync(f.base, "utf8"), generation(0));
  assert.equal(existsSync(f.proof + ".merged"), false);
  assert.match(errors.join("\n"), /^ERROR: could not run `git merge-file`.*\(git exited 255\).*error: Could not stat x/);
  assert.deepEqual(readRecords(f.dir), []);
}));

test("a missing Git is an error, not a conflict", posixOnly, t => fixture(f => {
  process.env.PATH = join(f.dir, "bin");
  const errors: string[] = [];
  t.mock.method(console, "error", (message: string) => errors.push(message));
  fails(() => dafnyRegen(f.gen, f.proof, f.base, generation(1), f.dir, undefined, undefined, true));
  assert.equal(readFileSync(f.proof, "utf8"), generation(0) + addition);
  assert.equal(existsSync(f.proof + ".merged"), false);
  assert.match(errors.join("\n"), /^ERROR:.*git not found on PATH/);
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
