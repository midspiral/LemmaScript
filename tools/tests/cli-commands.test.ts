import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readdirSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const cli = fileURLToPath(new URL("../dist/lsc.js", import.meta.url));
const source = "export function identity(value: number): number { return value; }\n";

function runCli(files: Record<string, string>, args: string[]) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), "lsc-commands-")));
  try {
    for (const [name, contents] of Object.entries(files)) writeFileSync(join(dir, name), contents);
    const result = spawnSync(process.execPath, [cli, ...args], {
      cwd: dir, env: { ...process.env, LSC_RUN_LOG: "false" }, encoding: "utf8", timeout: 30_000,
    });
    assert.ifError(result.error);
    return { ...result, files: readdirSync(dir).sort() };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const cases: { name: string; files: Record<string, string>; args: string[] }[] = [
  { name: "without a file", files: {}, args: [] },
  { name: "with a missing file", files: {}, args: ["missing.ts"] },
  { name: "with an ordinary file", files: { "source.ts": source }, args: ["source.ts"] },
  {
    name: "with a Lean-only file under the default Dafny backend",
    files: { "source.ts": "//@ backend lean\n" + source }, args: ["source.ts"],
  },
  {
    name: "with a Dafny-only file under the Lean backend",
    files: { "source.ts": "//@ backend dafny\n" + source }, args: ["--backend=lean", "source.ts"],
  },
  {
    name: "before loading invalid project configuration",
    files: { "source.ts": source, "lemmascript.json": "{" }, args: ["source.ts"],
  },
];

for (const { name, files, args } of cases) {
  test(`rejects an unknown command ${name}`, () => {
    const result = runCli(files, ["not-a-command", ...args]);
    assert.equal(result.status, 1, result.stdout + result.stderr);
    assert.equal(result.stdout, "");
    assert.equal(result.stderr, "Unknown command: not-a-command\n");
    assert.deepEqual(result.files, Object.keys(files).sort(), "unknown commands must not write artifacts");
  });
}

for (const cmd of ["gen", "gen-check", "check", "regen"]) {
  test(`${cmd} still skips a file for the other backend`, () => {
    const result = runCli({ "source.ts": "//@ backend lean\n" + source }, [cmd, "source.ts"]);
    assert.equal(result.status, 0, result.stderr);
    assert.match(result.stdout, /^Skipped: source\.ts /);
    assert.deepEqual(result.files, ["source.ts"]);
  });
}
