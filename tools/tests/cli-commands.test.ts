import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs";
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

test("a failed registered law points to its own source in single-file and workspace checks", () => {
  const files = {
    "source.ts": source,
    "LemmaScript-files.txt": "source.ts\n",
    "lemmascript.json": JSON.stringify({ "proof-files": { "source.ts": ["laws.dfy"] } }),
    "laws.dfy": "lemma ItChangesTheValue(x: int)\n  ensures identity(x) != x\n{}\n",
  };
  for (const args of [["check", "source.ts"], ["check"]]) {
    const result = runCli(files, args);
    assert.equal(result.status, 1);
    assert.match(result.stdout + result.stderr, /laws\.dfy\(2,\d+\): Related location: this is the postcondition/);
  }
});

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

for (const intermediate of ["gen", "gen-check", "check"] as const) {
  test(`lsc ${intermediate} between an edit and regen preserves the merge base`, () => {
    const dir = realpathSync(mkdtempSync(join(tmpdir(), "lsc-commands-base-")));
    try {
      const tsPath = join(dir, "t.ts");
      const dfyPath = join(dir, "t.dfy");
      const basePath = join(dir, "t.dfy.base");
      const run = (args: string[]) => spawnSync(process.execPath, [cli, ...args], {
        cwd: dir, env: { ...process.env, LSC_RUN_LOG: "false" }, encoding: "utf8", timeout: 30_000,
      });

      const v1 = [
        "export function inc(n: number): number {",
        "  //@ requires n >= 0",
        "  //@ ensures \\result > n",
        "  return n + 1;",
        "}",
        "",
      ].join("\n");
      writeFileSync(tsPath, v1);

      const init = run(["regen", "--backend=dafny", "--no-verify", "t.ts"]);
      assert.equal(init.status, 0, init.stdout + init.stderr);
      writeFileSync(dfyPath, readFileSync(dfyPath, "utf8") + "\nlemma UserProof() {}\n");

      // Repeated gen-check on an unchanged file does not create a base file.
      const cleanCheck = run(["gen-check", "--backend=dafny", "t.ts"]);
      assert.equal(cleanCheck.status, 0, cleanCheck.stdout + cleanCheck.stderr);
      assert.equal(existsSync(basePath), false);

      // Edit source and run the intermediate command before regen.
      writeFileSync(tsPath, v1.replace("return n + 1;", "return n + 2;"));
      const mid = run([intermediate, "--backend=dafny", "t.ts"]);
      assert.equal(mid.status, intermediate === "gen" ? 0 : 1, mid.stdout + mid.stderr);
      assert.equal(existsSync(basePath), true);

      // regen three-way merges using the saved base and removes it on success.
      const merged = run(["regen", "--backend=dafny", "--no-verify", "t.ts"]);
      assert.equal(merged.status, 0, merged.stdout + merged.stderr);
      assert.equal(existsSync(basePath), false);
      const proof = readFileSync(dfyPath, "utf8");
      assert.match(proof, /\(n \+ 2\)/);
      assert.match(proof, /lemma UserProof\(\) \{\}/);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
}

test("lsc gen-check removes a leftover base file once the proof matches again", () => {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), "lsc-commands-revert-")));
  try {
    const tsPath = join(dir, "t.ts");
    const basePath = join(dir, "t.dfy.base");
    const run = (args: string[]) => spawnSync(process.execPath, [cli, ...args], {
      cwd: dir, env: { ...process.env, LSC_RUN_LOG: "false" }, encoding: "utf8", timeout: 30_000,
    });

    const v1 = "export function inc(n: number): number { return n + 1; }\n";
    writeFileSync(tsPath, v1);
    assert.equal(run(["regen", "--backend=dafny", "--no-verify", "t.ts"]).status, 0);

    writeFileSync(tsPath, v1.replace("n + 1", "n + 2"));
    assert.equal(run(["gen-check", "--backend=dafny", "t.ts"]).status, 1);
    assert.equal(existsSync(basePath), true);

    writeFileSync(tsPath, v1);
    const reverted = run(["gen-check", "--backend=dafny", "t.ts"]);
    assert.equal(reverted.status, 0, reverted.stdout + reverted.stderr);
    assert.equal(existsSync(basePath), false);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
