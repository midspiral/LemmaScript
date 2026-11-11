import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import ts from "typescript";

// Build first: these tests exercise the CLI and guard forwarder shipped on npm.
const cli = fileURLToPath(new URL("../dist/lsc.js", import.meta.url));
const proxy = fileURLToPath(new URL("../dist/guard-command.js", import.meta.url));
const source = `export function positive(x: number): number {
  //@ requires x > 0
  return x;
}
`;

async function fixture(run: (dir: string) => void | Promise<void>) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), "lsc-guard-")));
  try {
    writeFileSync(join(dir, "package.json"), '{"type":"module"}');
    await run(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function runCli(dir: string, args: string[], env: NodeJS.ProcessEnv = {}, entry = cli) {
  const cleanEnv = { ...process.env };
  delete cleanEnv.LEMMASCRIPT;
  const result = spawnSync(process.execPath, [entry, ...args], {
    cwd: dir, env: { ...cleanEnv, ...env }, encoding: "utf8", timeout: 30_000,
  });
  assert.ifError(result.error);
  return result;
}

for (const directive of ["", "//@ backend lean\n", "//@ backend dafny\n"]) {
  test(`guard generates and enforces preconditions (${directive.trim() || "no backend directive"})`, () => fixture(async dir => {
    const name = "source with spaces";
    writeFileSync(join(dir, `${name}.ts`), directive + source);
    const result = runCli(dir, ["guard", `${name}.ts`]);
    assert.equal(result.status, 0, result.stdout + result.stderr);
    assert.match(result.stdout, /1 functions guarded/);
    assert.doesNotMatch(result.stdout, /Skipped/);

    for (const base of [name, `${name}.guarded`]) {
      const text = readFileSync(join(dir, `${base}.ts`), "utf8");
      const { outputText } = ts.transpileModule(text, {
        compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ES2022 },
      });
      writeFileSync(join(dir, `${base}.js`), outputText);
    }
    const guarded = await import(pathToFileURL(join(dir, `${name}.guarded.js`)).href);
    assert.equal(guarded.positive(1), 1);
    assert.equal(guarded.can.positive(1), true);
    assert.equal(guarded.can.positive(0), false);
    assert.throws(() => guarded.positive(0), guarded.PreconditionError);
  }));
}

test("guard without a file reports the satellite's usage and fails", () => fixture(dir => {
  const result = runCli(dir, ["guard"]);
  assert.equal(result.status, 1);
  assert.match(result.stderr, /usage: lemmascript-guard <file\.ts>/);
}));

test("guard reports missing files and fails", () => fixture(dir => {
  const result = runCli(dir, ["guard", "missing.ts"]);
  assert.equal(result.status, 1);
  assert.match(result.stderr, /file not found: .*missing\.ts/);
  assert.equal(existsSync(join(dir, "missing.guarded.ts")), false);
}));

test("guard propagates incomplete runtime contract failures", () => fixture(dir => {
  writeFileSync(join(dir, "source.ts"), source.replace("x > 0", "ghostPredicate(x)"));
  const result = runCli(dir, ["guard", "source.ts"]);
  assert.equal(result.status, 1, result.stdout + result.stderr);
  assert.match(result.stderr, /GUARD INCOMPLETE/);
  assert.match(readFileSync(join(dir, "source.guarded.ts"), "utf8"), /UNENFORCED/);
}));

// Isolate the forwarder so dependency absence and nonstandard child exit codes
// can be exercised without modifying this checkout's installed packages.
function isolatedProxy(dir: string, child?: string, setup = "") {
  const dist = join(dir, "tools", "dist");
  mkdirSync(dist, { recursive: true });
  copyFileSync(proxy, join(dist, "guard-command.js"));
  const entry = join(dir, "invoke.mjs");
  writeFileSync(entry, `import { runGuard } from "./tools/dist/guard-command.js";\n${setup}\nrunGuard(process.argv.slice(2));\n`);
  const dependency = join(dir, "node_modules", "lemmascript-guard");
  mkdirSync(join(dependency, "dist"), { recursive: true });
  // Block resolution through ancestor directories when simulating absence.
  writeFileSync(join(dependency, "package.json"), JSON.stringify(child === undefined ? { exports: {} } : { type: "module" }));
  if (child !== undefined) writeFileSync(join(dependency, "dist", "guard.js"), child);
  return entry;
}

test("guard forwards arguments, working directory, compiler location, and exit status", () => fixture(dir => {
  const entry = isolatedProxy(dir, `
console.log(JSON.stringify({ args: process.argv.slice(2), cwd: process.cwd(), compiler: process.env.LEMMASCRIPT }));
process.exit(7);
`);
  const args = ["source with spaces.ts", "--satellite-flag=value"];
  const result = runCli(dir, args, {}, entry);
  assert.equal(result.status, 7);
  const report = JSON.parse(result.stdout);
  assert.deepEqual(report.args, args);
  assert.equal(report.cwd, dir);
  assert.equal(realpathSync(report.compiler), dir);
  assert.equal(result.stderr, "", "child failures should not gain a duplicate stack trace");
}));

test("guard preserves an explicit LEMMASCRIPT override", () => fixture(dir => {
  const entry = isolatedProxy(dir, "console.log(process.env.LEMMASCRIPT);");
  const result = runCli(dir, ["source.ts"], { LEMMASCRIPT: "../compiler override" }, entry);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout.trim(), "../compiler override");
}));

test("guard fails with installation guidance when the optional dependency is unavailable", () => fixture(dir => {
  const result = runCli(dir, ["source.ts"], {}, isolatedProxy(dir));
  assert.equal(result.status, 1);
  assert.match(result.stderr, /needs lemmascript-guard >= 0\.1\.0/);
  assert.match(result.stderr, /--include=optional/);
}));

test("guard explains its Node requirement before trying to load the optional dependency", () => fixture(dir => {
  const entry = isolatedProxy(dir, undefined, 'Object.defineProperty(process.versions, "node", { value: "20.0.0" });');
  const result = runCli(dir, ["source.ts"], {}, entry);
  assert.equal(result.status, 1);
  assert.match(result.stderr, /requires Node\.js 22 or newer/);
}));
