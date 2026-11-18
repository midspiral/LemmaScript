import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { ModuleResolutionKind, Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { isBaseMethod } from "../../examples/httpMethods.ts";
import { distinctMethodCount, emptyMethodCount, hasFromEither, isExtendedKnown, isKnown } from "../../examples/setSpread.ts";

const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const loader = createRequire(import.meta.url).resolve("tsx");

function withDirectory(fn: (dir: string) => void) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-set-spread-"));
  try { fn(dir); }
  finally { rmSync(dir, { recursive: true, force: true }); }
}

function runCli(dir: string, command: "check" | "regen", file: string) {
  const result = spawnSync(process.execPath, ["--import", loader, cli, command,
    "--backend=dafny", "--time-limit=10", file], {
    cwd: dir, env: { ...process.env, LSC_RUN_LOG: "false" }, encoding: "utf8", timeout: 60_000,
  });
  assert.ifError(result.error);
  return { status: result.status, output: result.stdout + result.stderr };
}

test("the shared membership table has the specified JavaScript behavior", () => {
  for (const method of ["get", "post", "put", "head", "delete", "options", "patch", "", "GET"]) {
    assert.equal(isBaseMethod(method), ["get", "post"].includes(method));
    assert.equal(isKnown(method), ["get", "post", "put"].includes(method));
    assert.equal(isExtendedKnown(method), ["get", "post", "put", "head", "delete", "options"].includes(method));
    for (const left of [[], ["get"], ["post", "post"]]) {
      for (const right of [[], ["post", "get"], ["put", "put"]]) {
        assert.equal(hasFromEither(left, right, method), left.includes(method) || method === "put" || right.includes(method));
      }
    }
  }
  assert.equal(distinctMethodCount(), 6);
  assert.equal(emptyMethodCount(), 0);
});

test("the two-file example verifies, and changing the imported table invalidates its proof", () => {
  withDirectory(dir => {
    for (const file of ["setSpread.ts", "setSpread.dfy", "httpMethods.ts"]) {
      const dest = join(dir, file);
      mkdirSync(dirname(dest), { recursive: true });
      copyFileSync(fileURLToPath(new URL(`../../examples/${file}`, import.meta.url)), dest);
    }
    const base = runCli(dir, "check", "httpMethods.ts");
    assert.equal(base.status, 0, base.output);
    const before = runCli(dir, "check", "setSpread.ts");
    assert.equal(before.status, 0, before.output);
    const dependency = join(dir, "httpMethods.ts");
    const original = readFileSync(dependency, "utf8");
    const changed = original.replace('["get", "post"]', '["get"]');
    assert.notEqual(changed, original);
    writeFileSync(dependency, changed);
    const after = runCli(dir, "regen", "setSpread.ts");
    assert.equal(after.status, 1, after.output);
    assert.match(after.output, /a postcondition could not be proved/);
    assert.match(after.output, /Dafny program verifier finished with \d+ verified, 1 error/);
  });
});

test("renamed and re-exported arrays keep their declaration identity and respect local shadowing", () => {
  withDirectory(dir => {
    writeFileSync(join(dir, "first.ts"), 'export const methods = ["get", "post"];');
    writeFileSync(join(dir, "second.ts"), 'export const methods = ["patch"];');
    writeFileSync(join(dir, "third.ts"), 'export const methods = ["head"];');
    writeFileSync(join(dir, "barrel.ts"), 'export { methods } from "./second.js";');
    writeFileSync(join(dir, "source.ts"), `
import { methods as first } from "./first.js";
import { methods as same } from "./first.js";
import { methods as second } from "./barrel.js";
import { methods as literalOnly } from "./third.js";
const known = new Set<string>([...first, ...second]);
export function member(method: string): boolean {
  //@ verify
  //@ ensures \\result <==> (method === "get" || method === "post" || method === "patch")
  return known.has(method);
}
export function shadow(first: string[], method: string): boolean {
  //@ verify
  //@ ensures \\result <==> (method === "get" || method === "post")
  return new Set([...same]).has(method);
}
export function local(first: string[], method: string): boolean {
  //@ verify
  //@ ensures \\result <==> exists(i: nat, i < first.length && first[i] === method)
  return new Set([...first]).has(method);
}
export function plainLiteral(): boolean {
  //@ verify
  //@ ensures \\result
  return new Set([literalOnly[0]]).has("head");
}
`);
    const result = runCli(dir, "check", "source.ts");
    assert.equal(result.status, 0, result.output);
  });
});

for (const [dependency, error] of [
  ['export let methods = ["get"];', /non-constant 'methods'/],
  ['let method = "get"; export const methods = [method];', /non-constant 'method'/],
  ['function load(): string[] { return ["get"]; } export const methods = load();', /Unsupported imported constant array initializer: load\(\)/],
  ['export const methods = [..."get"];', /only support array spreads/],
  ['export const methods = [] as const;', /needs an explicit element type/],
  ['export const methods: string[] = [...other]; const other: string[] = [...methods];', /Cyclic imported constant array/],
] as const) {
  test(`imported data fails explicitly: ${dependency}`, () => {
    const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
      strict: true, target: ScriptTarget.ESNext, moduleResolution: ModuleResolutionKind.NodeJs,
      lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
    } });
    project.createSourceFile("/methods.ts", dependency);
    const source = project.createSourceFile("/main.ts", `
import { methods } from "./methods";
export function member(method: string): boolean {
  return new Set([...methods, "put"]).has(method);
}`);
    assert.throws(() => extractModule(source), error);
  });
}
