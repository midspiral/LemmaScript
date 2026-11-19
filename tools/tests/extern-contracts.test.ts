import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ModuleResolutionKind } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function resolve(source: string, dependencies: Record<string, string> = {}) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    moduleResolution: ModuleResolutionKind.NodeJs,
  } });
  for (const [name, contents] of Object.entries(dependencies)) project.createSourceFile(`/${name}`, contents);
  return resolveModule(extractModule(project.createSourceFile("/main.ts", source)));
}

for (const kind of ["requires", "ensures"] as const) {
  for (const imported of [false, true]) {
    test(`malformed ${kind} on ${imported ? "an imported" : "an explicit"} extern aborts resolution`, () => {
      const declaration = `
//@ ${kind} n >
export function read(n: number): number { return n; }`;
      const source = imported
        ? 'import { read } from "./library";\nexport function caller(): number { return read(1); }'
        : `//@ extern${declaration}`;
      assert.throws(() => resolve(source, imported ? { "library.ts": declaration } : {}),
        new RegExp(`extern read: //@ ${kind} n >: Unexpected end of expression`));
    });
  }
}

test("an extern precondition cannot silently lose an invalid result reference", () => {
  assert.throws(() => resolve(String.raw`
//@ extern
//@ requires \result > 0
declare function read(n: number): number;
`), /extern read: \/\/@ requires \\result > 0: \\result is only valid in ensures/);
});

test("an extern postcondition cannot silently lose a call to an impure extern", () => {
  assert.throws(() => resolve(`
//@ extern
//@ impure
declare function sample(): number;
//@ extern
//@ ensures sample() > 0
declare function read(n: number): number;
`), /extern read: \/\/@ ensures sample\(\) > 0: impure extern sample cannot be called from a specification/);
});

for (const impure of [false, true]) {
  test(`${impure ? "impure" : "pure"} externs preserve every valid clause, including proof helpers`, () => {
    const mod = resolve(`
//@ extern
${impure ? "//@ impure" : ""}
//@ requires n >= 0
//@ requires allowed(n)
//@ ensures \\result >= n
//@ ensures good(\\result)
declare function read(n: number): number;
`);
    const { typesFile, defFile } = transformModuleDafny(narrowModule(mod));
    const dafny = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
    assert.match(dafny, /requires \(n >= 0\)/);
    assert.match(dafny, /requires allowed\(n\)/);
    const result = impure ? "res" : "read(n)";
    assert.ok(dafny.includes(`ensures (${result} >= n)`));
    assert.ok(dafny.includes(`ensures good(${result})`));
  });
}

const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const loader = createRequire(import.meta.url).resolve("tsx");

test("failed extern resolution creates no artifacts and preserves existing proofs", () => {
  const dir = mkdtempSync(join(tmpdir(), "lsc-extern-contracts-"));
  try {
    writeFileSync(join(dir, "source.ts"), `
//@ extern
//@ requires n >
declare function read(n: number): number;
export function caller(): number { return read(1); }
`);
    const gen = join(dir, "source.dfy.gen");
    const proof = join(dir, "source.dfy");
    for (const existing of [false, true]) {
      if (existing) {
        writeFileSync(gen, "previous generated content\n");
        writeFileSync(proof, "previous proof additions\n");
      }
      const result = spawnSync(process.execPath, ["--import", loader, cli, "gen", "--backend=dafny", "source.ts"], {
        cwd: dir, encoding: "utf8", timeout: 30_000,
      });
      assert.ifError(result.error);
      assert.notEqual(result.status, 0);
      assert.match(result.stderr, /extern read: \/\/@ requires n >: Unexpected end of expression/);
      if (existing) {
        assert.equal(readFileSync(gen, "utf8"), "previous generated content\n");
        assert.equal(readFileSync(proof, "utf8"), "previous proof additions\n");
      } else {
        assert.equal(existsSync(gen), false);
        assert.equal(existsSync(proof), false);
      }
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
