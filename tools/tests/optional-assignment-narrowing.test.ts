import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { peepholeModule } from "../src/peephole.ts";
import * as runtime from "../fixtures/optional-assignment-narrowing.ts";

const fixture = readFileSync(new URL("../fixtures/optional-assignment-narrowing.ts", import.meta.url), "utf8");

function typed(text: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("optional-assignment.ts", text);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return narrowModule(resolveModule(extractModule(source)));
}

function generate(text: string): string {
  const { typesFile, defFile } = transformModuleDafny(typed(text));
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-optional-assignment-"));
  try {
    const path = join(dir, "test.dfy");
    writeFileSync(path, generate(text));
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=10", path],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("optional assignment narrowing agrees with JavaScript, including later absent writes", () => {
  for (const flag of [false, true]) {
    for (const fn of [runtime.coalescedNull, runtime.coalescedUndefined, runtime.conditionalReset]) {
      assert.equal(fn(flag), flag ? 7 : 5);
    }
    assert.equal(runtime.optionalFallback(flag), flag ? 5 : undefined);
  }
  assert.equal(runtime.repeatedWrites(), 8);
  assert.equal(runtime.compoundWrites(), 10);
  assert.equal(runtime.nestedReads(), 8);
  assert.equal(runtime.guardedCell(undefined), 7);
  for (const value of [-1, 0, 5]) assert.equal(runtime.guardedCell({ value }), value < 0 ? 7 : value);
  const result = verify(fixture);
  assert.equal(result.status, 0, result.output);
});

test("assignment narrowing does not prove a false postcondition", () => {
  const result = verify(fixture.replace("flag ==> \\result === 7", "flag ==> \\result === 5"));
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /postcondition could not be proved/);
  assert.doesNotMatch(result.output, /resolution\/type errors|timed out/);
});

test("a non-null assertion still requires the optional to be present", () => {
  const result = verify("export function readAbsent(p: number | undefined): number { return p!; }");
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /destructor.*value/);
  assert.doesNotMatch(result.output, /resolution\/type errors|timed out/);
});

test("Lean proves optional assignment narrowing and rejects an absent payload", {
  skip: !existsSync(new URL("../../.lake/build/lib/lean/LemmaScript/Option.olean", import.meta.url)),
}, () => {
  const dir = mkdtempSync(join(tmpdir(), "lsc-optional-assignment-lean-"));
  try {
    for (const [text, valid] of [
      [fixture, true],
      ["export function readAbsent(p: number | undefined): number { return p!; }", false],
    ] as const) {
      const mod = typed(text);
      const { typesFile, defFile } = transformModuleLean(mod);
      resetLeanModule();
      const output = emitLeanFile({ ...defFile, imports: ["LemmaScript"],
        decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
      const proofs = mod.functions.map(f =>
        `prove_correct ${f.name} by\n  velvet_vcgen [${f.name}] with finish${f.name === "guardedCell" ? " [Pure.guardedCell]" : ""}\n`).join("\n");
      const path = join(dir, "Assignments.lean");
      writeFileSync(path, output + "\n" + proofs);
      const result = spawnSync("lake", ["env", "lean", path], {
        cwd: fileURLToPath(new URL("../../", import.meta.url)), encoding: "utf8", timeout: 60_000,
      });
      assert.ifError(result.error);
      const log = result.stdout + result.stderr;
      assert.equal(result.status === 0, valid, log + output);
      if (!valid) assert.match(log, /unsolved goals|`finish` failed/);
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
