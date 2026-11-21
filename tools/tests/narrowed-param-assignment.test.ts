import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { inOptionalBlock, inUnionArm } from "../fixtures/narrowed-param-assignment.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function typed() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/narrowed-param-assignment.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-narrowed-param-"));
  try {
    const proof = join(dir, "narrowed-param.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("JavaScript: the narrowed block updates the parameter", () => {
  assert.deepEqual([inOptionalBlock(1, undefined), inOptionalBlock(1, 2)], [1, 3]);
  assert.deepEqual([inUnionArm(1, { kind: "circle", r: 2 }), inUnionArm(1, { kind: "square", s: 2 })], [3, 1]);
});

test("Dafny copies a parameter assigned only inside a match arm", () => {
  const { typesFile, defFile } = transformModuleDafny(typed());
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  for (const name of ["inOptionalBlock", "inUnionArm"]) {
    const body = output.slice(output.indexOf(`method ${name}`));
    assert.match(body, /^method [^\n]*\n\{\n\s*var p := p;/, output);
  }
  const ok = verify(output);
  assert.equal(ok.status, 0, output + ok.output);
});
