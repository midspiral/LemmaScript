import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import * as runtime from "../fixtures/narrowing-binder-capture.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

// Regression tests for binder capture: a match on a field path inside a
// narrowed scope must not reuse the binder of the enclosing narrowing.

function generate(): string {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/narrowing-binder-capture.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [],
    "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source))));
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-narrowing-binder-capture-"));
  try {
    const proof = join(dir, "narrowing-binder-capture.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("JavaScript gives a counterexample to each false ensures", () => {
  assert.equal(runtime.capturedInTernary([1], { u: [] }), -1);
  assert.deepEqual(runtime.capturedInCallback([1], [{ u: [] }]), [-1]);
});

test("Dafny refutes both false ensures", () => {
  const output = generate();
  const result = verify(output);
  assert.notEqual(result.status, 0, output + result.output);
  assert.doesNotMatch(result.output, /resolution|type errors/i, output + result.output);
  assert.match(result.output, /\b2 errors?\b/, output + result.output);
  assert.match(result.output, /capturedInTernary\(u, m\) == 0/, result.output);
  assert.match(result.output, /capturedInCallback\(u, ms\)\[i\] == 0/, result.output);
});

test("the inner match binder is distinct from the narrowed outer binder", () => {
  const output = generate();
  const body = (name: string) => {
    const start = output.indexOf(` ${name}(`);
    const end = output.indexOf("\n}\n", start);
    return output.slice(start, end);
  };
  for (const name of ["capturedInTernary", "capturedInCallback"]) {
    assert.match(body(name), /case ArrayBranch\(i_u_arr'\) =>\s+\(?\|i_u_arr'\| - \|i_u_arr\|\)?/, body(name));
  }
});
