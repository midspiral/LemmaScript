import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { addPaths, addFields, addWithUserName, earlyReturn, addMethod, counterCollision } from "../fixtures/optional-binder-collisions.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

function fixture() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/optional-binder-collisions.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function generate(): string {
  const { typesFile, defFile } = transformModuleDafny(fixture());
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

test("distinct optional paths retain their own values", () => {
  assert.equal(addPaths(3, { b: 7 }), 10);
  assert.equal(addFields({ b_c: 2 }, { c: 9 }), 11);
  assert.equal(addWithUserName(3, { b: 7 }, 11), 21);
  assert.equal(addMethod(3, { b: 7 }), 10);
  assert.equal(earlyReturn(3, { b: 7 }), 10);
  assert.equal(earlyReturn(undefined, { b: 7 }), -1);
  assert.equal(earlyReturn(3, {}), -1);
});

test("optional-chain snapshots cannot capture current storage", () => {
  assert.equal(counterCollision(3, [3]), true);
  assert.equal(counterCollision(3, [7]), false);
  assert.equal(counterCollision(0, [0]), true);
  assert.equal(counterCollision(undefined, [3]), false);
});

test("Dafny verifies the path-collision regressions and rejects a captured result", () => {
  const dir = mkdtempSync(join(tmpdir(), "lsc-optional-paths-"));
  try {
    const path = join(dir, "paths.dfy");
    const generated = generate();
    for (const [text, valid] of [[generated, true],
      [generated.replaceAll("== 10", "== 14"), false]] as const) {
      writeFileSync(path, text);
      const result = spawnSync("dafny", ["verify", "--verification-time-limit=20", path],
        { encoding: "utf8", timeout: 60_000 });
      assert.ifError(result.error);
      const output = result.stdout + result.stderr;
      assert.equal(result.status === 0, valid, output + text);
      if (!valid) {
        assert.match(output, /postcondition could not be proved/);
        assert.doesNotMatch(output, /resolution|type errors|timed out/);
      }
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});

test("optional lowering is deterministic across repeated compilations", () => {
  assert.equal(generate(), generate());
});
