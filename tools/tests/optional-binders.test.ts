import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { addPaths, addFields, addWithUserName, earlyReturn, addMethod, counterCollision } from "../fixtures/optional-binder-collisions.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function fixture() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/optional-binder-collisions.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

test("distinct optional paths with colliding flattened names verify without minting binders", () => {
  assert.equal(addPaths(3, { b: 7 }), 10);
  assert.equal(addFields({ b_c: 2 }, { c: 9 }), 11);
  assert.equal(addWithUserName(3, { b: 7 }, 11), 21);
  assert.equal(addMethod(3, { b: 7 }), 10);
  assert.equal(earlyReturn(3, { b: 7 }), 10);
  assert.equal(earlyReturn(undefined, { b: 7 }), -1);
  assert.equal(earlyReturn(3, {}), -1);
  assert.equal(counterCollision(3, [3]), true);
  assert.equal(counterCollision(3, [7]), false);
  assert.equal(counterCollision(0, [0]), true);
  assert.equal(counterCollision(undefined, [3]), false);

  const { typesFile, defFile } = transformModuleDafny(fixture());
  const dafny = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.doesNotMatch(dafny, /\bmatch\b/, "coercion narrowing mints no path match binders");
  const dir = mkdtempSync(join(tmpdir(), "lsc-opt-binders-"));
  try {
    const file = join(dir, "binders.dfy");
    writeFileSync(file, dafny);
    const res = spawnSync("dafny", ["verify", "--verification-time-limit=10", file], { encoding: "utf8", timeout: 60_000 });
    assert.ifError(res.error);
    assert.equal(res.status, 0, res.stdout + res.stderr);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});

test("coercion narrowing output is deterministic across repeated compilations", () => {
  const emit = () => {
    const { typesFile, defFile } = transformModuleDafny(fixture());
    return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  };
  assert.equal(emit(), emit());
});
