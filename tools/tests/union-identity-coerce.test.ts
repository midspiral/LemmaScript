import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function fixture() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/union-identity-coerce.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the fixture must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

test("a value already typed as the synth union is not double-wrapped", () => {
  const mod = fixture();
  const { typesFile, defFile } = transformModuleDafny(mod);
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.doesNotMatch(output, /NonArrayBranch\(c\.aud\)/,
    "c.aud is already the union type and must not be wrapped in NonArrayBranch");
  assert.match(output, /audiences\(c\.aud\)/,
    "c.aud should be passed directly to audiences()");
});

test("audienceCount emits without Dafny errors", () => {
  const mod = fixture();
  const { typesFile, defFile } = transformModuleDafny(mod);
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.doesNotMatch(output, /ERROR/i, "emission must not contain errors");
  assert.ok(output.includes("audienceCount"), "audienceCount should appear in the output");
});
