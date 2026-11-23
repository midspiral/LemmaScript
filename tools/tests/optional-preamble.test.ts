import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function emitSource(body: string, declarations = ""): string {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("local-optional.ts", `${declarations}\nexport function localOptional(): number { ${body} }`);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "regressions must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source))));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "local-optional.ts");
}

// Emit each case as a separate file: an optional in another function could
// supply the preamble and hide the missing dependency (issue #357).
for (const [name, body] of [
  ["mutable local", "let a: number | undefined = 5; return a === undefined ? 0 : a;"],
  ["constant local", "const a: number | undefined = 5; return a === undefined ? 0 : a;"],
  ["undefined local", "let a: number | undefined = undefined; return a ?? 0;"],
  ["assignment", "let a: number | undefined = undefined; a = 5; return a ?? 0;"],
  ["array pop", "const values: number[] = [5]; let a = values.pop(); return a ?? 0;"],
]) {
  test(`Dafny declares Option for a file with only a local optional: ${name}`, () => {
    const output = emitSource(body);
    assert.equal(output.match(/datatype Option<T> = None \| Some\(value: T\)/g)?.length, 1, output);
    const dir = mkdtempSync(join(tmpdir(), "lsc-optional-preamble-"));
    try {
      const proof = join(dir, "local-optional.dfy");
      writeFileSync(proof, output);
      const result = spawnSync("dafny", ["verify", "--verification-time-limit", "10", proof],
        { encoding: "utf8", timeout: 60_000 });
      assert.ifError(result.error);
      assert.equal(result.status, 0, result.stdout + result.stderr);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
}

test("Dafny omits Option when the file has no optional values", () => {
  assert.doesNotMatch(emitSource("let a = 5; return a;"), /datatype Option/);
});

test("a user datatype constructor named Some does not request Option", () => {
  const output = emitSource('const a: Choice = { tag: "Some", value: 5 }; return a.value;',
    'type Choice = { tag: "Some"; value: number } | { tag: "None" };');
  assert.doesNotMatch(output, /datatype Option/);
});
