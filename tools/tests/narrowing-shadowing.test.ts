import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import * as runtime from "../fixtures/narrowing-shadowing.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

// Regression tests for #351: narrowing substitution must stop where an inner
// declaration rebinds the narrowed name.

function generate(): string {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/narrowing-shadowing.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source))));
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-narrowing-shadowing-"));
  try {
    const proof = join(dir, "narrowing-shadowing.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("JavaScript reads the inner declaration, not the narrowed outer name", () => {
  assert.equal(runtime.shadowLet(99), 1);
  assert.equal(runtime.shadowInNestedBlock(7, true), 71);
  assert.equal(runtime.shadowInNestedBlock(7, false), 7);
  assert.equal(runtime.shadowForOf("ab", [3, 4]), 9);
  assert.equal(runtime.shadowQuantifier("abcd", [1]), 4);
  assert.equal(runtime.shadowUnion({ kind: "a", v: 99 }, true), 1);
  assert.equal(runtime.shadowUnionInNestedBlock({ kind: "a", v: 7 }, true), 71);
  assert.equal(runtime.shadowUnionInNestedBlock({ kind: "a", v: 7 }, false), 7);
  assert.equal(runtime.ghostLetDoesNotShadow(5), 5);
});

test("Dafny proves the JavaScript results for shadowed narrowed names", () => {
  const output = generate();
  const result = verify(output);
  assert.equal(result.status, 0, output + result.output);
});

test("the binder of a narrowed name does not replace reads of a shadowing declaration", () => {
  const output = generate();
  const body = (name: string) => {
    const start = output.indexOf(` ${name}(`);
    const end = output.indexOf("\n}\n", start);
    return output.slice(start, end);
  };
  assert.match(body("shadowLet"), /var (p(?:_\d+)?) := 1;\s+\1\b/);
  assert.match(body("shadowInNestedBlock"), /var (p(?:_\d+)?) := 1;\s+\(?\(?before \* 10\)? \+ \1\)?/);
  assert.match(body("shadowForOf"), /total \+ p\b/);
  assert.match(body("shadowQuantifier"), /forall p: int :: .*xs\[p\] == xs\[p\]/);
  assert.match(body("shadowUnion"), /var (s(?:_\d+)?) := a\(1\);\s+return \1\.v;/);
  assert.match(body("shadowUnionInNestedBlock"), /var (s(?:_\d+)?) := a\(1\);\s+\(?\(?before \* 10\)? \+ \1\.v\b/);
  assert.match(body("ghostLetDoesNotShadow"), /ghost var p(?:_\d+)?: int := 0;\s+return i_p_val;/);
});
