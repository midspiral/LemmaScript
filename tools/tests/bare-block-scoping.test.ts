import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget, type SourceFile } from "ts-morph";
import * as runtime from "../fixtures/bare-block-scoping.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

// A declaration inside a bare `{ }` block goes out of scope at the closing
// brace (#361). Flattening the block without renaming verified false claims.

function source(text?: string): SourceFile {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = text === undefined
    ? project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/bare-block-scoping.ts", import.meta.url)))
    : project.createSourceFile("scoping.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [],
    "the regression must be valid TypeScript");
  return file;
}

function generate(text?: string): string {
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source(text)))));
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-bare-block-scoping-"));
  try {
    const proof = join(dir, "bare-block-scoping.dfy");
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
  assert.equal(runtime.bareBlock(3), 3);
  assert.equal(runtime.bareBlockMethod(3), 3);
  assert.equal(runtime.bareBlockNarrowed(7), 7);
});

test("Dafny refutes each false ensures after a bare block", () => {
  const output = generate();
  const result = verify(output);
  assert.notEqual(result.status, 0, output + result.output);
  assert.doesNotMatch(result.output, /resolution|type errors/i, output + result.output);
  assert.match(result.output, /\b3 errors\b/, output + result.output);
});

test("sibling blocks, specs that read fields, and non-colliding blocks", () => {
  const output = generate(String.raw`
export type S = { p: number };

//@ ensures \result === p + 3
export function siblingBlocks(p: number): number {
  let r = 0;
  {
    const p = 1;
    r = r + p;
  }
  {
    const p = 2;
    r = r + p;
  }
  return r + p;
}

//@ ensures \result === p
export function specReadsField(s: S, p: number): number {
  let r = 0;
  {
    const p = s.p + 1;
    //@ assert p === s.p + 1
    r = r + p;
  }
  return p;
}

//@ ensures \result === p + 1
export function noCollision(p: number): number {
  let r = 0;
  {
    const q = 1;
    r = r + q;
  }
  return p + r;
}
`);
  const result = verify(output);
  assert.equal(result.status, 0, output + result.output);
  assert.match(output, /var q := 1;/, output);
  assert.match(output, /s\.p \+ 1/, output);
  assert.doesNotMatch(output, /s\.p_/, output);
});
