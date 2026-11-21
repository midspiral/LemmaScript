import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  whileIdx, sumFrom, countCleared, stepUntilGone, fieldPath, truthy,
} from "../fixtures/while-presence-narrowing.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function typed() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/while-presence-narrowing.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-while-presence-"));
  try {
    const proof = join(dir, "while-presence.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function body(output: string, name: string, keyword: string) {
  const start = output.indexOf(`${keyword} ${name}`);
  assert.notEqual(start, -1, `missing ${name}\n${output}`);
  const next = output.indexOf(`\n${keyword} `, start + 1);
  return output.slice(start, next === -1 ? undefined : next);
}

test("JavaScript: each loop runs while its index is present and in range", () => {
  const a = [5, 6, 7];
  assert.deepEqual([undefined, -1, 0, 2, 3].map(i => whileIdx(a, i)), [0, 0, 5, 7, 0]);
  assert.deepEqual([undefined, -1, 0, 2, 3].map(i => sumFrom(a, i)), [0, 0, 18, 7, 0]);
  assert.deepEqual([undefined, 0, 4].map(i => countCleared(i)), [0, 0, 1]);
  assert.deepEqual([undefined, -1, 0, 1, 2, 3].map(i => stepUntilGone(a, i)), [0, 0, 31, 20, 7, 0]);
  assert.deepEqual([{}, { pos: -1 }, { pos: 1 }, { pos: 3 }].map(c => fieldPath(a, c)), [0, 0, 6, 0]);
  assert.deepEqual([undefined, 0, 1, 2, 3].map(i => truthy(a, i)), [0, 0, 6, 13, 0]);
});

test("Dafny narrows the guard and body of a while presence check", () => {
  const { typesFile, defFile } = transformModuleDafny(typed());
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });

  const repro = body(output, "whileIdx", "method");
  assert.match(repro, /while \(i\.Some\? && /, "the guard tests presence with .Some? so Dafny can infer a measure");
  assert.match(repro, /var i := i;/, "a parameter assigned inside a match arm needs a mutable copy");
  assert.match(repro, /a\[i_i_val\]/, "the body reads the narrowed binder");
  assert.match(repro, /i := None;/);

  assert.match(body(output, "sumFrom", "method"), /i := Some\(\(i_i_val \+ 1\)\);/,
    "assigning a present value keeps the variable optional");
  assert.match(body(output, "countCleared", "method"), /i := None;\s*if \(match i \{/,
    "a read after the assignment sees the new, optional value");

  const ok = verify(output);
  assert.equal(ok.status, 0, output + ok.output);
});

test("Lean narrows the guard and body of a while presence check", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(typed());
  const output = [typesFile, defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");

  const repro = body(output, "whileIdx", "method");
  assert.match(repro, /let mut i : Option Int := i/);
  assert.match(repro, /while \(\(match i with \| \.some _i_val => [^\n]* \| \.none => false\) : Bool\)/,
    "a match guard is ascribed Bool so the loop condition is decidable");
  assert.match(repro, /a\[_i_val\.toNat\]!/, "the body reads the narrowed binder");
  assert.match(repro, /i := none/);
  assert.match(body(output, "sumFrom", "method"), /i := some \(_i_val \+ 1\)/,
    "assigning a present value keeps the variable optional");
});
