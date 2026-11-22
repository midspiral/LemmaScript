import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import * as runtime from "../fixtures/narrowing-closures-and-loop-specs.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

// Regression tests for #353: narrowing substitution must reach lambda bodies
// and loop decreases/done_with clauses.

function typed() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(
    fileURLToPath(new URL("../fixtures/narrowing-closures-and-loop-specs.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function generateDafny(): string {
  const { typesFile, defFile } = transformModuleDafny(typed());
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-narrowing-closures-"));
  try {
    const proof = join(dir, "narrowing-closures-and-loop-specs.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--standard-libraries", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function body(output: string, name: string): string {
  const start = output.indexOf(` ${name}`);
  assert.notEqual(start, -1, `${name} missing from output`);
  const next = output.slice(start + 1).search(/\n(function|method|def|theorem) /);
  return next === -1 ? output.slice(start) : output.slice(start, start + 1 + next);
}

test("JavaScript closures and loops read the narrowed value", () => {
  assert.deepEqual(runtime.closureReadsNarrowed(10, [1, 2]), [11, 12]);
  assert.deepEqual(runtime.blockClosureReadsNarrowed(10, [1, 2]), [11, 12]);
  assert.equal(runtime.predicateReadsNarrowed(0, [1, 2]), true);
  assert.deepEqual(runtime.lambdaParamShadows("s", [1, 2]), [2, 3]);
  assert.equal(runtime.whileDecreasesNarrowed(3), 3);
});

test("Dafny accepts narrowed reads in closures and loop decreases", () => {
  const output = generateDafny();
  const result = verify(output);
  assert.equal(result.status, 0, output + result.output);
});

test("the binder replaces narrowed reads in closures and decreases, but not a shadowing lambda parameter", () => {
  const output = generateDafny();
  assert.match(body(output, "closureReadsNarrowed("), /\(x \+ i_o_val\)/);
  assert.match(body(output, "blockClosureReadsNarrowed("), /var y := \(x \+ i_o_val\)/);
  assert.match(body(output, "predicateReadsNarrowed("), /\(x > i_o_val\)/);
  assert.match(body(output, "lambdaParamShadows("), /var p := xs\[i_map\]; \(p \+ 1\)/);
  assert.match(body(output, "whileDecreasesNarrowed("), /decreases \(i_o_val - i\)/);
});

test("Lean done_with uses the binder of a narrowed name", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(typed());
  const output = [typesFile, defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  const loop = body(output, "whileDecreasesNarrowed");
  assert.match(loop, /done_with \(i = _o_val\b/, loop);
  assert.doesNotMatch(loop, /decreasing [^\n]*(?<!_)\bo\b/, loop);
});
