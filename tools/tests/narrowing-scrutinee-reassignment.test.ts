import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import * as falseRuntime from "../fixtures/narrowing-scrutinee-reassignment-false.ts";
import * as validRuntime from "../fixtures/narrowing-scrutinee-reassignment-valid.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

// Regression tests for scrutinee reassignment inside narrowed union arms
// (follow-up to #358): match-binder substitution, variant write-back frames,
// and scrutinee-update ctor stamping must not assume stale binders after
// whole-variable (or path-prefix) reassignment.

function loadTyped(fixtureName: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(
    fileURLToPath(new URL(`../fixtures/${fixtureName}`, import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [],
    `${fixtureName} must be valid TypeScript`);
  return narrowModule(resolveModule(extractModule(source)));
}

function generateDafny(fixtureName: string): string {
  const { typesFile, defFile } = transformModuleDafny(loadTyped(fixtureName));
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verifyDafny(name: string, text: string) {
  const dir = mkdtempSync(join(tmpdir(), `lsc-${name}-`));
  try {
    const proof = join(dir, `${name}.dfy`);
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

test("JavaScript gives counterexamples to every false ensures in the reassignment fixture", () => {
  const a0 = { kind: "a" as const, n: 0 };
  const p0 = { kind: "a" as const, x: 0, y: 0 };
  assert.deepEqual(falseRuntime.callbackAfterReassignment(a0, [0]), [5]);
  assert.equal(falseRuntime.directAfterReassignment(a0), 5);
  assert.deepEqual(falseRuntime.ifTagAfterReassignment(a0, [0]), [5]);
  assert.deepEqual(falseRuntime.defaultArmAfterReassignment(a0, [0]), [5]);
  assert.deepEqual(falseRuntime.conditionalReassignment(a0, true, [0]), [5]);
  assert.equal(falseRuntime.whileLoopReassignment(a0), 5);
  assert.equal(falseRuntime.fieldWriteAfterReassignment(p0), 15);
  assert.deepEqual(falseRuntime.crossVariantReassignment(a0, [0]), [5]);
  assert.equal(falseRuntime.nestedIndependentSwitchReassign(a0, a0), 10);
  assert.equal(falseRuntime.nestedIndependentSwitchSwapped(a0, a0), 10);
});

test("JavaScript matches every valid ensures in the reassignment fixture", () => {
  const a0 = { kind: "a" as const, n: 0 };
  const a2 = { kind: "a" as const, n: 2 };
  const p0 = { kind: "a" as const, x: 0, y: 0 };
  assert.deepEqual(validRuntime.callbackAfterReassignmentOk(a0, [0]), [5]);
  assert.equal(validRuntime.rhsReadsOldBinder(a2), 7);
  assert.equal(validRuntime.fieldWriteAfterReassignmentOk(p0), 15);
  assert.equal(validRuntime.fieldWriteBeforeReassignmentOk(p0), 15);
  assert.deepEqual(validRuntime.elseBranchStillUsesBinder(a0, true, [0]), [5]);
  assert.deepEqual(validRuntime.elseBranchStillUsesBinder(a0, false, [0]), [0]);
  assert.deepEqual(validRuntime.crossVariantReassignmentOk(a0, [0]), [5]);
  assert.equal(validRuntime.synthArrayUnionReassigned([1, 2]), 42);
  assert.equal(validRuntime.pathSynthArrayUnionReassigned({ u: [1, 2] }), 42);
  assert.equal(validRuntime.nestedIndependentSwitchReassignOk(a0, a0), 15);
  assert.equal(validRuntime.nestedIndependentSwitchSwappedOk(a0, a0), 15);
});

test("Dafny refutes every false ensures after scrutinee reassignment", () => {
  const output = generateDafny("narrowing-scrutinee-reassignment-false.ts");
  const result = verifyDafny("reassignment-false", output);
  assert.notEqual(result.status, 0, output + result.output);
  assert.doesNotMatch(result.output, /resolution|type errors/i, output + result.output);
  assert.match(result.output, /\b10 errors?\b/, output + result.output);
});

test("Dafny verifies every valid contract after scrutinee reassignment", () => {
  const output = generateDafny("narrowing-scrutinee-reassignment-valid.ts");
  const result = verifyDafny("reassignment-valid", output);
  assert.equal(result.status, 0, output + result.output);
});

test("Lean reads live storage and matches all uniform constructors on shared union fields after reassignment", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(loadTyped("narrowing-scrutinee-reassignment-valid.ts"));
  const output = [typesFile, defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  const cross = body(output, "crossVariantReassignmentOk");
  assert.match(cross, /match sh with \| \.a _v => _v \| \.b _v => _v/, cross);
  assert.doesNotMatch(cross, /x \+ _sh_n/, cross);
  const cb = body(output, "callbackAfterReassignmentOk");
  assert.doesNotMatch(cb, /x \+ _sh_n/, cb);
});
