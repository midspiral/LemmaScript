import { test } from "node:test";
import assert from "node:assert/strict";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function compileLean(tsText: string, fileName: string): string {
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true },
    useInMemoryFileSystem: true,
  });
  const sf = project.createSourceFile(fileName, tsText, { overwrite: true });
  const diags = project.getPreEmitDiagnostics().map(d => d.getMessageText());
  assert.deepEqual(diags, [], `invalid TS in ${fileName}: ${JSON.stringify(diags)}`);
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(narrowModule(resolveModule(extractModule(sf))));
  const optTypes = typesFile ? peepholeModule(typesFile, "lean") : null;
  const optDef = peepholeModule(defFile, "lean");
  return [optTypes ? emitLeanFile(optTypes) : "", emitLeanFile(optDef)].filter(Boolean).join("\n\n");
}

test("Math.floor(a / b) with signed or negative divisor emits Int.fdiv on Lean", () => {
  const lean = compileLean(`
export function floorDiv(a: number, b: number): number {
  //@ verify
  //@ requires b !== 0
  return Math.floor(a / b);
}

export function floorDivNegLit(a: number): number {
  //@ verify
  return Math.floor(a / -2);
}
`, "floor_div_signed.ts");

  assert.match(lean, /Int\.fdiv a b/, lean);
  assert.match(lean, /Int\.fdiv a \(-2\)/, lean);
});

test("Math.floor(a / b) with Nat or positive literal divisor keeps native / on Lean", () => {
  const lean = compileLean(`
export function midpoint(lo: number, hi: number): number {
  //@ verify
  return Math.floor((lo + hi) / 2);
}

export function floorByNat(a: number, b: number): number {
  //@ verify
  //@ type b nat
  //@ requires b > 0
  return Math.floor(a / b);
}
`, "floor_div_nonneg.ts");

  assert.match(lean, /\(lo \+ hi\) \/ 2/, lean);
  assert.match(lean, /a \/ b/, lean);
  assert.doesNotMatch(lean, /Int\.fdiv/, lean);
});
