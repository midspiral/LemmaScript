import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract";
import { resolveModule } from "../src/resolve";
import { narrowModule } from "../src/narrow";
import { transformModuleDafny } from "../src/transform";
import { emitDafnyFile } from "../src/dafny-emit";

// A `BigInt(n)` / `Number(n)` result returned where an optional is expected
// must be wrapped in `Some`, exactly like the plain operand `n` would be.
const source = `
export function positiveBig(n: number): bigint | null {
  return n > 0 ? BigInt(n) : null;
}
export function positiveSmall(n: bigint): number | null {
  if (n > 0n) return Number(n);
  return null;
}
`;

const facts = `
lemma ConversionResults()
  ensures positiveBig(3) == Some(3) && positiveBig(0) == None
  ensures positiveSmall(4) == Some(4) && positiveSmall(-1) == None
{}
`;

test("Dafny wraps an integer BigInt()/Number() conversion returned as an optional", () => {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("conv.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(file))));
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "conv.ts");
  const dir = mkdtempSync(join(tmpdir(), "lsc-bigint-conversion-"));
  try {
    const proof = join(dir, "conv.dfy");
    writeFileSync(proof, output + facts);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    assert.equal(result.status, 0, result.stdout + result.stderr);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
