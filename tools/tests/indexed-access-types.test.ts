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

// Indexed access types (`T["k"]`) name a property's type. The checker resolves
// them; the annotation's source text alone does not say what the type is.
const source = `
export interface Info { kind: "a" | "b"; count: number; tags: string[] }

export function sameKind(x: Info["kind"], y: Info["kind"]): boolean {
  return x === y;
}
export function kindOf(i: Info): Info["kind"] {
  return i.kind;
}
export function total(...counts: Info["count"][]): number {
  let sum: Info["count"] = 0;
  for (let i: Info["count"] = 0; i < counts.length; i++) sum += counts[i];
  return sum;
}
export function hasKind(i: Info, ...kinds: Info["kind"][]): boolean {
  return kinds.includes(i.kind);
}
export function firstTag(i: Info): Info["tags"][number] | undefined {
  return i.tags.length > 0 ? i.tags[0] : undefined;
}
export function doubled(i: Info): number[] {
  return [i.count].map((c: Info["count"]) => c * 2);
}
`;

function emit() {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("indexed.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(file))));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "indexed.ts");
}

test("Dafny resolves indexed access types to the property's type", () => {
  const output = emit();
  assert.doesNotMatch(output, /\["|\]\[number\]|i__type/, output);
  assert.match(output, /function sameKind\(x: string, y: string\): bool/, output);
  assert.match(output, /function kindOf\(i: Info\): string/, output);
  assert.match(output, /method total\(counts: seq<int>\) returns \(res: int\)|function total\(counts: seq<int>\): int/, output);
  assert.match(output, /function hasKind\(i: Info, kinds: seq<string>\): bool/, output);
  assert.match(output, /function firstTag\(i: Info\): Option<string>/, output);

  const dir = mkdtempSync(join(tmpdir(), "lsc-indexed-access-"));
  try {
    const proof = join(dir, "indexed.dfy");
    writeFileSync(proof, output);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    assert.equal(result.status, 0, result.stdout + result.stderr);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
