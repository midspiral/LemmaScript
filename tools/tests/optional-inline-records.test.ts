import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { copyFileSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import { Project } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const exampleDir = fileURLToPath(new URL("../../examples/", import.meta.url));
const exampleName = "optionalInlineRecords";
const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const loader = createRequire(import.meta.url).resolve("tsx");

function extract(source: string, exactOptionalPropertyTypes: boolean) {
  const project = new Project({ useInMemoryFileSystem: true,
    compilerOptions: { strict: true, exactOptionalPropertyTypes, types: [] } });
  const file = project.createSourceFile("/optional.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return extractModule(file);
}

for (const exact of [false, true]) {
  test(`inline records preserve optional keys and nullish values (exact=${exact})`, () => {
    const raw = extract(`
interface Named { value?: string }
interface Base { inherited?: { value?: string } }
interface Api extends Base {
  inline?: { value?: string };
  named?: Named;
  required: { value?: string };
  nullable: { value?: string } | null;
  undefinable: { value?: string } | undefined;
  both?: { value?: string } | null | undefined;
  nested?: { child?: { value?: string } };
}
type PartialApi = Partial<{ fallback: { value?: string } }>;
`, exact);
    const typed = resolveModule(raw);
    const api = typed.typeDecls.find(d => d.name === "Api")!;
    for (const [field, inner] of [
      ["inline", "ApiInline"], ["named", "Named"], ["nullable", "ApiNullable"],
      ["undefinable", "ApiUndefinable"], ["both", "ApiBoth"], ["nested", "ApiNested"],
      ["inherited", "ApiInherited"],
    ]) {
      assert.deepEqual(api.fields!.find(f => f.name === field)!.type,
        { kind: "optional", inner: { kind: "user", name: inner } }, field);
    }
    assert.deepEqual(api.fields!.find(f => f.name === "required")!.type,
      { kind: "user", name: "ApiRequired" });
    const partial = typed.typeDecls.find(d => d.name === "PartialApi")!;
    assert.equal(partial.fields![0].optionalKey, true, "mapped optional keys have no question token");
    assert.deepEqual(partial.fields![0].type,
      { kind: "optional", inner: { kind: "user", name: "PartialApiFallback" } });
    const nested = typed.typeDecls.find(d => d.name === "ApiNested")!;
    assert.deepEqual(nested.fields![0].type,
      { kind: "optional", inner: { kind: "user", name: "ApiNestedChild" } });

    const { typesFile, defFile } = transformModuleDafny(typed);
    const dafny = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
    resetLeanModule();
    const lean = emitLeanFile(transformModuleLean(typed).typesFile!);
    assert.match(dafny, /inline: Option<ApiInline>/);
    assert.match(lean, /inline : Option ApiInline/);
    assert.doesNotMatch(dafny + lean, /__type|Option<Option|Option \(Option/);
  });

  test(`optional inline record example verifies through the CLI (exact=${exact})`, () => {
    const dir = mkdtempSync(join(tmpdir(), "lsc-optional-inline-"));
    try {
      for (const extension of ["ts", "dfy", "dfy.gen"]) {
        const name = `${exampleName}.${extension}`;
        copyFileSync(join(exampleDir, name), join(dir, name));
      }
      const configPath = join(dir, "tsconfig.json");
      const config = JSON.parse(readFileSync(join(exampleDir, "tsconfig.json"), "utf8"));
      config.compilerOptions.exactOptionalPropertyTypes = exact;
      writeFileSync(configPath, JSON.stringify(config));
      const project = new Project({ tsConfigFilePath: configPath });
      assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
      const result = spawnSync(process.execPath,
        ["--import", loader, cli, "check", "--backend=dafny", "--time-limit=20", join(dir, `${exampleName}.ts`)],
        { encoding: "utf8", timeout: 120_000, env: { ...process.env, LSC_RUN_LOG: "false" } });
      assert.ifError(result.error);
      assert.equal(result.status, 0, result.stdout + result.stderr);
      assert.match(result.stdout, /[1-9]\d* verified, 0 errors/);
      const output = readFileSync(join(dir, `${exampleName}.dfy.gen`), "utf8");
      assert.match(output, /datatype Api = Api\(name: string, fallback: Option<ApiFallback>\)/);
      assert.match(output, /Api\(name, None\)/);
      assert.match(output, /Api\(name, Some\(ApiFallback\(None\)\)\)/);
      assert.match(output, /Api\(name, Some\(ApiFallback\(Some\(value\)\)\)\)/);
      assert.doesNotMatch(output, /missing:|map\[\]/);
      assert.equal(output, readFileSync(join(exampleDir, `${exampleName}.dfy.gen`), "utf8"), "committed example is current");
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
}

test("record constructors follow their resolved type when another record has only optional fields", () => {
  const raw = extract(`
interface Unrelated { hint?: string; detail?: string }
interface Api { name: string; fallback?: { value?: string } }
export function noFallback(name: string): Api { return { name }; }
export function emptyFallback(name: string): Api { return { name, fallback: {} }; }
`, true);
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(raw)));
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.match(output, /Api\(name, None\)/);
  assert.match(output, /Api\(name, Some\(ApiFallback\(None\)\)\)/);
});
