import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { mergeNull, mergeUndefined, mergeOptionalKey } from "../fixtures/spread-null-override.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function dafny(): string {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/spread-null-override.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source))));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

function bodyOf(text: string, name: string): string {
  const start = text.indexOf(`function ${name}(`);
  assert.ok(start >= 0, `missing ${name}`);
  const next = text.slice(start + 1).search(/\n(?:function|lemma) /);
  return next < 0 ? text.slice(start) : text.slice(start, start + 1 + next);
}

test("spread copies a present null/undefined and skips an absent key at runtime", () => {
  assert.equal(mergeNull({ a: 1, b: 0 }, { a: null, b: 0 }), null);
  assert.equal(mergeUndefined({ a: 1, b: 0 }, { a: undefined, b: 0 }), undefined);
  assert.equal(mergeOptionalKey({ a: 1, b: 0 }, { b: 0 }), 1);
});

test("Dafny falls back to the base field only for `?` keys", () => {
  const text = dafny();
  assert.ok(bodyOf(text, "mergeNull").includes("N(y.a, y.b)"));
  assert.ok(bodyOf(text, "mergeUndefined").includes("U(y.a, y.b)"));
  assert.ok(bodyOf(text, "mergeOptionalKey").includes("case None => x.a"));
});
