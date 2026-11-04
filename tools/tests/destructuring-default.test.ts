import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  objectDefault, defaultIntoOptional, renamedDefault, arrayDefault, secondDefault,
} from "../fixtures/destructuring-default.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function project() {
  return new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
}

function dafny(): string {
  const p = project();
  const source = p.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/destructuring-default.ts", import.meta.url)));
  assert.deepEqual(p.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source))));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

function bodyOf(text: string, name: string): string {
  const start = text.indexOf(`function ${name}(`);
  assert.ok(start >= 0, `missing ${name}`);
  const next = text.slice(start + 1).search(/\n(?:function|lemma) /);
  return next < 0 ? text.slice(start) : text.slice(start, start + 1 + next);
}

function extract(code: string) {
  return () => extractModule(project().createSourceFile("probe.ts", code));
}

test("destructuring defaults apply at runtime", () => {
  assert.equal(objectDefault({ b: 0 }), 5);
  assert.equal(defaultIntoOptional({ b: 0 }), 5);
  assert.equal(renamedDefault({ b: 1 }), 6);
  assert.equal(arrayDefault([]), 7);
  assert.equal(secondDefault([1]), 9);
});

test("Dafny keeps the default value", () => {
  const text = dafny();
  for (const name of ["objectDefault", "defaultIntoOptional", "renamedDefault"]) {
    assert.ok(bodyOf(text, name).includes("case None => 5"), name);
  }
  assert.ok(bodyOf(text, "arrayDefault").includes("if (0 < |xs|) then xs[0] else 7"));
  assert.ok(bodyOf(text, "secondDefault").includes("if (1 < |xs|) then xs[1] else 9"));
});

test("defaults that can't be modeled are rejected", () => {
  assert.throws(extract(`
    interface Z { a: number | null }
    export function f(o: Z): number {
      //@ verify
      const { a = 5 } = o;
      return a ?? 0;
    }`), /may be null/);
  assert.throws(extract(`
    interface Q { a?: number }
    export function f({ a = 5 }: Q): number {
      //@ verify
      return a;
    }`), /parameter destructuring/);
});
