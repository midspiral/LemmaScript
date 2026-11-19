import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  objectDefault, defaultIntoOptional, renamedDefault, arrayDefault, secondDefault,
} from "../fixtures/destructuring-default.ts";
import {
  optionalDefault, nullableDefault, nullDefault, nullableArrayDefault, optionalArrayDefault,
  nullishDefault, nullishArrayDefault, nullableParameterDefault, renamedNullableParameterDefault,
  nullishParameterDefault, mixedDefault, mixedArrayDefault, unreachableDefault,
  parameterDefault, renamedParameterDefault, genericParameterDefault,
} from "../../examples/destructuringDefaults.ts";
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

test("destructuring preserves null and falsy values, and defaults only undefined", () => {
  for (const value of [null, 0, 2]) {
    assert.equal(nullableDefault({ value }), value);
    assert.equal(nullableArrayDefault([value]), value);
    assert.equal(nullableParameterDefault({ value }), value);
    assert.equal(renamedNullableParameterDefault({ value }), value);
    assert.equal(unreachableDefault({ value }), value);
    assert.equal(mixedDefault({ value }), value);
    assert.equal(mixedArrayDefault([value]), value);
  }
  for (const value of [undefined, 0, 2]) {
    assert.equal(optionalDefault({ value }), value === undefined ? 5 : value);
    assert.equal(nullDefault({ value }), value === undefined ? null : value);
    assert.equal(optionalArrayDefault([value]), value === undefined ? 7 : value);
  }
  assert.equal(optionalDefault({}), 5);
  assert.equal(nullableArrayDefault([]), 7);
  assert.equal(optionalArrayDefault([]), 7);
  assert.equal(mixedDefault({}), 5);
  assert.equal(mixedDefault({ value: undefined }), 5);
  assert.equal(mixedArrayDefault([]), 7);
  assert.equal(mixedArrayDefault([undefined]), 7);
});

test("a null default composes with sources containing both null and undefined", () => {
  for (const value of [undefined, null, 0, 2]) {
    assert.equal(nullishDefault({ value }), value === undefined ? null : value);
    assert.equal(nullishArrayDefault([value]), value === undefined ? null : value);
    assert.equal(nullishParameterDefault({ value }), value === undefined ? null : value);
  }
  assert.equal(nullishDefault({}), null);
  assert.equal(nullishArrayDefault([]), null);
});

test("Dafny keeps the default value", () => {
  const text = dafny();
  for (const name of ["objectDefault", "defaultIntoOptional", "renamedDefault"]) {
    assert.ok(bodyOf(text, name).includes("case None => 5"), name);
  }
  assert.ok(bodyOf(text, "arrayDefault").includes("if (0 < |xs|) then xs[0] else 7"));
  assert.ok(bodyOf(text, "secondDefault").includes("if (1 < |xs|) then xs[1] else 9"));
});

test("mixed null and undefined defaults stay pure in the shared Option model", () => {
  for (const binding of ["const { a = 5 } = o;", "const [a = 5] = xs;"]) {
    const mod = resolveModule(extract(`
    interface Z { a?: number | null }
    export function f(o: Z, xs: (number | null | undefined)[]): number {
      //@ verify
      ${binding}
      return a ?? 0;
    }`)());
    assert.equal(mod.functions.find(f => f.name === "f")?.isPure, true);
  }
});

test("flattened parameters use their post-default types and retain source defaults", () => {
  const mod = extract(`
    interface Q { value?: number }
    export function f({ value: a = 5 }: Q): number {
      return a;
    }
  `)();
  const fn = mod.functions.find(f => f.name === "f")!;
  assert.deepEqual(fn.params, [{ name: "a", tsType: "number" }]);
  assert.deepEqual(fn.tsParams, [{ kind: "object", binds: ["a"], defaults: { a: "5" } }]);

  assert.equal(parameterDefault({}), 5);
  assert.equal(parameterDefault({ value: 0 }), 0);
  assert.equal(renamedParameterDefault({}), 5);
  assert.equal(renamedParameterDefault({ value: null }), null);
  assert.equal(genericParameterDefault(5, { value: undefined }), 5);
  assert.doesNotThrow(extract(`
    export function f<T>(fallback: T, { a = fallback }: { a: T }): T {
      return a;
    }`));
});
