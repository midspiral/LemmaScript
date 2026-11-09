import { test } from "node:test";
import assert from "node:assert/strict";
import { Project } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function emit(spec: string): string {
  const project = new Project({ useInMemoryFileSystem: true });
  const file = project.createSourceFile("/main.ts", `
export function identity(xs: number[]): number[] {
  //@ ensures ${spec}
  return xs;
}`);
  const mod = narrowModule(resolveModule(extractModule(file)));
  const { typesFile, defFile } = transformModuleDafny(mod);
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

test("perm preserves calls to helpers defined in the proof file", () => {
  const dafny = emit("perm(helper(xs), xs) && perm(xs, helper(xs))");
  assert.match(dafny, /predicate Perm<T\(==\)>\(a: seq<T>, b: seq<T>\)/);
  assert.match(dafny, /ensures Perm\(helper\(xs\), xs\)/);
  assert.match(dafny, /ensures Perm\(xs, helper\(xs\)\)/);
});

test("perm leaves invalid argument types for the backend to reject", () => {
  assert.match(emit("perm(1, 2)"), /ensures Perm\(1, 2\)/);
});
