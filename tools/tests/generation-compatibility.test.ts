import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { SourceProjects } from "../src/source-projects.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const projects = new SourceProjects();

// These shipped examples exercise the additions-only proof boundary. Changing
// unrelated boolean grouping or introducing unnecessary temporaries breaks it.
for (const name of ["binarySearch", "arrayFind", "countBadPairs", "forContinue", "spec", "todo-domain", "optionalLookup"]) {
  test(`nullish lowering preserves the existing ${name} proof baseline`, () => {
    const file = new URL(`../../examples/${name}.ts`, import.meta.url);
    const typed = narrowModule(resolveModule(extractModule(projects.load(fileURLToPath(file)))));
    const { typesFile, defFile } = transformModuleDafny(typed);
    const merged = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny");
    assert.equal(emitDafnyFile(merged, `${name}.ts`), readFileSync(new URL(`${name}.dfy.gen`, file), "utf8"));
  });
}

test("a callback invoking a Velvet method remains monadic", () => {
  const file = new URL("../../examples/clampAll.ts", import.meta.url);
  const typed = narrowModule(resolveModule(extractModule(projects.load(fileURLToPath(file)))));
  const { defFile } = transformModuleLean(typed);
  resetLeanModule();
  const text = emitLeanFile(peepholeModule(defFile, "lean"));
  assert.match(text, /arr\.mapM/);
  assert.match(text, /← clampElement x lo hi/);
  assert.equal(text, readFileSync(new URL("clampAll.def.lean", file), "utf8"));
});
