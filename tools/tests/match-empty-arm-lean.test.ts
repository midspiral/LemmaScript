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

test("empty switch case before non-empty default emits pure () instead of falling into default", () => {
  const lean = compileLean(`
type Tag = "a" | "b" | "c";

export function switchEmptyWithDefault(t: Tag): number {
  //@ verify
  //@ ensures t === "a" ==> \\result === 0
  //@ ensures t !== "a" ==> \\result === 1
  let x = 0;
  switch (t) {
    case "a":
      break;
    default:
      x = 1;
      break;
  }
  return x;
}
`, "switch_empty_default.ts");

  assert.match(lean, /if t = Tag\.a then\n\s+pure \(\)\n\s+else\n\s+x := 1/, lean);
});

test("exhaustive switch keeps empty arm before non-empty final arm", () => {
  const lean = compileLean(`
type Tag = "a" | "b" | "c";

export function switchMiddleEmpty(t: Tag): number {
  //@ verify
  //@ ensures t === "a" ==> \\result === 1
  //@ ensures t === "b" ==> \\result === 0
  //@ ensures t === "c" ==> \\result === 2
  let x = 0;
  switch (t) {
    case "a":
      x = 1;
      break;
    case "b":
      break;
    case "c":
      x = 2;
      break;
  }
  return x;
}
`, "switch_middle_empty.ts");

  assert.match(lean, /if t = Tag\.a then\n\s+x := 1\n\s+else if t = Tag\.b then\n\s+pure \(\)\n\s+else\n\s+x := 2/, lean);
});

test("discriminated union switch keeps empty arm before non-empty payload arm", () => {
  const lean = compileLean(`
type Shape = { kind: "empty" } | { kind: "box"; w: number };

export function shapeWidth(s: Shape): number {
  //@ verify
  let x = 0;
  switch (s.kind) {
    case "empty":
      break;
    case "box":
      x = s.w;
      break;
  }
  return x;
}
`, "switch_union_empty.ts");

  assert.match(lean, /if \(?match s with \| \.empty => true \| _ => false\)? then\n\s+pure \(\)\n\s+else/, lean);
});

test("trailing empty arm with no default is still omitted cleanly", () => {
  const lean = compileLean(`
type Tag = "a" | "b";

export function switchTrailingEmpty(t: Tag): number {
  //@ verify
  let x = 0;
  switch (t) {
    case "a":
      x = 1;
      break;
    case "b":
      break;
  }
  return x;
}
`, "switch_trailing_empty.ts");

  assert.match(lean, /if t = Tag\.a then\n\s+x := 1\n\s+return x/, lean);
  assert.doesNotMatch(lean, /pure \(\)/, lean);
});
