import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { nestedTernary, nestedStatement } from "../fixtures/narrowing-binder-capture.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const sourceText = readFileSync(new URL("../fixtures/narrowing-binder-capture.ts", import.meta.url), "utf8");

function generate(text: string, backend: "dafny" | "lean" = "dafny"): string {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("binder-capture.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [],
    "the regression must be valid TypeScript");
  const typed = narrowModule(resolveModule(extractModule(source)));
  const { typesFile, defFile } = backend === "dafny" ? transformModuleDafny(typed) : transformModuleLean(typed);
  const mod = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, backend);
  if (backend === "dafny") return emitDafnyFile(mod);
  resetLeanModule();
  return emitLeanFile(mod);
}

const siblingSource = `
type Action = { kind: "first"; idx: number } | { kind: "second"; idx: number } | { kind: "third"; idx: number };
export function siblingSwitch(a: Action): number {
  //@ ensures a.kind === "first" ==> \\result === a.idx
  //@ ensures a.kind === "second" ==> \\result === a.idx + 1
  //@ ensures a.kind === "third" ==> \\result === a.idx + 2
  switch (a.kind) {
    case "first": return a.idx;
    case "second": return a.idx + 1;
    case "third": return a.idx + 2;
  }
}
export function siblingStatements(a: Action): number {
  //@ ensures \\result === siblingSwitch(a)
  let result = 0;
  switch (a.kind) {
    case "first": result = a.idx; break;
    case "second": result = a.idx + 1; break;
    case "third": result = a.idx + 2; break;
  }
  return result;
}
`;

test("sibling match arms and independent contracts reuse their original binders", () => {
  const dafny = generate(siblingSource);
  for (const variant of ["first", "second", "third"]) {
    assert.ok(dafny.includes(`case ${variant}(i_a_idx) =>`), dafny);
  }
  assert.doesNotMatch(dafny, /i_a_idx'/);
  const lean = generate(siblingSource, "lean");
  for (const variant of ["first", "second", "third"]) {
    assert.ok(lean.includes(`| .${variant} _a_idx =>`), lean);
  }
  // The original nested collision still needs distinct names on both backends.
  assert.match(generate(sourceText), /i_u_arr'/);
  assert.match(generate(sourceText, "lean"), /_u_arr'/);
  const result = verify(dafny);
  assert.equal(result.status, 0, result.output);
});

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-binder-capture-"));
  try {
    const path = join(dir, "capture.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", path],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("nested narrowing reads two different arrays at runtime", () => {
  for (const fn of [nestedTernary, nestedStatement]) assert.equal(fn([1], { u: [] }), -1);
});

test("Dafny proves the actual result of both nested matches", () => {
  const generated = generate(sourceText);
  const result = verify(generated + `
lemma concreteCounterexample()
  ensures nestedTernary(ArrayBranch([1]), Msg(ArrayBranch([]))) == -1
{}
`);
  assert.equal(result.status, 0, generated + result.output);
});

test("Dafny rejects the false zero result, without syntax or type errors", () => {
  const generated = generate(sourceText.replaceAll(/ensures .*$/gm, "ensures \\result === 0"));
  const result = verify(generated);
  assert.notEqual(result.status, 0, generated + result.output);
  assert.doesNotMatch(result.output, /resolution|type errors|timed out/i, generated + result.output);
  assert.match(result.output, /\b2 errors\b/, result.output);
  assert.match(result.output, /postcondition could not be proved/, result.output);
});
