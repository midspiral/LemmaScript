import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { ifThen, earlyReturn, ternary } from "../fixtures/double-negation-narrowing.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function typed() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/double-negation-narrowing.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-double-negation-"));
  try {
    const proof = join(dir, "double-negation.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const cases: [number | undefined, number][] = [[undefined, 2], [0, 2], [5, 2], [-3, 2]];

test("JavaScript: !!o and !!!o test o's truthiness, so 0 counts as absent", () => {
  for (const fn of [ifThen, earlyReturn, ternary]) {
    assert.deepEqual(cases.map(([o, x]) => fn(o, x)), [0, 0, 3, -5]);
  }
});

test("Dafny narrows o under !!o and !!!o", () => {
  const { typesFile, defFile } = transformModuleDafny(typed());
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  const facts = ["ifThen", "earlyReturn", "ternary"].map(name => `
lemma ${name}Values()
  ensures ${name}(None, 2) == 0 && ${name}(Some(0), 2) == 0
  ensures ${name}(Some(5), 2) == 3 && ${name}(Some(-3), 2) == -5
{}
`).join("");
  const ok = verify(output + facts);
  assert.equal(ok.status, 0, output + ok.output);
});

test("Lean narrows o under !!o and !!!o", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(typed());
  const output = [typesFile, defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  for (const name of ["ifThen", "earlyReturn", "ternary"]) {
    const body = output.slice(output.indexOf(`def ${name}`));
    assert.match(body, /^def \w+[^\n]*\n\s*match o with/, output);
  }
  assert.doesNotMatch(output, /\bo - x\b/, "o is optional; arithmetic must use its unwrapped binder");
});
