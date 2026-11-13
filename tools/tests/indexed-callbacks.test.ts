import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { DEFAULT_OPTIONS } from "../src/config.ts";
import { pairwiseAtMost, plusIndex } from "../../examples/indexedCallbacks.ts";

const example = readFileSync(new URL("../../examples/indexedCallbacks.ts", import.meta.url), "utf8");

function generate(source = example, library: "stdlib" | "local" = "stdlib") {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("indexedCallbacks.ts", source);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(file))));
  const module = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny");
  return emitDafnyFile(module, undefined, { ...DEFAULT_OPTIONS, "dafny-library": library });
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-indexed-callbacks-"));
  try {
    const path = join(dir, "indexed.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--standard-libraries", "--verification-time-limit=15", path],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

test("issue #288 examples agree with JavaScript, including empty arrays", () => {
  assert.equal(pairwiseAtMost([1, 2], [1, 3]), true);
  assert.equal(pairwiseAtMost([1, 4], [1, 3]), false);
  assert.equal(pairwiseAtMost([], []), true);
  assert.equal(pairwiseAtMost([1], []), false);
  assert.deepEqual(plusIndex([10, 10, 10]), [10, 11, 12]);
  assert.deepEqual(plusIndex([]), []);
});

for (const library of ["stdlib", "local"] as const) test(`issue #288 examples verify with ${library} helpers`, () => {
  // Reuse the proof additions from the example against freshly generated code.
  const companion = readFileSync(new URL("../../examples/indexedCallbacks.dfy", import.meta.url), "utf8");
  const start = companion.indexOf("lemma IndexedCallbackExamples()");
  assert.notEqual(start, -1, "the example must retain its behavioral proof");
  const facts = companion.slice(start).replace("reveal Std.Collections.Seq.All();",
    library === "stdlib" ? "reveal Std.Collections.Seq.All();" : "reveal SeqAll();");
  const result = verify(generate(example, library) + "\n" + facts);
  assert.equal(result.status, 0, result.output);
});

test("indexed callbacks cannot capture escaped or shadowed outer names", () => {
  for (const source of [
    `export function f(_q: number): boolean {
      //@ requires _q === 2
      //@ ensures \\result === true
      return [7].every((value, index) => value >= 0 && index === _q);
    }`,
    `export function f(index: number): boolean {
      //@ requires index === 1
      //@ ensures \\result === true
      return [7].some((value, index, source) => index === 1);
    }`,
  ]) {
    const result = verify(generate(source));
    assert.notEqual(result.status, 0, result.output);
    assert.match(result.output, /postcondition could not be proved/);
  }
});

test("unused index parameters preserve element-only every and map output", () => {
  for (const [method, body, result] of [["every", "value > 0", "boolean"], ["map", "value + 1", "number[]"]]) {
    const source = (parameters: string) => `export function f(xs: number[]): ${result} {
      return xs.${method}((${parameters}) => ${body});
    }`;
    assert.equal(generate(source("value, index")), generate(source("value")));
  }
});
