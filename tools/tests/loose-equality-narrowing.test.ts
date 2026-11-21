import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import * as fixture from "../fixtures/loose-equality-narrowing.ts";
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
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/loose-equality-narrowing.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-loose-equality-"));
  try {
    const proof = join(dir, "loose-equality.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

// Functions of `(o, x)` that return `o - x` when `o` is present. `0` is
// present, so these are presence checks, not truthiness checks.
const presence = [
  "ifLooseNull", "ifLooseUndefined", "ifNegatedStrict", "ifNegatedStrictReversed", "ifReversed",
  "ternaryLooseNull", "ternaryLooseUndefined", "ternaryNegatedStrict",
  "earlyLooseNull", "earlyLooseUndefined", "earlyReversed", "earlyNegatedStrict",
  "ternaryEqNull", "ternaryEqUndefined",
] as const;
const returns = ["returnLooseNull", "returnLooseUndefined"] as const;
const indexes = ["chainLooseNull", "chainLooseUndefined", "chainNegatedStrict", "earlyIndexLooseNull"] as const;

test("JavaScript: loose null checks and !(o === undefined) test presence", () => {
  for (const name of presence) {
    const fn = fixture[name];
    assert.deepEqual([fn(undefined, 2), fn(0, 2), fn(5, 2)], [0, -2, 3], name);
  }
  for (const name of returns) {
    const fn = fixture[name];
    assert.deepEqual([fn(undefined), fn(0), fn(7)], [0, 0, 7], name);
  }
  for (const name of indexes) {
    const fn = fixture[name];
    const a = [10, 20, 30];
    assert.deepEqual([fn(a, undefined), fn(a, 1), fn(a, -1), fn(a, 3)], [0, 20, 0, 0], name);
  }
  assert.deepEqual([fixture.looseColor("red"), fixture.looseColor("green")], [true, false]);
  assert.deepEqual(
    [fixture.optChainNotNull(undefined), fixture.optChainNotNull({}), fixture.optChainNotNull({ val: 0 })],
    [2, 2, 1],
  );
  assert.deepEqual(
    [fixture.optChainOrNotNull(undefined, false), fixture.optChainOrNotNull(undefined, true), fixture.optChainOrNotNull({ val: 0 }, false)],
    [2, 1, 1],
  );
  assert.deepEqual(
    [fixture.optChainNeqOpt(undefined, undefined), fixture.optChainNeqOpt(undefined, 5), fixture.optChainNeqOpt({ val: 5 }, 5)],
    [2, 1, 2],
  );
  assert.deepEqual(
    [fixture.optChainNeqLiteral(undefined), fixture.optChainNeqLiteral({ val: 42 }), fixture.optChainNeqLiteral({ val: 7 })],
    [-1, 42, -1],
  );
});

test("Dafny narrows optionals under loose null checks and !(o === undefined)", () => {
  const { typesFile, defFile } = transformModuleDafny(typed());
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  const facts = [
    ...presence.map(name => `
lemma ${name}Values()
  ensures ${name}(None, 2) == 0 && ${name}(Some(0), 2) == -2 && ${name}(Some(5), 2) == 3
{}
`),
    ...returns.map(name => `
lemma ${name}Values()
  ensures ${name}(None) == 0 && ${name}(Some(0)) == 0 && ${name}(Some(7)) == 7
{}
`),
    ...indexes.map(name => `
lemma ${name}Values()
  ensures ${name}([10, 20, 30], None) == 0 && ${name}([10, 20, 30], Some(1)) == 20
  ensures ${name}([10, 20, 30], Some(-1)) == 0 && ${name}([10, 20, 30], Some(3)) == 0
{}
`),
    `
lemma looseColorValues()
  ensures looseColor(Color.red) && !looseColor(Color.green)
{}

lemma optChainLooseValues()
  ensures optChainNotNull(None) == 2 && optChainNotNull(Some(OptBox(None))) == 2 && optChainNotNull(Some(OptBox(Some(0)))) == 1
  ensures optChainOrNotNull(None, false) == 2 && optChainOrNotNull(None, true) == 1 && optChainOrNotNull(Some(OptBox(Some(0))), false) == 1
  ensures optChainNeqOpt(None, None) == 2 && optChainNeqOpt(None, Some(5)) == 1 && optChainNeqOpt(Some(SolidBox(5)), Some(5)) == 2
  ensures optChainNeqLiteral(None) == -1 && optChainNeqLiteral(Some(SolidBox(42))) == 42 && optChainNeqLiteral(Some(SolidBox(7))) == -1
{}
`,
  ].join("");
  const ok = verify(output + facts);
  assert.equal(ok.status, 0, output + ok.output);
});

test("defined-check .filter(...) narrows under loose != null and !(x === undefined)", () => {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("filter-some-loose.ts", `
    export function filterLooseNull(xs: (number | undefined)[]): number[] {
      return xs.filter(x => x != null);
    }
    export function filterNegatedStrict(xs: (number | undefined)[]): number[] {
      return xs.filter(x => !(x === undefined));
    }
  `);
  assert.deepEqual(project.getPreEmitDiagnostics(), []);
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source))));
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  const ok = verify(output + `
lemma filterLooseValues()
  ensures filterLooseNull([None, Some(0), Some(5), None]) == [0, 5]
  ensures filterNegatedStrict([None, Some(0), Some(5), None]) == [0, 5]
{}
`);
  assert.equal(ok.status, 0, output + ok.output);
});

test("non-string-union synthesized datatypes do not lower string literals to constructors", () => {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("synth-string-eq.ts", `
    //@ ensures Array.isArray(x) ==> \\result === 1
    export function looseCtorCollision(x: string | string[]): number {
      if (x == "ArrayBranch") return 1;
      return 2;
    }
    export function looseEmpty(x: string | string[]): boolean {
      return x == "";
    }
  `);
  assert.deepEqual(project.getPreEmitDiagnostics(), []);
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(source))));
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.doesNotMatch(output, /\.ArrayBranch\?/);
  assert.doesNotMatch(output, /\.\?/);
  const bad = verify(output);
  assert.notEqual(bad.status, 0, "Dafny must reject comparing synthesized union directly with string");
});

test("Lean generates the loose-equality fixture", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(typed());
  const output = [typesFile, defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  assert.doesNotMatch(output, /\bo - x\b/, "o is optional; arithmetic must use its unwrapped binder");
});
