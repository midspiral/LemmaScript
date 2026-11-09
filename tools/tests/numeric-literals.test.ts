import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract";
import { resolveModule } from "../src/resolve";
import { narrowModule } from "../src/narrow";
import { transformModuleDafny, transformModuleLean } from "../src/transform";
import { emitDafnyFile } from "../src/dafny-emit";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit";

function sourceModule(text: string) {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const source = project.createSourceFile("numbers.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "regressions must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function emitSource(text: string): string {
  const { typesFile, defFile } = transformModuleDafny(sourceModule(text));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "numbers.ts");
}

test("Dafny preserves an exponent-form threshold instead of truncating it to one", () => {
  const output = emitSource(`
    export function below(x: number): boolean {
      //@ type x real
      return x < 1e-10;
    }
  `);
  assert.match(output, /\(x < 0\.0000000001\)/);
});

for (const [literal, decimal, integral] of [
  ["1e-10", "0.0000000001", false],
  ["0.0000000001", "0.0000000001", false],
  ["1e21", "1000000000000000000000", true],
  ["0.000001", "0.000001", false],
  ["2.5e-7", "0.00000025", false],
  ["-1e-10", "-0.0000000001", false],
  ["-1e21", "-1000000000000000000000", true],
  ["1E+21", "1000000000000000000000", true],
  ["1.25e21", "1250000000000000000000", true],
  ["1_000e-10", "0.0000001", false],
  ["5e-324", `0.${"0".repeat(323)}5`, false],
  ["1.7976931348623157e308", `17976931348623157${"0".repeat(292)}`, true],
  ["1e20", "100000000000000000000", true],
  ["0.8", "0.8", false],
  ["-0.8", "-0.8", false],
  ["0x10", "16", true],
  ["0b10", "2", true],
  ["0o10", "8", true],
  ["1_000", "1000", true],
] as const) {
  test(`Dafny preserves ${literal} in constants, bodies and annotations`, () => {
    const output = emitSource(`
      export const threshold = ${literal};
      export function below(x: number): boolean {
        //@ type x real
        //@ ensures \\result === (x < ${literal})
        return x < ${literal};
      }
    `);
    assert.ok(output.includes(`const threshold: ${integral ? "int" : "real"} := ${decimal}\n`), output);
    const comparison = `(x < ${integral ? `(${decimal} as real)` : decimal})`;
    assert.ok(output.includes(`  ${comparison}\n`), output);
    assert.ok(output.includes(`(below(x) == ${comparison})`), output);
    assert.doesNotMatch(output, /\b\d+(?:\.\d+)?[eE][+-]?\d+/);
  });
}

test("Lean preserves large integral exponent literals without scientific syntax", () => {
  const { typesFile, defFile } = transformModuleLean(sourceModule("export const huge = 1e21;"));
  resetLeanModule();
  const output = emitLeanFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.ok(output.includes(":= 1000000000000000000000"), output);
});

test("Dafny rejects numeric literals that overflow to infinity", () => {
  assert.throws(() => emitSource("export const overflow = 1e309;"), /non-finite numeric literal/i);
});

for (const value of [Infinity, -Infinity, NaN]) {
  test(`Dafny refuses a non-finite numeric IR value: ${value}`, () => {
    assert.throws(() => emitDafnyFile({ comment: "", imports: [], options: [], decls: [
      { kind: "const", name: "invalid", type: { kind: "real" }, value: { kind: "num", value } },
    ] }), /non-finite numeric literal/i);
  });
}

test("Dafny verifies exact literal values and rejects the former threshold-one claim", () => {
  const output = emitSource(`
    export const tiny = 1e-10;
    export const huge = 1e21;
    export function tinyGuard(x: number): boolean {
      //@ type x real
      return x < tiny;
    }
    export function inlineGuard(x: number): boolean {
      //@ type x real
      return x < 0.0000000001;
    }
    export function hugeGuard(x: number): boolean {
      //@ type x real
      return x > 1e21;
    }
    export function fractionalGuard(x: number): boolean {
      //@ type x real
      return x < 2.5e-7;
    }
  `);
  const dir = mkdtempSync(join(tmpdir(), "lsc-numeric-literals-"));
  try {
    const proof = join(dir, "numbers.dfy");
    const correct = output + `
      lemma LiteralValues()
        ensures tiny == 1.0 / 10000000000.0
        ensures huge == 1000000000000000000000
        ensures !tinyGuard(0.5)
        ensures !inlineGuard(0.5)
        ensures !hugeGuard(2.0)
        ensures fractionalGuard(1.0 / 5000000.0)
      {}
    `;
    const verify = () => {
      const result = spawnSync("dafny", ["verify", "--verification-time-limit", "10", proof],
        { encoding: "utf8", timeout: 60_000 });
      assert.ifError(result.error);
      return { status: result.status, output: result.stdout + result.stderr };
    };
    writeFileSync(proof, correct);
    const baseline = verify();
    assert.equal(baseline.status, 0, baseline.output);
    writeFileSync(proof, correct + "\nlemma WrongThreshold() ensures tinyGuard(0.5) {}\n");
    const wrong = verify();
    assert.notEqual(wrong.status, 0, wrong.output);
    assert.match(wrong.output, /could not be proved|might not hold/);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
