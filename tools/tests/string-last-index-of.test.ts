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

const source = `
export function last(s: string, sub: string): number {
  return s.lastIndexOf(sub);
}
export function lastAt(s: string, sub: string, position: number): number {
  return s.lastIndexOf(sub, position);
}
`;

function sourceModule() {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("last.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

function emitDafny() {
  const { typesFile, defFile } = transformModuleDafny(sourceModule());
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "last.ts");
}

function dafny(args: string[], text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-last-index-of-"));
  try {
    const proof = join(dir, "last.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", [...args, proof], { encoding: "utf8", timeout: 180_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const verify = (text: string) => dafny(["verify", "--verification-time-limit", "30"], text);

const dafnyString = (s: string) => JSON.stringify(s);

// The emitted functions are compiled and run, and every result is compared
// with JavaScript's own lastIndexOf, including the empty needle (which matches
// at the clamped position) and positions outside [0, |s|]. Running the code
// avoids asking the verifier to prove literal sequence disequalities, which it
// cannot do without per-index hints.
test("Dafny's string lastIndexOf computes JavaScript's result", () => {
  const output = emitDafny();
  assert.match(output, /StringLastIndexOf\(s, sub\)/, output);
  assert.match(output, /StringLastIndexOfFrom\(s, sub, StringSearchPosition\(s, position\)\)/, output);
  const calls: string[] = [];
  const expected: number[] = [];
  for (const s of ["", "abc", "aba", "a.b.c"]) {
    for (const sub of ["", "a", "b", ".", "ab", "abcd"]) {
      calls.push(`last(${dafnyString(s)}, ${dafnyString(sub)})`);
      expected.push(s.lastIndexOf(sub));
      for (const p of [-1, 0, 1, 2, 10]) {
        calls.push(`lastAt(${dafnyString(s)}, ${dafnyString(sub)}, ${p})`);
        expected.push(s.lastIndexOf(sub, p));
      }
    }
  }
  const main = `\nmethod Main() {\n${calls.map(c => `  print ${c}, "\\n";`).join("\n")}\n}\n`;
  const run = dafny(["run", "--no-verify"], output + main);
  assert.equal(run.status, 0, run.output);
  const printed = run.output.trim().split("\n").slice(-calls.length).map(Number);
  assert.deepEqual(printed, expected);
});

test("Dafny's lastIndexOf postconditions state the match and that no later match exists", () => {
  const facts = `
lemma Found(s: string)
  requires last(s, ".") >= 0
  ensures s[last(s, ".")] == '.'
  ensures forall j :: last(s, ".") < j < |s| ==> s[j] != '.'
{
  var r := last(s, ".");
  assert StringMatchesAt(s, ".", r);
  assert s[r..r + 1][0] == s[r];
  forall j | r < j < |s| ensures s[j] != '.' {
    assert !StringMatchesAt(s, ".", j);
    assert s[j..j + 1][0] == s[j];
  }
}
lemma NotFound(s: string)
  requires last(s, ".") == -1
  ensures forall j :: 0 <= j < |s| ==> s[j] != '.'
{
  forall j | 0 <= j < |s| ensures s[j] != '.' {
    assert !StringMatchesAt(s, ".", j);
    assert s[j..j + 1][0] == s[j];
  }
}
`;
  const ok = verify(emitDafny() + facts);
  assert.equal(ok.status, 0, ok.output);
  const wrong = verify(emitDafny() + `\nlemma Wrong() ensures last("a.b", ".") == 0 {}\n`);
  assert.notEqual(wrong.status, 0, wrong.output);
  assert.match(wrong.output, /could not be proved|might not hold/);
});

test("Lean keeps rejecting string lastIndexOf", () => {
  const { typesFile, defFile } = transformModuleLean(sourceModule());
  resetLeanModule();
  assert.throws(() => emitLeanFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }),
    /Unsupported Lean method call: \.lastIndexOf\(\) on string/);
});
