import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { DEFAULT_OPTIONS } from "../src/config.ts";
import * as sourceFns from "../fixtures/string-index.ts";

const source = readFileSync(new URL("../fixtures/string-index.ts", import.meta.url), "utf8");
const comparisonSource = ["===", "!==", "<", "<=", ">", ">="].map((op, k) => `
export function cmp${k}(s: string, t: string): boolean {
  //@ requires s.length > 0 && t.length > 0
  return s[0] ${op} t[0];
}`).join("\n");
const comparisonCases = [["a", "a"], ["a", "b"], ["b", "a"], ["é", "z"], ["\n", '"']].flatMap(([s, t]) => {
  const expected = [s[0] === t[0], s[0] !== t[0], s[0] < t[0], s[0] <= t[0], s[0] > t[0], s[0] >= t[0]];
  return expected.map((value, k) => ({ s, t, value, fn: `cmp${k}` }));
});

function resolved(text = source) {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("string-index.ts", text);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return narrowModule(resolveModule(extractModule(file)));
}

function dafny(text = source, utf16 = false) {
  const { typesFile, defFile } = transformModuleDafny(resolved(text));
  const mod = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny");
  return emitDafnyFile(mod, undefined, { ...DEFAULT_OPTIONS,
    "string-semantics": utf16 ? "javascript-utf16" : "unicode-scalar", "dafny-library": "local" });
}

function verify(text: string, utf16 = false, symbol?: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-string-index-"));
  try {
    const path = join(dir, "index.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=10",
      ...(symbol ? [`--filter-symbol=${symbol}`] : []),
      ...(utf16 ? ["--unicode-char:false", "--allow-deprecation"] : ["--unicode-char:true"]), path],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

test("string indexing resolves to strings through locals and optional chains", () => {
  const mod = resolved();
  const local = mod.functions.find(f => f.name === "doubledIndex")!.body[0];
  assert.equal(local.kind, "let");
  if (local.kind === "let") assert.equal(local.init.ty.kind, "string");
  const optional = mod.functions.find(f => f.name === "optionalFirst")!.body[0];
  assert.equal(optional.kind, "return");
  if (optional.kind === "return") assert.deepEqual(optional.value.ty, { kind: "optional", nullish: "undefined", inner: { kind: "string" } });
});

for (const utf16 of [false, true]) test(`string operations verify in ${utf16 ? "UTF-16" : "scalar"} mode`, () => {
  const output = dafny(source, utf16);
  assert.match(output, /\[s\[i\]\] == \[t\[j\]\]/);
  assert.match(output, /JSStringLt\(\[s\[i\]\], \[t\[j\]\]\)/);
  assert.match(output, /\(xs\[i\] == xs\[j\]\)/, "array comparisons retain native indexing");
  // Establish the singleton/slice identity before the recursive lexicographic
  // predicate is unfolded, as proof additions to the generated companion lemma.
  const proof = output.replace(/(lemma beforeElement_ensures[\s\S]*?\{\n)/, `$1  assert [s[i]] == s[i..i + 1];
  assert [t[j]] == t[j..j + 1];
`);
  const result = verify(proof + `
lemma IndexExamples()
  ensures firstIsA("abc") && !firstIsA("") && !firstIsA("b")
  ensures sameElement("ab", "ba", 0, 1) && !sameElement("ab", "ab", 0, 1)
  ensures beforeElement("ab", "ab", 0, 1) && !beforeElement("ab", "ab", 1, 0)
  ensures !matchesElement("ab", 0, "") && !matchesElement("ab", 0, "ab") && matchesElement("ab", 0, "a")
  ensures doubledIndex("ab", 1) == "bb" && indexLength("ab", 1) == 1
  ensures selectedFirst("a", "b", false) == "b"
  ensures nestedIndex("ab", 1) == "b" && arrayElement(["ab"], 0, 1) == "b"
{}
lemma IndexEquality(s: string, t: string, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |t|
  ensures sameElement(s, t, i, j) == (s[i] == t[j])
  ensures beforeElement(s, t, i, j) == (s[i] < t[j])
{
  assert JSStringLt("", "") == false;
  assert [s[i]][1..] == "" && [t[j]][1..] == "";
}
` + (utf16 ? `
lemma Surrogates()
  ensures stringAt("\\uD83D\\uDE00", 0) == "\\uD83D"
  ensures stringAt("\\uD83D\\uDE00", 1) == "\\uDE00"
  ensures !sameElement("\\uD83D\\uDE00", "\\uD83D\\uDE00", 0, 1)
{}
` : `
lemma Scalars()
  ensures stringAt("😀x", 0) == "😀" && stringAt("😀x", 1) == "x"
{}
`), utf16);
  assert.equal(result.status, 0, result.output);
});

test("Dafny retains bounds obligations and rejects a wrong indexed comparison", () => {
  const unchecked = verify(dafny("export function unchecked(s: string, i: number): string { return s[i]; }"));
  assert.notEqual(unchecked.status, 0, unchecked.output);
  assert.match(unchecked.output, /index out of range/);
  const wrong = verify(dafny(source.replace("return s[i] === t[j];", "return s[i] !== t[j];")), false, "sameElement_ensures");
  assert.notEqual(wrong.status, 0, wrong.output);
  assert.match(wrong.output, /postcondition could not be proved/);
});

test("all indexed comparison operators agree with JavaScript", () => {
  const clauses = comparisonCases.map(({ s, t, value, fn }) =>
    `  ensures ${fn}(${JSON.stringify(s)}, ${JSON.stringify(t)}) == ${value}`);
  const result = verify(dafny(comparisonSource) + `\nlemma Comparisons()\n${clauses.join("\n")}\n{}\n`);
  assert.equal(result.status, 0, result.output);
  assert.equal(sourceFns.sameElement("ab", "ba", 0, 1), true);
  assert.equal(sourceFns.sameElement("ab", "ab", 0, 1), false);
  assert.equal(sourceFns.firstIsA(""), false);
});

function leanPure() {
  const { typesFile, defFile } = transformModuleLean(resolved(source + comparisonSource));
  resetLeanModule();
  // Compile the emitted pure mirrors with Lean core and the real string helper;
  // this focused test does not need a Lake/Velvet installation.
  return emitLeanFile({ comment: "", imports: [], options: [],
    decls: [...(typesFile?.decls ?? []), ...defFile.decls].filter(d => d.kind === "namespace") });
}

test("Lean emits string indexing through its scalar helper", () => {
  const output = leanPure();
  assert.match(output, /import LemmaScript.JSString/);
  assert.match(output, /JSString.index \(s\) \(i\)/);
  assert.doesNotMatch(output, /Unknown|\bs\[i\]/);
});

const leanProbe = spawnSync("lean", ["--version"], { encoding: "utf8", timeout: 10_000 });
test("Lean proves emitted string-index examples and index-to-index equivalence", { skip: leanProbe.status !== 0 }, () => {
  const dir = mkdtempSync(join(tmpdir(), "lsc-string-index-lean-"));
  try {
    mkdirSync(join(dir, "LemmaScript"));
    writeFileSync(join(dir, "LemmaScript", "JSString.lean"), readFileSync(new URL("../../LemmaScript/JSString.lean", import.meta.url)));
    const env = { ...process.env, LEAN_PATH: dir };
    const helper = spawnSync("lean", ["--root", dir, "-o", join(dir, "LemmaScript", "JSString.olean"),
      join(dir, "LemmaScript", "JSString.lean")], { env, encoding: "utf8", timeout: 30_000 });
    assert.ifError(helper.error);
    assert.equal(helper.status, 0, helper.stdout + helper.stderr);
    const path = join(dir, "Index.lean");
    writeFileSync(path, leanPure() + `
example : Pure.firstIsA "abc" = true := by decide
example : Pure.firstIsA "" = false := by decide
example : Pure.sameElement "ab" "ba" 0 1 = true := by decide
example : Pure.sameElement "ab" "ab" 0 1 = false := by decide
example : Pure.agreesAt "ab" "ba" 0 1 true = true := by decide
example : Pure.agreesAt "ab" "ab" 0 1 true = false := by decide
example : Pure.beforeElement "ab" "ab" 0 1 = true := by decide
example : Pure.beforeElement "ab" "ab" 1 0 = false := by decide
example : Pure.matchesElement "ab" 0 "" = false := by decide
example : Pure.matchesElement "ab" 0 "ab" = false := by decide
example : Pure.doubledIndex "ab" 1 = "bb" := by decide
example : Pure.indexLength "ab" 1 = 1 := by decide
example : Pure.optionalFirst none = none := by decide
example : Pure.optionalFirst (some "ab") = some "a" := by decide
example : Pure.selectedFirst "a" "b" false = "b" := by decide
example : Pure.nestedIndex "ab" 1 = "b" := by decide
example : Pure.arrayElement #["ab"] 0 1 = "b" := by decide
example : Pure.stringAt "😀x" 0 = "😀" := by decide
example : Pure.stringAt "😀x" 1 = "x" := by decide
example (s t : String) (i j : Int) :
    (JSString.index s i = JSString.index t j) ↔ (s.toList[i.toNat]! = t.toList[j.toNat]!) := by
  simp [JSString.index, String.singleton_inj]
` + comparisonCases.map(({ s, t, value, fn }) =>
      `example : Pure.${fn} ${JSON.stringify(s)} ${JSON.stringify(t)} = ${value} := by decide\n`).join(""));
    const result = spawnSync("lean", ["--root", dir, path], { env, encoding: "utf8", timeout: 30_000 });
    assert.ifError(result.error);
    assert.equal(result.status, 0, result.stdout + result.stderr);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
