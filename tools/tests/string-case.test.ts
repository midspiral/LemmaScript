import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
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

const source = `
export function upper(s: string): string { return s.toUpperCase(); }
export function lower(s: string): string { return s.toLowerCase(); }
`;

function emitDafny(utf16: boolean): string {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("case.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(file))));
  const mod = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny");
  return emitDafnyFile(mod, undefined, { ...DEFAULT_OPTIONS,
    "string-semantics": utf16 ? "javascript-utf16" : "unicode-scalar", "dafny-library": "local" });
}

function verify(text: string, utf16: boolean) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-string-case-"));
  try {
    const path = join(dir, "case.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=60",
      ...(utf16 ? ["--unicode-char:false", "--allow-deprecation"] : ["--unicode-char:true"]), path],
      { encoding: "utf8", timeout: 180_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

/** A Dafny sequence of the string's elements, written as character codes. */
const chars = (s: string) => "[" + Array.from(s, c => `(${c.charCodeAt(0)} as char)`).join(", ") + "]";

/** Claims JavaScript refutes: `"ß".toUpperCase()` is `"SS"`, `"Ä".toLowerCase()` is `"ä"`. */
const refuted = [
  "lemma UpperKeepsLength(s: string) ensures |upper(s)| == |s| {}",
  "lemma LowerKeepsLength(s: string) ensures |lower(s)| == |s| {}",
  `lemma SharpSStaysOneChar() ensures |upper(${chars("ß")})| == 1 {}`,
  `lemma LowerFixesUmlaut() ensures lower(${chars("Ä")}) == ${chars("Ä")} {}`,
];

function everyAsciiCharMatchesJavaScript(): string {
  const facts = Array.from({ length: 128 }, (_, n) => String.fromCharCode(n)).flatMap(c => [
    `  ensures upper(${chars(c)}) == ${chars(c.toUpperCase())}`,
    `  ensures lower(${chars(c)}) == ${chars(c.toLowerCase())}`,
  ]);
  return `\nlemma EveryAsciiChar()\n${facts.join("\n")}\n{}\n`;
}

const asciiFacts = `
lemma AsciiKeepsLength(s: string)
  requires forall i :: 0 <= i < |s| ==> (s[i] as int) < 128
  ensures |upper(s)| == |s| && |lower(s)| == |s|
{}
lemma Deterministic(a: string, b: string) requires a == b ensures lower(a) == lower(b) {}
`;

for (const utf16 of [false, true]) {
  const mode = utf16 ? "UTF-16" : "scalar";

  test(`${mode}: case conversion admits no claim JavaScript refutes (#312)`, () => {
    const generated = emitDafny(utf16);
    for (const claim of refuted) {
      const result = verify(generated + "\n" + claim + "\n", utf16);
      assert.notEqual(result.status, 0, `${claim}\n${result.output}`);
      assert.match(result.output, /could not be proved|might not hold/, result.output);
    }
  });

  test(`${mode}: ASCII input gets JavaScript's case mapping`, () => {
    const result = verify(emitDafny(utf16) + asciiFacts + everyAsciiCharMatchesJavaScript(), utf16);
    assert.equal(result.status, 0, result.output);
  });
}
