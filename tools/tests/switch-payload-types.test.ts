import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import ts from "typescript";
import { Project, ScriptTarget } from "ts-morph";
import { DEFAULT_OPTIONS } from "../src/config.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const bodies = {
  explicitCase: `switch (bound.tag) {
    case "always": return false;
    case "until": return bound.value.day < cutoff;
  }`,
  defaultCase: `switch (bound.tag) {
    case "always": return false;
    default: return bound.value.day < cutoff;
  }`,
  ifElse: `if (bound.tag === "always") return false;
    else return bound.value.day < cutoff;`,
  ifThen: `if (bound.tag === "until") return bound.value.day < cutoff;
    return false;`,
  negatedIf: `if (bound.tag !== "always") return bound.value.day < cutoff;
    return false;`,
  reversedCheck: `if ("until" === bound.tag) return bound.value.day < cutoff;
    return false;`,
  negatedCheck: `if (!(bound.tag !== "until")) return bound.value.day < cutoff;
    return false;`,
  earlyReturn: `if (bound.tag === "always") return false;
    return bound.value.day < cutoff;`,
  negatedGuard: `if (bound.tag !== "until") return false;
    return bound.value.day < cutoff;`,
  conditional: `return bound.tag === "always" ? false : bound.value.day < cutoff;`,
  andGuard: `return bound.tag === "until" && bound.value.day < cutoff;`,
  orGuard: `return !(bound.tag === "always" || bound.value.day >= cutoff);`,
  whileGuard: `while (bound.tag === "until") {
      //@ done_with true
      return bound.value.day < cutoff;
    }
    return false;`,
  methodDefault: `let result = false;
    switch (bound.tag) {
      case "always": break;
      default: result = bound.value.day < cutoff; break;
    }
    return result;`,
};

function source(reverse = false): string {
  const variants = ['{ tag: "always"; value: boolean }', '{ tag: "until"; value: Deadline }'];
  if (reverse) variants.reverse();
  return `interface Deadline { day: string }
type Bound = ${variants.join(" | ")};
${Object.entries(bodies).map(([name, body]) => `
export function ${name}(bound: Bound, cutoff: string): boolean {
  //@ ensures bound.tag === "always" ==> !\\result
  //@ ensures bound.tag === "until" ==> \\result === (bound.value.day < cutoff)
  ${body}
}`).join("\n")}`;
}

function typed(text: string) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("/dispatch.ts", text);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return narrowModule(resolveModule(extractModule(file)));
}

function dafny(text: string): string {
  const { typesFile, defFile } = transformModuleDafny(typed(text));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dispatch.ts", {
    ...DEFAULT_OPTIONS, "string-semantics": "javascript-utf16", "dafny-library": "local",
  });
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-switch-payload-"));
  try {
    const path = join(dir, "dispatch.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--unicode-char:false", "--allow-deprecation", "--verification-time-limit=10", path],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function runtime(text: string): Record<string, (...args: any[]) => boolean> {
  const exports = {};
  const js = ts.transpileModule(text, { compilerOptions: {
    target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.CommonJS,
  } }).outputText;
  new Function("exports", js)(exports);
  return exports;
}

for (const reverse of [false, true]) {
  test(`all dispatch forms preserve string ordering with ${reverse ? "reversed" : "original"} union order`, () => {
    const text = source(reverse);
    for (const fn of Object.values(runtime(text))) {
      assert.equal(fn({ tag: "always", value: true }, "cutoff"), false);
      for (const [day, cutoff] of [["2026-09-04", "2026-09-05"], ["9", "10"], ["", "x"], ["x", "x"], ["\uD800", "\uD801"]]) {
        assert.equal(fn({ tag: "until", value: { day } }, cutoff), day < cutoff);
      }
    }
    const result = verify(dafny(text));
    assert.equal(result.status, 0, result.output);
  });
}

test("the false date-ordering contract is rejected for every dispatch form", () => {
  const text = source() + Object.keys(bodies).map(name => `
export function wrong_${name}(): boolean {
  //@ ensures !\\result
  return ${name}({ tag: "until", value: { day: "2026-09-04" } }, "2026-09-05");
}`).join("\n");
  const functions = runtime(text);
  for (const name of Object.keys(bodies)) assert.equal(functions[`wrong_${name}`](), true);
  const result = verify(dafny(text));
  assert.notEqual(result.status, 0, result.output);
  assert.equal((result.output.match(/a postcondition could not be proved/g) ?? []).length, Object.keys(bodies).length, result.output);
  assert.doesNotMatch(result.output, /resolution\/type errors|unresolved identifier|timed out/);
});

test("Lean binds the remaining variant's payload in pure and imperative defaults", () => {
  const { typesFile, defFile } = transformModuleLean(typed(source()));
  resetLeanModule();
  const output = emitLeanFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.match(output, /\.until _bound_value =>/);
  assert.match(output, /_bound_value\.day < cutoff/);
  assert.doesNotMatch(output, /\bbound\.value\b/);
});

test("array-union early returns preserve both outcomes of Array.isArray and typeof checks", () => {
  const guards = ["Array.isArray(items)", "!Array.isArray(items)", 'typeof items === "string"'];
  const text = guards.map((guard, i) => `
export function classify${i}(items: number[] | string): number {
  if (${guard}) return ${i === 0 ? 2 : 1};
  return ${i === 0 ? 1 : 2};
}
export function check${i}(): boolean {
  //@ ensures \\result
  return classify${i}("text") === 1 && classify${i}([]) === 2;
}`).join("\n");
  const functions = runtime(text);
  for (let i = 0; i < guards.length; i++) assert.equal(functions[`check${i}`](), true);
  const result = verify(dafny(text));
  assert.equal(result.status, 0, result.output);
});

test("a default covering multiple variants remains a catch-all", () => {
  const text = `type Choice = { tag: "a" } | { tag: "b" } | { tag: "c" };
export function other(value: Choice): boolean {
  //@ ensures \\result === (value.tag !== "a")
  switch (value.tag) { case "a": return false; default: return true; }
}`;
  const output = dafny(text);
  assert.match(output, /case _ =>/);
  const result = verify(output);
  assert.equal(result.status, 0, result.output);
});
