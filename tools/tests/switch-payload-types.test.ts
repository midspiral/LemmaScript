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

test("optional-chain early returns preserve undefined === undefined and still narrow concrete user types", () => {
  const text = `type Status = "open" | "closed";
interface Box { value: number }
interface Item { status: Status; value: number }

export function single(box: Box | undefined, other: number | undefined): boolean {
  if (box?.value !== other) return false;
  return box === undefined;
}
export function compound(box: Box | undefined, other: number | undefined, flag: boolean): boolean {
  if (box?.value !== other || flag) return false;
  return box === undefined;
}
export function enumGuard(item: Item | undefined): number {
  if (item?.status !== "open") return 0;
  return item.value;
}
export function enumOrGuard(item: Item | undefined, flag: boolean): number {
  if (item?.status !== "open" || flag) return 0;
  return item.value;
}
export function check(): boolean {
  //@ ensures \\result
  return single(undefined, undefined) && compound(undefined, undefined, false) &&
    !single({ value: 1 }, 1) && !single(undefined, 1) && !compound(undefined, undefined, true) &&
    enumGuard({ status: "open", value: 7 }) === 7 && enumGuard(undefined) === 0 &&
    enumOrGuard({ status: "open", value: 9 }, false) === 9 && enumOrGuard(undefined, false) === 0;
}`;
  const fns = runtime(text);
  assert.equal(fns.check(), true);
  // Concrete user types (including coerced string-union literals) still narrow.
  const narrowed = typed(text);
  assert.equal(narrowed.functions.find(f => f.name === "enumGuard")!.body[0].kind, "someMatch");
  assert.equal(narrowed.functions.find(f => f.name === "enumOrGuard")!.body[0].kind, "someMatch");
  // Nullable RHS must NOT rewrite to an unconditional `None => return false`.
  assert.equal(narrowed.functions.find(f => f.name === "single")!.body[0].kind, "if");
  assert.equal(narrowed.functions.find(f => f.name === "compound")!.body[0].kind, "if");
  const result = verify(dafny(text));
  assert.equal(result.status, 0, result.output);
  const wrong = verify(dafny(text.replace("//@ ensures \\result\n", "//@ ensures !\\result\n")));
  assert.notEqual(wrong.status, 0, wrong.output);
  assert.match(wrong.output, /a postcondition could not be proved/);

  // Unconstrained type parameter T may be instantiated with undefined, so
  // `box?.value !== other` must not narrow `box` as present on fallthrough.
  const genericText = `interface GenBox<T> { value: T }
export function generic<T>(box: GenBox<T> | undefined, other: T): boolean {
  if (box?.value !== other) return false;
  return box === undefined;
}`;
  assert.equal(runtime(genericText).generic(undefined, undefined), true);
  const genFn = typed(genericText).functions.find(f => f.name === "generic")!;
  assert.equal(genFn.body[0].kind, "if");
});
