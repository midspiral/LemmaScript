import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { DEFAULT_OPTIONS } from "../src/config.ts";
import { peepholeModule } from "../src/peephole.ts";
import * as runtime from "../fixtures/callback-arguments.ts";

function raw(source?: string) {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = source === undefined
    ? project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/callback-arguments.ts", import.meta.url)))
    : project.createSourceFile("callbacks.ts", source);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return extractModule(file);
}

function generate(source?: string, backend: "dafny" | "lean" = "dafny", library: "stdlib" | "local" = "stdlib") {
  const module = narrowModule(resolveModule(raw(source)));
  const { typesFile, defFile } = (backend === "dafny" ? transformModuleDafny : transformModuleLean)(module);
  const output = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, backend);
  resetLeanModule();
  return backend === "dafny" ? emitDafnyFile(output, undefined, { ...DEFAULT_OPTIONS, "dafny-library": library }) : emitLeanFile(output);
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-callbacks-"));
  try {
    const path = join(dir, "callbacks.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--standard-libraries", "--verification-time-limit=15", path],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

test("callback observations agree with JavaScript", () => {
  for (const [name, expected] of Object.entries({ restCount: [3], tailCount: [2], unusedRestOnly: [42],
    indexedMap: [7, 8], restIndex: [0, 1], sourceArgument: [7, 8], indexedSome: true,
    indexedEvery: true, indexedFilter: [7, 9], indexedFind: 8, indexedFindIndex: 1,
    indexedReduce: 9, reduceRestCount: 6, nestedShadow: [2], nestedCapture: [2], unusedPositional: [8] })) {
    assert.deepEqual((runtime[name as keyof typeof runtime] as () => unknown)(), expected, name);
  }
  assert.equal(runtime.capturedIndex(1), false);
  assert.deepEqual(runtime.unusedRest([1, 2]), [2, 3]);
});

test("extraction preserves rest binding operations", () => {
  const module = raw("export function f(xs: number[]) { return xs.map((x, ...rest: [number, number[]]) => x); }");
  const ret = module.functions[0].body[0];
  assert.ok(ret.kind === "return" && ret.value.kind === "call");
  const callback = ret.value.args[0];
  assert.ok(callback.kind === "lambda");
  assert.equal(callback.params[1].rest, true);
});

test("defaults retain their lexical scope and effectful callees", () => {
  const module = raw(`export function f(i: number): number[] {
    for (let i = 0; i < 1; i++) {
      return [7].map((value, index, source, extra = i) => extra);
    }
    return [];
  }`);
  const counter = module.functions[0].body[0];
  assert.ok(counter.kind === "let" && counter.name !== "i");
  const loop = module.functions[0].body[1];
  assert.ok(loop.kind === "while");
  const ret = loop.body[0];
  assert.ok(ret.kind === "return" && ret.value.kind === "call");
  const callback = ret.value.args[0];
  assert.ok(callback.kind === "lambda");
  assert.deepEqual(callback.params[3].defaultValue, { kind: "var", name: counter.name });
  const resolved = resolveModule(raw(`
    function next(): number { let value = 0; value += 1; return value; }
    export function f(): number[] { return [7].map((value, index, source, extra = next()) => value); }
  `));
  assert.equal(resolved.functions.find(f => f.name === "f")?.isPure, false);
});

for (const library of ["stdlib", "local"] as const) test(`Dafny proves the actual callback behavior with ${library} helpers`, () => {
  // An ordinary witness assertion in the proof companion, without changing
  // the generated quantifier or choosing a trigger for users' predicates.
  const proof = generate(undefined, "dafny", library).replace(/(lemma indexedSome_ensures\(\)[\s\S]*?\{)\n/,
    "$1\n  assert 1 in CallbackIndices(2);\n");
  const result = verify(proof);
  assert.equal(result.status, 0, result.output);
});

test("empty indexed callbacks preserve empty-array behavior", () => {
  const result = verify(generate(`
    export function f(): boolean {
      //@ ensures \\result === false
      return ([] as number[]).some((value, index) => index === 0);
    }
    export function g(): number[] {
      //@ ensures \\result.length === 0
      return ([] as number[]).map((value, index) => index);
    }
  `));
  assert.equal(result.status, 0, result.output);
});

test("a computed receiver is evaluated once outside callback parameter scope", () => {
  const output = generate(`
    function makeItems(): number[] { let n = 6; n += 1; return [n]; }
    export function f(_callbackSource0: number): number[] {
      return makeItems().map((_callbackSource0, index, source) => source[index]);
    }
  `);
  assert.equal((output.match(/:= makeItems\(\)/g) ?? []).length, 1, output);
  const result = verify(output);
  assert.equal(result.status, 0, result.output);
});

test("defaults that execute retain obligations even when their value is unused", () => {
  const helper = `function unavailable(): number {
    //@ requires false
    return 0;
  }`;
  const ignored = verify(generate(`${helper}
    export function f(): number[] { return [7].map((value = unavailable()) => value); }
  `));
  assert.equal(ignored.status, 0, ignored.output);
  const executed = verify(generate(`${helper}
    export function f(): number[] {
      return [7].map((value, index, source, extra = unavailable()) => value);
    }
  `));
  assert.notEqual(executed.status, 0, executed.output);
  assert.match(executed.output, /precondition/);
  assert.throws(() => generate(`${helper}
    export function f(xs: unknown[]): number[] { return xs.map((value = unavailable()) => 1); }
  `), /callback default.*known argument type/);
  const aliased = verify(generate(`${helper}
    type Missing = undefined;
    export function f(xs: Missing[]): number[] { return xs.map((value: number | undefined = unavailable()) => 1); }
  `));
  assert.notEqual(aliased.status, 0, aliased.output);
  assert.match(aliased.output, /precondition/);
});

test("rest-pack mutation cannot leave subsequent observations unchanged", () => {
  assert.throws(() => generate(`export function f(): number[] {
    return [7].map((value, ...rest: (number | number[])[]) => { rest.push(9); return rest.length; });
  }`), /cannot materialize callback rest/);
});

test("Dafny rejects the formerly provable false rest and index postconditions", () => {
  for (const source of [
    `export function f(): number[] {
      //@ ensures \\result[0] === 1
      return [[7]].map((...args: (number | number[] | number[][])[]) => args.length);
    }`,
    `export function f(index: number): boolean {
      //@ requires index === 1
      //@ ensures \\result === true
      return [7].some((value, index) => index === 1);
    }`,
  ]) {
    const result = verify(generate(source));
    assert.notEqual(result.status, 0, result.output);
    assert.match(result.output, /postcondition could not be proved/);
  }
});

test("returning the rest pack cannot masquerade as an ordinary parameter", () => {
  assert.throws(() => generate(`export function f(): number[] {
    return [[7]].map((...args: (number | number[] | number[][])[]) => args).map(row => row.length);
  }`), /cannot materialize callback rest/);
});

test("unused rest and positional bindings preserve unary output on both backends", () => {
  for (const backend of ["dafny", "lean"] as const) {
    const plain = generate("export function f(xs: number[]): number[] { return xs.map(value => value + 1); }", backend);
    for (const parameters of ["value, ...rest: [number, number[]]", "value, index, source"]) {
      const output = generate(`export function f(xs: number[]): number[] { return xs.map((${parameters}) => value + 1); }`, backend);
      assert.equal(output, plain);
    }
  }
});

test("Lean uses the same argument binding and indexed iteration", () => {
  // findIndex has no Lean lowering; exercise the supported collection surface.
  const output = generate(`export function f(xs: number[]): number[] {
    return xs.map((value, ...rest: [number, number[]]) => value + rest[0] + rest[1].length);
  }`, "lean");
  assert.match(output, /Array.range/);
  assert.doesNotMatch(output, /\brest\b/);
});
