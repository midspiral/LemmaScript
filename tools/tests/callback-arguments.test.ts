import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget, ts } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { DEFAULT_OPTIONS } from "../src/config.ts";
import { peepholeModule } from "../src/peephole.ts";
import * as runtime from "../../examples/callbackArguments.ts";

function raw(source?: string) {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = source === undefined
    ? project.addSourceFileAtPath(fileURLToPath(new URL("../../examples/callbackArguments.ts", import.meta.url)))
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

function execute(source: string, ...args: unknown[]): unknown {
  const { outputText } = ts.transpileModule(source, { compilerOptions: {
    target: ts.ScriptTarget.ESNext, module: ts.ModuleKind.CommonJS,
  } });
  const exports: { f?: (...args: unknown[]) => unknown } = {};
  new Function("exports", outputText)(exports);
  return exports.f!(...args);
}

test("callback observations agree with JavaScript", () => {
  for (const [name, expected] of Object.entries({ restCount: [3], tailCount: [2], unusedRestOnly: [42],
    indexedMap: [7, 8], restIndex: [0, 1], sourceArgument: [7, 8], indexedSome: true, defaultFromIndex: [0, 1],
    indexedEvery: true, indexedFilter: [7, 9], indexedFind: 8, indexedFindIndex: 1,
    indexedReduce: 9, reduceRestCount: 6, nestedShadow: [2], nestedCapture: [2], unusedPositional: [8] })) {
    assert.deepEqual((runtime[name as keyof typeof runtime] as () => unknown)(), expected, name);
  }
  assert.equal(runtime.capturedIndex(1), false);
  assert.deepEqual(runtime.unusedRest([1, 2]), [2, 3]);
  assert.deepEqual(runtime.laterDefaultCapture(3), [9]);
});

test("a default closure captures the later parameter, not its outer namesake", () => {
  const source = `export function f(extra: number): number[] {
    //@ requires extra === 3
    //@ ensures \\result[0] === 9
    return [7].map((value, index, source, read = (unused: number) => extra, extra = 9) => read(0));
  }`;
  assert.deepEqual(execute(source, 3), [9]);
  const correct = verify(generate(source));
  assert.equal(correct.status, 0, correct.output);
  const incorrect = verify(generate(source.replace("result[0] === 9", "result[0] === 3")));
  assert.notEqual(incorrect.status, 0, incorrect.output);
  assert.match(incorrect.output, /postcondition could not be proved/);
});

test("default closures compose through dependencies, rest observations, and lexical shadowing", () => {
  const cases: [string, number][] = [
    ["(value, index, source, read = (n: number) => extra, extra = 9, result = read(0)) => result", 9],
    ["(value, index, source, read = (n: number) => next(n), next = (n: number) => value + n) => read(1)", 8],
    ["(value, index, source, read = (n: number) => [5].map(extra => extra + 1)[0], extra = 9) => read(0)", 6],
    ["(value, index, source, read = (n: number) => rest.length, ...rest: number[]) => read(0)", 0],
    ["(value, index, source, read = (n: number) => extra) => { const extra = 9; return read(0); }", 3],
    ["(value, index, source, read = (n: number) => extra === undefined ? 0 : extra, extra = value > 0 ? value : undefined) => read(0)", 7],
    ["(value, index, source, read = (n: number) => { if (extra === undefined) return 0; return extra; }, extra = value > 0 ? value : undefined) => read(0)", 7],
  ];
  const sources = cases.map(([callback, expected], i) => {
    const source = `export function f(extra: number): number[] {
      //@ requires extra === 3
      //@ ensures \\result[0] === ${expected}
      return [7].map(${callback});
    }`;
    assert.deepEqual(execute(source, 3), [expected], callback);
    return source.replace("function f(", `function f${i}(`);
  });
  const result = verify(generate(sources.join("\n")));
  assert.equal(result.status, 0, result.output);
});

test("a callback function binding shadows module call metadata", () => {
  const source = `function read(n: number, extra?: number): number { return 3; }
    export function f(): number[] {
      //@ ensures \\result[0] === 9
      return [7].map((value, index, source, read = (n: number) => extra, extra = 9) => read(0));
    }`;
  assert.deepEqual(execute(source), [9]);
  const result = verify(generate(source));
  assert.equal(result.status, 0, result.output);
  const lean = generate(source, "lean");
  assert.doesNotMatch(lean.slice(lean.indexOf("def f "), lean.indexOf("end Pure")), /Pure\.read/);
});

test("a default closure can capture a later supplied argument", () => {
  const source = `export function f(xs: undefined[]): number[] {
    //@ requires xs.length === 1
    //@ ensures \\result[0] === 0
    return xs.map((read: ((n: number) => number) | undefined = (n: number) => index, index) => read(0));
  }`;
  assert.deepEqual(execute(source, [undefined]), [0]);
  const result = verify(generate(source));
  assert.equal(result.status, 0, result.output);
});

test("calls in defaults cannot read a later binding before it is initialized", () => {
  for (const parameters of [
    "read = (n: number) => extra, result = read(0), extra = 9",
    "result = invoke((n: number) => extra), extra = 9",
    "result = [1].map(n => extra)[0], extra = 9",
    "result = invoke((n: number) => rest.length), ...rest: number[]",
  ]) {
    const source = `function invoke(read: (n: number) => number): number { return read(0); }
      export function f(extra: number): number[] {
        return [7].map((value, index, source, ${parameters}) => result);
      }`;
    assert.throws(() => execute(source, 3), ReferenceError);
    // No front-end policy rejection: ordinary lowering retains the reference
    // and the backend diagnoses its unavailable binding.
    const result = verify(generate(source));
    assert.notEqual(result.status, 0, result.output);
    assert.match(result.output, /unresolved identifier: i_callbackParam/);
  }
});

test("passing a default closure before its captures are initialized remains a backend limitation", () => {
  const source = `type Reader = (n: number) => number;
    function identity(read: Reader): Reader { return read; }
    function invoke(read: (n: number) => number): number { return read(0); }
    export function f(extra: number): number[] {
      //@ requires extra === 3
      //@ ensures \\result[0] === 9
      return [7].map((value, index, source, read = (n: number) => extra,
        saved = identity(read), extra = 9) => invoke(saved));
    }`;
  // JavaScript can pass the closure without reading extra. Immutable backend
  // closures cannot be constructed yet; do not move the identity call to hide it.
  assert.deepEqual(execute(source, 3), [9]);
  const result = verify(generate(source));
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /unresolved identifier: i_callbackParam/);
  const afterInitialization = source.replace("saved = identity(read), extra = 9", "extra = 9, saved = identity(read)");
  assert.deepEqual(execute(afterInitialization, 3), [9]);
  // Function-level proof additions expose the helpers' bodies to their caller.
  const proof = generate(afterInitialization)
    .replace(/(function identity\(read: Reader\): Reader\n)/, "$1  ensures identity(read) == read\n")
    .replace(/(function invoke\(read: \(int\) -> int\): int\n)/, "$1  ensures invoke(read) == read(0)\n")
    .replace(/(lemma f_ensures[\s\S]*?\{\n)/, "$1  var read := (n: int) => 9;\n"
      + "  assert identity(read) == read;\n  assert invoke(identity(read)) == 9;\n"
      + "  assert f(extra)[0] == invoke(identity(read));\n");
  const supported = verify(proof);
  assert.equal(supported.status, 0, supported.output);
});

test("constant folding cannot erase an uninitialized parameter read", () => {
  const source = `function invoke(read: (n: number) => boolean): boolean { return read(0); }
    export function f(extra: number[]): boolean[] {
      return [7].map((value, index, source, result = invoke((n: number) => !extra), extra = [9]) => result);
    }`;
  assert.throws(() => execute(source, []), ReferenceError);
  const result = verify(generate(source));
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /unresolved identifier: i_callbackParam/);
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
