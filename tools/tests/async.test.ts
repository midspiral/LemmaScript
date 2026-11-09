import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { autoHavocModule } from "../src/autohavoc.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { lowerAsyncModule } from "../src/async-lower.ts";
import * as native from "../fixtures/async-functions.ts";

function extract(source: string) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [],
  } });
  return extractModule(project.createSourceFile("/async.ts", source + "\nexport {};"));
}
function typed(source: string) { return autoHavocModule(narrowModule(resolveModule(extract(source)))); }
function emit(source: string) {
  const { typesFile, defFile } = transformModuleDafny(typed(source));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

test("async without await keeps its promise and allocates a result handle", () => {
  const source = "export async function value(): Promise<bigint> { return 1n; }";
  const raw = extract(source);
  assert.equal(raw.functions[0].isAsync, true);
  assert.equal(raw.functions[0].returnType, "Promise<bigint>");
  assert.equal(typed(source).functions[0].returnTy.kind, "promise");
  const output = emit(source);
  assert.match(output, /method f0_value_start/);
  assert.match(output, /result.id == \|s.outcomes\|/);
  assert.match(output, /Finished\(Fulfilled\(BigIntValue\(1\)\)\)/);
});

test("the inline handler example supports synchronous autohavoc and rejects async erasure", () => {
  const source = readFileSync(new URL("../../examples/inlineHandler.ts", import.meta.url), "utf8");
  const output = emit(source);
  assert.match(output, /method get_entries\(/);
  assert.match(output, /var contents := readSafe\(filePath\);/);
  const asyncSource = source.replace('app.get("/entries", (', 'app.get("/entries", async (');
  assert.throws(() => emit(asyncSource), /async get_entries: autohavoc cannot abstract/);
});

test("await of undefined still registers a continuation", () => {
  const output = emit("async function wait(): Promise<void> { await undefined; }");
  assert.match(output, /Create\(Fulfilled\(UndefinedValue\)/);
  assert.match(output, /Suspend\(v0,/);
});

test("async contracts describe fulfillment values, while native parameters are explicit", () => {
  const source = `async function nonnegative(p: Promise<bigint>): Promise<bigint> {
    //@ native p
    //@ ensures \\result >= 0n
    const x = await p;
    return x > 0n ? x : 0n;
  }`;
  const output = emit(source);
  assert.match(output, /value\.bigint >= 0/);
  assert.match(output, /p0\.accepts\(o\) && o\.Fulfilled\? ==> o\.value\.BigIntValue\?/);
  assert.throws(() => emit(source.replace("//@ native p", "")), /add \/\/@ native p/);
});

test("throws and handlers survive extraction instead of becoming unreachable paths", () => {
  const source = `async function recover(): Promise<bigint> {
    try { throw 0n; } catch (e) { return e === 0n ? 1n : 2n; }
  }`;
  const raw = extract(source).functions[0].body[0];
  assert.equal(raw.kind, "try");
  if (raw.kind !== "try") return;
  assert.deepEqual(raw.body[0], { kind: "throw", value: { kind: "bigint", value: "0" }, line: 2 });
  const output = emit(source);
  assert.match(output, /var v0: int := 0/);
  assert.match(output, /Finished\(Fulfilled\(BigIntValue\(1\)\)\)/);
});

test("return p adopts outside its catch, while return await p enters the catch", () => {
  const template = `async function f(p: Promise<bigint>): Promise<bigint> {
    //@ native p
    try { return EXPR; } catch { return 7n; }
  }`;
  const adopted = lowerAsyncModule(typed(template.replace("EXPR", "p")), "dafny").async!.functions[0].body;
  const awaited = lowerAsyncModule(typed(template.replace("EXPR", "await p")), "dafny").async!.functions[0].body;
  assert.equal(adopted.kind, "adopt");
  assert.equal(awaited.kind, "wait");
  if (awaited.kind === "wait") assert.deepEqual(awaited.rejected, {
    kind: "done", rejected: false, value: { kind: "bigint", value: "7", ty: { kind: "int", big: true } },
  });
});

for (const [description, source, error] of [
  ["shared state", `async function f(s: { count: bigint }) { const n = s.count; await undefined; return s.count === n; }`, /shared-state/],
  ["callback effects", `async function f(cb: () => bigint) { return cb(); }`, /shared-state|callback/],
  ["async loops", `async function f(n: bigint) { while (n > 0n) { await undefined; n -= 1n; } }`, /while is not supported/],
  ["recursive calls", `async function f(n: bigint): Promise<bigint> { return n === 0n ? 0n : await f(n - 1n); }`, /recursive async calls/],
  ["type erasure", `async function f(p: Promise<bigint>) {\n //@ type p bigint\n return await p; }`, /type overrides/],
  ["type assertions", `async function f() { return 1 as unknown as bigint; }`, /type assertions/],
  ["manual havoc", `async function f() {\n //@ havoc\n const x = await Promise.resolve(1n); return x; }`, /havoc/],
  ["skipped effects", `async function f() { let n = 0n;\n //@ skip\n n = 1n; return n; }`, /skip/],
  ["autohavoc", `//@ autohavoc\nasync function f() { await undefined; }`, /autohavoc/],
  ["shadowing", `async function f(n: bigint) { if (n > 0n) { let n = 1n; return n; } return n; }`, /shadowed binding/],
  ["destructuring", `async function f({ n }: { n: bigint }) { return n; }`, /simple binding/],
  ["local destructuring", `async function f() { const {} = await Promise.resolve(1n); }`, /simple bindings/],
  ["uninitialized locals", `async function f() { let n!: bigint; return n; }`, /explicit initializers/],
  ["synchronous promise calls", `async function f() { return 1n; }\nfunction g() { f(); }`, /synchronous promise APIs/],
  ["structural thenables", `async function f(p: PromiseLike<bigint>) { return await p; }`, /shared-state\/thenable/],
] as const) {
  test(`async rejects ${description} explicitly`, () => assert.throws(() => emit(source), error));
}

test("an object named Promise is not mistaken for the native constructor", () => {
  const source = `const Promise = { resolve(n: bigint) { return n; } };
    async function f() { return await Promise.resolve(1n); }`;
  const raw = extract(source);
  assert.doesNotMatch(JSON.stringify(raw.functions[0].body), /"kind":"promise"/);
  assert.throws(() => emit(source), /calls must target/);
});

test("Lean refuses async even when there is no await", () => {
  assert.throws(() => transformModuleLean(typed("async function f() { return 1n; }")), /use --backend=dafny/);
});

test("a caught value may be a promise: it cannot be resolved or compared as an ordinary scalar", async () => {
  const source = (body: string) => `async function f(p: Promise<void>): Promise<boolean> {
    //@ native p
    //@ ensures !\\result
    try { await p; return false; } catch (e) { ${body} }
  }`;
  assert.throws(() => emit(source("return Promise.resolve(e) === e;")), /may assimilate a thenable/);
  assert.throws(() => emit(source("return e === p;")), /may hide a promise identity/);
  const promised = Promise.resolve();
  async function actual(p: Promise<void>) {
    try { await p; return false; } catch (e) { return Promise.resolve(e) === e; }
  }
  assert.equal(await actual(Promise.reject(promised)), true, "the previously accepted false contract has a native counterexample");
});

test("block and catch bindings cannot escape into references to globals", () => {
  assert.throws(() => emit(`const x = 1n;
    async function f(): Promise<bigint> {
      //@ ensures \\result === 2n
      if (true) { const x = 2n; }
      return x;
    }`), /shadowed binding 'x'/);
  assert.throws(() => emit(`const error = 1n;
    async function f(): Promise<bigint> {
      try { throw 0n; } catch (error) {}
      return error;
    }`), /shadowed binding 'error'/);
});

test("a catch binding cannot redirect a selected async call", () => {
  assert.throws(() => emit(`async function selected(): Promise<bigint> { return 0n; }
    async function f(p: Promise<void>): Promise<bigint> {
      //@ native p
      try { await p; return 0n; } catch (selected: any) { return await selected(); }
    }`), /call to shadowed binding 'selected'/);
});

test("shadowed undefined cannot become the undefined literal", () => {
  assert.throws(() => emit("async function f(undefined: bigint) { return undefined === 0n; }"), /shadowed undefined/);
  assert.throws(() => emit("const undefined = 0n; async function f() { return undefined === 0n; }"), /shadowed undefined/);
});

test("global constant initializers keep global scope when parameters shadow their dependencies", () => {
  const output = emit(`const base = 3n; const offset = base + 1n;
    async function f(base: bigint): Promise<bigint> {
      //@ ensures \\result === 4n
      await undefined;
      return offset;
    }`);
  assert.match(output, /Finished\(Fulfilled\(BigIntValue\(\(3 \+ 1\)\)\)\)/);
});

test("captured constants cannot hide erased runtime types or shadowed undefined", () => {
  assert.throws(() => emit(`const disguised = 0n as unknown as number;
    async function f(): Promise<boolean> {
      //@ ensures \\result
      return disguised === 0;
    }`), /type assertions in captured constants/);
  assert.throws(() => emit(`const disguised = 0n as unknown as number;
    const alias = disguised + 1;
    async function f() { return alias; }`), /type assertions in captured constants/);
  assert.throws(() => emit(`const undefined = 0n; const alias = undefined;
    async function f() { return alias; }`), /shadowed undefined/);
});

test("autohavoc cannot erase an async operation nested in an opaque call", () => {
  for (const expression of ["selected()", "Promise.resolve(1n)"]) {
    const mod = resolveModule(extract(`function opaque(x: unknown): any { return x; }
      async function selected() { return 1n; }
      function f() { opaque(${expression}); }`));
    mod.functions.find(f => f.name === "f")!.autohavoc = true;
    assert.throws(() => autoHavocModule(mod), /autohavoc cannot abstract/);
  }
});

test("the verified sources run with native promises, including falsy rejection reasons", async () => {
  assert.equal(await native.twice(10n), 12n);
  assert.equal(await native.repeated(10n), 22n);
  assert.equal(await native.recover(), 7n);
  assert.equal(await native.returnBeforeFinally(), 1n);
  assert.equal(await native.finallyOverrides(), 5n);
  assert.equal(await native.shortCircuit(false), false);
  assert.equal(await native.shortCircuit(true), true);
  await assert.rejects(native.adoptWithoutCatch(), reason => reason === 0n);
  await assert.rejects(native.rethrow(), reason => reason === undefined);
  const p = Promise.resolve(-3n);
  const a = native.absolute(p), b = native.absolute(p);
  assert.notEqual(a, b);
  assert.notEqual(a, p);
  assert.deepEqual(await Promise.all([a, b]), [3n, 3n]);
});

test("native await and adoption take different numbers of microtasks", async () => {
  let yielded = false, adopted = false;
  native.yieldPlain(1n).then(() => { yielded = true; });
  native.adoptWithoutCatch().catch(() => { adopted = true; });
  await Promise.resolve();
  assert.equal(yielded, false);
  assert.equal(adopted, false);
  await Promise.resolve();
  assert.equal(yielded, true);
  assert.equal(adopted, false);
  await Promise.resolve();
  assert.equal(adopted, true);
});

test("failure of the first cleanup still waits for the second cleanup", async () => {
  function deferred() {
    let resolve!: () => void, reject!: (reason: unknown) => void;
    const promise = new Promise<void>((yes, no) => { resolve = yes; reject = no; });
    return { promise, resolve, reject };
  }
  const first = deferred(), second = deferred();
  let finished = false;
  const result = native.cleanupBoth(first.promise, second.promise).catch(reason => {
    finished = true;
    assert.equal(reason, 0n);
  });
  first.reject(0n);
  await Promise.resolve();
  await Promise.resolve();
  assert.equal(finished, false);
  second.resolve();
  await result;
  assert.equal(finished, true);
});
