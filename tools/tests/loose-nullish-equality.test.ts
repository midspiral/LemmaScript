import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { peepholeModule } from "../src/peephole.ts";
import {
  looseIsNullish, looseOptional, looseNullable, looseDefault, looseEarlyReturn,
  loosePositive, looseAbsentOrPositive, looseField, looseCompare,
} from "../../examples/looseNullish.ts";

function generate(source: string): string {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("loose-nullish-regression.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  const typed = narrowModule(resolveModule(extractModule(file)));
  const { typesFile, defFile } = transformModuleDafny(typed);
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(source: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-loose-nullish-"));
  try {
    const text = generate(source);
    const path = join(dir, "test.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=10", path], {
      encoding: "utf8", timeout: 60_000,
    });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr, text };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("loose nullish examples agree with JavaScript, including zero", () => {
  for (const x of [null, undefined, 0, -1, 3]) {
    const absent = x === null || x === undefined;
    assert.equal(looseIsNullish(x), absent);
    assert.equal(looseDefault(x), absent ? 7 : x);
    assert.equal(looseEarlyReturn(x), absent ? 7 : x);
    assert.equal(loosePositive(x), !absent && x > 0);
    assert.equal(looseAbsentOrPositive(x), absent || x > 0);
    assert.equal(looseField({ value: x }), absent ? 7 : x);
    if (x !== null) assert.equal(looseOptional(x), absent);
    if (x !== undefined) assert.equal(looseNullable(x), !absent);
  }
  assert.equal(looseField({}), 7);
  for (const a of [null, 0, -1, 3]) {
    for (const b of [undefined, 0, -1, 3]) assert.equal(looseCompare(a, b), a == b);
  }
});

test("loose comparisons match both sentinels in either operand order", () => {
  const functions: string[] = [];
  for (const type of ["number | null", "number | undefined", "number | null | undefined"]) {
    for (const sentinel of ["null", "undefined"]) {
      for (const op of ["==", "!="]) {
        for (const reversed of [false, true]) {
          const expression = reversed ? `${sentinel} ${op} x` : `x ${op} ${sentinel}`;
          const expected = op === "==" ? "(x === null || x === undefined)" : "(x !== null && x !== undefined)";
          functions.push(String.raw`
export function compare${functions.length}(x: ${type}): boolean {
  //@ ensures \result === ${expected}
  return ${expression};
}`);
        }
      }
    }
  }
  const result = verify(functions.join("\n"));
  assert.equal(result.status, 0, result.output + result.text);
});

test("loose checks narrow branches, guards, fields and specification premises", () => {
  const example = readFileSync(new URL("../../examples/looseNullish.ts", import.meta.url), "utf8");
  const result = verify(example + String.raw`
export function optionalValue(x: number | undefined): number {
  //@ ensures x != null ==> \result === x
  if (x != null) return x;
  return 7;
}
export function retainUndefined(x: number | undefined): undefined {
  //@ ensures \result === undefined
  if (x == null) return x;
  return undefined;
}
export function retainNull(x: number | null): null {
  //@ ensures \result === null
  if (x == undefined) return x;
  return null;
}
export function ternary(x: number | null | undefined): number {
  //@ ensures x === null || x === undefined ==> \result === 7
  //@ ensures x !== null && x !== undefined ==> \result === x
  return x != null ? x : 7;
}
export function annotation(x: number | null | undefined): boolean {
  //@ ensures \result === (x == null)
  return x === null || x === undefined;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("loose nullish equality does not treat falsy payloads as absent", () => {
  const result = verify(String.raw`
export function zero(x: number | null | undefined): boolean {
  //@ requires x === 0
  //@ ensures \result
  return x != null;
}
export function empty(x: string | null | undefined): boolean {
  //@ requires x === ""
  //@ ensures \result
  return undefined != x;
}
export function falsy(x: boolean | null | undefined): boolean {
  //@ requires x === false
  //@ ensures !\result
  return x == null;
}
`);
  assert.equal(result.status, 0, result.output + result.text);
});

test("strict and loose nullish equality remain observably different", () => {
  for (const source of [String.raw`
export function wrong(x: number | null | undefined): boolean {
  //@ ensures \result === (x === null)
  return x == null;
}`, String.raw`
export function wrong(x: number | null | undefined): boolean {
  //@ ensures \result === (x == null)
  return x === null;
}`]) {
    const result = verify(source);
    assert.notEqual(result.status, 0, result.text);
    assert.match(result.output, /postcondition could not be proved/, result.output);
  }
});

test("loose nullish comparisons evaluate method operands once and in order", () => {
  const result = verify(String.raw`
function readFirst(): number | null { let x: number | null = null; return x; }
function readSecond(): number | undefined { let x: number | undefined = undefined; return x; }
export function compareCalls(): boolean {
  return readFirst() == readSecond();
}
export function compareNull(): boolean {
  return null != readFirst();
}
`);
  assert.equal(result.status, 0, result.output + result.text);
  const text = result.text;
  const compare = text.slice(text.indexOf("method compareCalls("), text.indexOf("method compareNull("));
  assert.equal((compare.match(/:= readFirst\(\)/g) ?? []).length, 1, compare);
  assert.equal((compare.match(/:= readSecond\(\)/g) ?? []).length, 1, compare);
  assert.ok(compare.indexOf(":= readFirst()") < compare.indexOf(":= readSecond()"), compare);
  const reversed = text.slice(text.indexOf("method compareNull("));
  assert.equal((reversed.match(/:= readFirst\(\)/g) ?? []).length, 1, reversed);
});

test("constant loose-comparison results cannot hide call or lookup obligations", () => {
  for (const source of [String.raw`
function sentinel(ok: boolean): null {
  //@ requires ok
  return null;
}
export function wrong(): boolean { return sentinel(false) == undefined; }
`, String.raw`
function payload(ok: boolean): number {
  //@ requires ok
  return 0;
}
export function wrong(): boolean { return null == payload(false); }
`, String.raw`
export function wrong(xs: number[]): boolean {
  //@ requires xs.length === 0
  //@ ensures xs[0] != null
  return true;
}
`]) {
    const result = verify(source);
    assert.notEqual(result.status, 0, result.text);
    assert.match(result.output, /precondition|out of range/, result.output);
  }
});
