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
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { peepholeModule } from "../src/peephole.ts";
import * as runtime from "../../examples/narrowedAssignment.ts";

// Regression tests for #342: assigning to a variable or path narrowed by
// `!== undefined` must end the narrowing instead of leaving reads bound to the
// stale match binder.

function generate(source: string): string {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext,
    lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("narrowed.ts", source);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(file))));
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-narrowed-"));
  try {
    const path = join(dir, "narrowed.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=15", path],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

test("narrowed-assignment example agrees with JavaScript", () => {
  assert.equal(runtime.assignDefined(3), 5);
  assert.equal(runtime.assignDefined(undefined), 0);
  assert.equal(runtime.assignFromSelf(3), 5);
  assert.equal(runtime.assignFromSelf(undefined), 0);
  assert.equal(runtime.assignInNestedIf(3, true), 4);
  assert.equal(runtime.assignInNestedIf(3, false), 3);
  assert.equal(runtime.assignInNestedIf(undefined, true), 0);
  assert.equal(runtime.assignInBranchAtTail(3, true), 4);
  assert.equal(runtime.assignInBranchAtTail(3, false), 3);
  assert.equal(runtime.assignInBranchAtTail(undefined, true), 0);
  assert.equal(runtime.assignUndefinedInBranch(3, true), 9);
  assert.equal(runtime.assignUndefinedInBranch(3, false), 3);
  assert.equal(runtime.assignUndefinedInBranch(undefined, false), 0);
  assert.equal(runtime.assignUndefined(3), 7);
  assert.equal(runtime.assignUndefined(undefined), 0);
  assert.equal(runtime.compareAfterUndefined(3), 1);
  assert.equal(runtime.compareAfterUndefined(undefined), 0);
});

test("a read after reassigning a narrowed path sees the assigned value", () => {
  const text = generate(`
export interface Box { v?: number }
export function wrong(q: Box): boolean {
  //@ ensures q.v === 1 ==> \\result === true
  let b: Box = q;
  if (b.v !== undefined) {
    b = { v: 7 };
    return b.v === 1;
  }
  return true;
}
`);
  const result = verify(text);
  assert.notEqual(result.status, 0, `the false postcondition must not verify:\n${text}`);
  assert.match(result.output, /postcondition could not be proved/);
});

test("writes that would leave a narrowing stale get a positioned lsc error", () => {
  const cases: [string, RegExp][] = [
    [`
export interface Cell { v: number }
export function cellField(p: Cell | undefined): number {
  let c = p;
  if (c !== undefined) { c.v = 1; return c.v; }
  return 0;
}
`, /narrowed\.ts:5: lsc does not support assigning 'c\.v' while a check narrows 'c' to a defined value/],
    [`
export interface Box { v?: number }
export function fieldEq(q: Box): number {
  let b: Box = q;
  if (b.v !== undefined) { b.v = 7; return b.v; }
  return 0;
}
`, /narrowed\.ts:5: lsc does not support assigning 'b\.v' while a check narrows 'b\.v' to a defined value/],
    [`
export function whileAssign(p: number | undefined): number {
  let o = p;
  let s = 0;
  if (o !== undefined) {
    let i = 0;
    while (i < 3) {
      //@ decreases 3 - i
      s = s + o;
      o = 5;
      i = i + 1;
    }
  }
  return s;
}
`, /narrowed\.ts:10: lsc does not support assigning 'o' inside a loop while a check outside the loop narrows 'o'/],
    [`
export function switchAssign(p: number | undefined, k: string): number {
  let o = p;
  if (o !== undefined) {
    switch (k) {
      case "a": o = 5; break;
      default: break;
    }
    return o;
  }
  return 0;
}
`, /narrowed\.ts:6: lsc does not support assigning 'o' inside a switch while a check outside it narrows 'o'/],
  ];
  for (const [source, message] of cases) assert.throws(() => generate(source), message);
});
