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
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function compileDafny(tsText: string, fileName = "repro.ts"): string {
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true },
    useInMemoryFileSystem: true,
  });
  const sf = project.createSourceFile(fileName, tsText, { overwrite: true });
  const diags = project.getPreEmitDiagnostics().map(d => d.getMessageText());
  assert.deepEqual(diags, [], `invalid TS in ${fileName}: ${JSON.stringify(diags)}`);
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(sf))));
  const optTypes = typesFile ? peepholeModule(typesFile, "dafny") : null;
  const optDef = peepholeModule(defFile, "dafny");
  return emitDafnyFile({ ...optDef, decls: [...(optTypes?.decls ?? []), ...optDef.decls] }, fileName);
}

function verifyDafny(dfyText: string): { status: number | null; output: string } {
  const dir = mkdtempSync(join(tmpdir(), "lsc-405-"));
  try {
    const file = join(dir, "repro.dfy");
    writeFileSync(file, dfyText);
    const res = spawnSync("dafny", ["verify", "--verification-time-limit:15", file], {
      encoding: "utf8",
      timeout: 60_000,
    });
    assert.ifError(res.error);
    return { status: res.status, output: `${res.stdout ?? ""}\n${res.stderr ?? ""}` };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("#405: union scrutinee reassignment verifies true contracts across switch, tagMatch, callbacks, spreads, structural calls, nested switches, and synth array-unions", () => {
  const validTs = `
export interface Payload { n: number }
export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
export type Pair = { kind: "a"; x: number; y: number } | { kind: "b"; x: number };
export type Colliding = { kind: "a"; value: number } | { kind: "b"; value: string };

export function readPayload(p: Payload): number {
  return p.n;
}

//@ requires input.kind === "a" && input.n === 0
//@ ensures \\result === 5
export function directAfterReassignment(input: Shape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, n: 5 };
      return sh.n;
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ requires xs.length === 1 && xs[0] === 0
//@ ensures \\result.length === 1 && \\result[0] === 5
export function callbackAfterReassignment(input: Shape, xs: number[]): number[] {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, n: 5 };
      return xs.map(x => x + sh.n);
    case "b":
      return [];
  }
}

//@ requires input.kind === "a" && input.x === 0 && input.y === 0
//@ ensures \\result === 15
export function fieldWriteAfterSpreadReassignment(input: Pair): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, x: 5 };
      sh.y = 10;
      return sh.x + sh.y;
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.n === 0
//@ ensures \\result === 5
export function structuralCallAfterReassignment(input: Shape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, n: 5 };
      return readPayload(sh);
    case "b":
      return 0;
  }
}

//@ requires input.kind === "a" && input.value === 1
//@ ensures \\result === "bye"
export function crossVariantCollidingSpread(input: Colliding): string {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { kind: "b", value: "hi" };
      sh = { ...sh, value: "bye" };
      return sh.value;
    case "b":
      return sh.value;
  }
}

//@ requires input.kind === "a" && input.value === 1
//@ ensures \\result === 9
export function sameVariantCollidingSpread(input: Colliding): number {
  let sh = input;
  if (sh.kind === "a") {
    sh = { ...sh, value: 9 };
    return sh.value;
  }
  return 0;
}

//@ requires Array.isArray(input) && input.length === 2
//@ ensures \\result === 47
export function synthArrayUnionReadPushAndReassign(input: number[] | number): number {
  let u = input;
  if (Array.isArray(u)) {
    const before = u.length;
    u.push(7);
    const after = u.length;
    u = 42;
    return before + after + u;
  }
  return u;
}

//@ requires aIn.kind === "a" && aIn.n === 0
//@ requires bIn.kind === "a" && bIn.n === 0
//@ ensures \\result === 15
export function nestedIndependentSwitches(aIn: Shape, bIn: Shape): number {
  let a = aIn;
  let b = bIn;
  switch (a.kind) {
    case "a":
      switch (b.kind) {
        case "a":
          a = { ...a, n: 5 };
          b.n = 10;
          return a.n + b.n;
        case "b":
          return 0;
      }
    case "b":
      return 0;
  }
}

export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };

//@ ensures input.kind === "b" ==> \\result === 1
export function unionArrayPushPostSwitch(input: Item): number {
  let u = input;
  const before = u.kind === "b" ? u.items.length : 0;
  switch (u.kind) {
    case "a":
      u.v = 99;
      break;
    case "b":
      u.items.push(1);
      break;
  }
  const after = u.kind === "b" ? u.items.length : 0;
  return after - before;
}
`;
  const dfy = compileDafny(validTs, "valid_405.ts");
  const res = verifyDafny(dfy);
  assert.equal(res.status, 0, `${dfy}\n${res.output}`);

  const synthPushTs = `
//@ ensures Array.isArray(input) ==> \\result === 1
export function synthArrayPushPostBranch(input: number[] | string): number {
  let x = input;
  const before = Array.isArray(x) ? x.length : 0;
  if (Array.isArray(x)) {
    x.push(99);
  }
  const after = Array.isArray(x) ? x.length : 0;
  return after - before;
}
`;
  const synthDfy = compileDafny(synthPushTs, "synth_push_405.ts");
  const synthRes = verifyDafny(synthDfy);
  assert.equal(synthRes.status, 0, `${synthDfy}\n${synthRes.output}`);
});

test("#405: false postconditions after union scrutinee reassignment are rejected by Dafny", () => {
  const falseCases: Array<[string, string]> = [
    [
      "direct-stale-read",
      `export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
      //@ requires input.kind === "a" && input.n === 0
      //@ ensures \\result === 0
      export function f(input: Shape): number {
        let sh = input;
        switch (sh.kind) {
          case "a": sh = { ...sh, n: 5 }; return sh.n;
          case "b": return 0;
        }
      }`,
    ],
    [
      "callback-stale-read",
      `export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
      //@ requires input.kind === "a" && input.n === 0
      //@ requires xs.length === 1 && xs[0] === 0
      //@ ensures \\result.length === 1 && \\result[0] === 0
      export function f(input: Shape, xs: number[]): number[] {
        let sh = input;
        switch (sh.kind) {
          case "a": sh = { ...sh, n: 5 }; return xs.map(x => x + sh.n);
          case "b": return [];
        }
      }`,
    ],
    [
      "field-write-clobber",
      `export type Pair = { kind: "a"; x: number; y: number } | { kind: "b"; x: number };
      //@ requires input.kind === "a" && input.x === 0 && input.y === 0
      //@ ensures \\result === 10
      export function f(input: Pair): number {
        let sh = input;
        switch (sh.kind) {
          case "a": sh = { ...sh, x: 5 }; sh.y = 10; return sh.x + sh.y;
          case "b": return 0;
        }
      }`,
    ],
    [
      "nested-switch-b-write",
      `export type Shape = { kind: "a"; n: number } | { kind: "b"; n: number };
      //@ requires aIn.kind === "a" && aIn.n === 0
      //@ requires bIn.kind === "a" && bIn.n === 0
      //@ ensures \\result === 5
      export function f(aIn: Shape, bIn: Shape): number {
        let a = aIn;
        let b = bIn;
        switch (a.kind) {
          case "a":
            switch (b.kind) {
              case "a": a = { ...a, n: 5 }; b.n = 10; return a.n + b.n;
              case "b": return 0;
            }
          case "b": return 0;
        }
      }`,
    ],
  ];

  for (const [label, src] of falseCases) {
    const dfy = compileDafny(src, `${label}.ts`);
    const res = verifyDafny(dfy);
    assert.notEqual(res.status, 0, `${label} should fail verification!\n${dfy}\n${res.output}`);
    assert.match(res.output, /postcondition could not be proved|might not hold/, `${label}: expected postcondition failure, got:\n${res.output}`);
  }
});

test("#405: Lean emits constructor-preserving match updates (no invalid `{ sh with ... }` on inductives)", () => {
  const tsText = `
export type Shape = { kind: "a"; x: number; y: number } | { kind: "b"; z: number };
export function updateShape(input: Shape): number {
  let sh = input;
  switch (sh.kind) {
    case "a":
      sh = { ...sh, x: 5 };
      sh.y = 10;
      return sh.x + sh.y;
    case "b":
      return sh.z;
  }
}
`;
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true },
    useInMemoryFileSystem: true,
  });
  const sf = project.createSourceFile("lean_405.ts", tsText, { overwrite: true });
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(narrowModule(resolveModule(extractModule(sf))));
  if (typesFile) emitLeanFile(typesFile);
  const leanDef = emitLeanFile(defFile);
  assert.doesNotMatch(leanDef, /\{ sh with/, `Lean inductive cannot use struct-with syntax:\n${leanDef}`);
  assert.match(leanDef, /match sh with \| \.a _ _f1 => Shape\.a \(5\) _f1/, leanDef);
  assert.match(leanDef, /match sh with \| \.a _f0 _ => Shape\.a _f0 \(10\)/, leanDef);
});
