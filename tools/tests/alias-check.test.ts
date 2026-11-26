import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  bindCopyGroup,
  bindFreshGroup,
  findLiveAliasConflict,
  hasLiveAliasConflict,
  lookupAliasGroup,
} from "../src/alias-check.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { checkModuleLiveAliases } from "../src/alias-check-pass.ts";
import {
  createImperativeCounts,
  evaluateImperativeProgram,
  type ImperativeProgram,
} from "../fuzz/imperative-oracle.ts";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

function checkAliasesOfSource(tsText: string) {
  const project = makeProject();
  const sf = project.createSourceFile("alias_case.ts", tsText, { overwrite: true });
  const resolved = resolveModule(extractModule(sf));
  return checkModuleLiveAliases(resolved);
}

test("alias-check.ts pure conflict kernel contracts (#50)", () => {
  let aliases = new Map<string, number>();
  aliases = bindFreshGroup(aliases, "a", 1);
  aliases = bindCopyGroup(aliases, "b", "a", 2);
  assert.equal(lookupAliasGroup(aliases, "a"), 1);
  assert.equal(lookupAliasGroup(aliases, "b"), 1);
  assert.equal(findLiveAliasConflict("b", aliases, new Set(["a", "b"]), ["a", "b"]), "a");
  assert.equal(hasLiveAliasConflict("b", aliases, new Set(["b"]), ["a", "b"]), false);

  aliases = bindFreshGroup(aliases, "b", 3);
  assert.equal(hasLiveAliasConflict("b", aliases, new Set(["a", "b"]), ["a", "b"]), false);
});

test("tools/src/alias-check.ts self-verifies cleanly via lsc check --backend=dafny (#50)", () => {
  const res = spawnSync(
    process.execPath,
    [compiledCli, "check", "--backend=dafny", path.join(repoRoot, "tools/src/alias-check.ts")],
    {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    },
  );
  assert.ifError(res.error);
  const out = `${res.stdout ?? ""}\n${res.stderr ?? ""}`;
  assert.equal(res.status, 0, out);
  assert.match(out, /finished with \d+ verified, 0 errors/);
});

test("precise live-alias boundary: rejects live-alias mutations, allows read-only aliases, dead moves, clones, and unaliased reassignments (#50)", () => {
  // 1. Live-alias mutation -> rejected naming both `b` and `a`.
  const liveConflict = checkAliasesOfSource([
    "export function target(a: number[]): number {",
    "  const b = a;",
    "  b.push(1);",
    "  return a.length;",
    "}",
  ].join("\n"));
  assert.equal(liveConflict.length, 1);
  assert.equal(liveConflict[0]!.mutatedVar, "b");
  assert.equal(liveConflict[0]!.liveAlias, "a");
  assert.match(liveConflict[0]!.detail, /`b`/);
  assert.match(liveConflict[0]!.detail, /`a`/);

  // 2. Loop-carried live-alias mutation -> rejected.
  const loopConflict = checkAliasesOfSource([
    "export function target(a: number[], n: number): number {",
    "  const b = a;",
    "  let i = 0;",
    "  let total = 0;",
    "  while (i < n) {",
    "    b.push(i);",
    "    total = total + a.length;",
    "    i = i + 1;",
    "  }",
    "  return total;",
    "}",
  ].join("\n"));
  assert.ok(loopConflict.length >= 1, "expected loop-carried live-alias mutation to be rejected");

  // 3. Partial branch unaliasing (`if (flag) b = []`) -> still aliases `a` on else path -> rejected.
  const branchConflict = checkAliasesOfSource([
    "export function target(a: number[], flag: boolean): number {",
    "  let b = a;",
    "  if (flag) {",
    "    b = [];",
    "  }",
    "  b.push(1);",
    "  return a.length;",
    "}",
  ].join("\n"));
  assert.equal(branchConflict.length, 1);

  // 4. Read-only alias -> allowed.
  assert.equal(checkAliasesOfSource([
    "export function target(a: number[]): number {",
    "  const b = a;",
    "  return a.length + b.length;",
    "}",
  ].join("\n")).length, 0);

  // 5. Dead-source move -> allowed.
  assert.equal(checkAliasesOfSource([
    "export function target(a: number[]): number {",
    "  const b = a;",
    "  b.push(1);",
    "  return b.length;",
    "}",
  ].join("\n")).length, 0);

  // 6. Post-reassignment unaliased mutation (`b = []`) -> allowed.
  assert.equal(checkAliasesOfSource([
    "export function target(a: number[]): number {",
    "  let b = a;",
    "  b = [];",
    "  b.push(1);",
    "  return a.length + b.length;",
    "}",
  ].join("\n")).length, 0);

  // 7. Explicit clones (`[...a]`, `new Map(m)`, `new Set(s)`) -> allowed.
  assert.equal(checkAliasesOfSource([
    "export function target(a: number[], m: Map<string, number>, s: Set<number>): number {",
    "  const a2 = [...a];",
    "  a2.push(1);",
    "  const m2 = new Map(m);",
    '  m2.set("k", 2);',
    "  const s2 = new Set(s);",
    "  s2.add(3);",
    "  return a.length + a2.length + m.size + m2.size + s.size + s2.size;",
    "}",
  ].join("\n")).length, 0);

  // 8. Entry-parameter `//@ ensures` mention (swap.ts pattern) -> allowed.
  assert.equal(checkAliasesOfSource([
    "export function swap(arr: number[], i: number, j: number): number[] {",
    "  //@ requires 0 <= i && i < arr.length && 0 <= j && j < arr.length",
    "  //@ ensures \\result[i] === arr[j]",
    "  let result = arr;",
    "  const tmp = result[i];",
    "  result[i] = result[j];",
    "  result[j] = tmp;",
    "  return result;",
    "}",
  ].join("\n")).length, 0);
});

test("imperative soundness oracle confirms live-alias-mutation is rejected while dead-source-move and read-only-alias verify (#50)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m3b-alias-"));
  try {
    const liveAlias: ImperativeProgram = {
      family: "aliasing",
      label: "live-alias-mutation",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(a: number[]): number {",
        "  const b = a;",
        "  b.push(5);",
        "  return a.length;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "int-array", value: [1, 2] }] }],
    };
    const rLive = evaluateImperativeProgram(liveAlias, { project, workDir, counts: createImperativeCounts(), timeoutSec: 15 });
    assert.equal(rLive.ok, false);
    assert.equal(rLive.oracle, "rejected");
    assert.match(rLive.detail, /Live-alias mutation/);

    const deadMove: ImperativeProgram = {
      family: "aliasing",
      label: "dead-source-move",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(a: number[]): number {",
        "  const b = a;",
        "  b.push(5);",
        "  return b.length;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "int-array", value: [1, 2] }] }],
    };
    const rDead = evaluateImperativeProgram(deadMove, { project, workDir, counts: createImperativeCounts(), timeoutSec: 15 });
    assert.equal(rDead.ok, true, `${rDead.signature}\n${rDead.detail}`);

    const readOnly: ImperativeProgram = {
      family: "aliasing",
      label: "read-only-alias",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(a: number[]): number {",
        "  const b = a;",
        "  return a.length + b.length;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "int-array", value: [1, 2] }] }],
    };
    const rRead = evaluateImperativeProgram(readOnly, { project, workDir, counts: createImperativeCounts(), timeoutSec: 15 });
    assert.equal(rRead.ok, true, `${rRead.signature}\n${rRead.detail}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("review regressions (#50): break/continue liveness & forward escape, ternary/nullish/optChain aliases, shallow-copy nested mutation vs outer mutation, nonNull clones, this.field, m.values(), and lambdas", () => {
  // Issue 5a: break backward liveness (`if (flag) { b.push(1); break; } return 0;` before `return a.length;`)
  assert.ok(checkAliasesOfSource([
    "export function target(a: number[], flag: boolean): number {",
    "  const b = a;",
    "  let i = 0;",
    "  while (i < 1) {",
    "    if (flag) { b.push(1); break; }",
    "    return 0;",
    "  }",
    "  return a.length;",
    "}",
  ].join("\n")).length >= 1, "break backward liveness must catch live-alias mutation");

  // Issue 5b: break forward alias escape (`if (flag) { b = a; break; } b = [];` then `b.push(1); return a.length;`)
  assert.ok(checkAliasesOfSource([
    "export function target(a: number[], flag: boolean): number {",
    "  let b: number[] = [];",
    "  let i = 0;",
    "  while (i < 1) {",
    "    if (flag) { b = a; break; }",
    "    b = [];",
    "    i = i + 1;",
    "  }",
    "  b.push(1);",
    "  return a.length;",
    "}",
  ].join("\n")).length >= 1, "break forward alias escape must be caught");

  // Issue 5c: continue backward liveness inside loop
  assert.ok(checkAliasesOfSource([
    "export function target(a: number[], flag: boolean): number {",
    "  const b = a;",
    "  let i = 0;",
    "  let total = 0;",
    "  while (i < 2) {",
    "    total = total + a.length;",
    "    i = i + 1;",
    "    if (flag) { b.push(1); continue; }",
    "    return total;",
    "  }",
    "  return total;",
    "}",
  ].join("\n")).length >= 1, "continue backward liveness must catch live-alias mutation");

  // Issue 6: conditional, nullish coalescing, and optional chaining aliases
  assert.ok(checkAliasesOfSource([
    "export function target(a: number[], flag: boolean): number {",
    "  const b = flag ? a : [9];",
    "  b.push(1);",
    "  return a.length;",
    "}",
  ].join("\n")).length >= 1, "ternary alias must be caught");

  assert.ok(checkAliasesOfSource([
    "export function target(a?: number[]): number {",
    "  const b = a ?? [];",
    "  b.push(1);",
    "  return a !== undefined ? a.length : 0;",
    "}",
  ].join("\n")).length >= 1, "nullish coalescing alias must be caught");

  assert.ok(checkAliasesOfSource([
    "export interface Box { items?: number[] }",
    "export function target(b?: Box): number {",
    "  const sub = b?.items;",
    "  if (sub !== undefined) sub.push(1);",
    "  return b !== undefined && b.items !== undefined ? b.items.length : 0;",
    "}",
  ].join("\n")).length >= 1, "optional chain alias must be caught");

  // Issue 7a: shallow copy `{ ...a, count: 2 }` with NESTED mutation `b.items.push(99)` -> REJECTED!
  assert.ok(checkAliasesOfSource([
    "export interface Box { count: number; items: number[] }",
    "export function target(a: Box): number {",
    "  const b = { ...a, count: 2 };",
    "  b.items.push(99);",
    "  return a.items.length;",
    "}",
  ].join("\n")).length >= 1, "shallow record spread + nested push must be caught");

  // Issue 7b: shallow copy `new Map(m)` with NESTED `m2.get("k")?.push(99)` -> REJECTED!
  assert.ok(checkAliasesOfSource([
    "export function target(m: Map<string, number[]>): number {",
    "  const m2 = new Map(m);",
    '  m2.get("k")?.push(99);',
    '  const orig = m.get("k");',
    "  return orig !== undefined ? orig.length : 0;",
    "}",
  ].join("\n")).length >= 1, "shallow Map clone + nested push must be caught");

  // Issue 7c: shallow copy `new Map(m)` with TOP-LEVEL `m2.set("k", [])` -> ALLOWED (like todo-domain.ts)!
  assert.equal(checkAliasesOfSource([
    "export function target(m: Map<string, number[]>): number {",
    "  const m2 = new Map(m);",
    '  m2.set("k", []);',
    "  return m.size + m2.size;",
    "}",
  ].join("\n")).length, 0, "shallow Map clone + top-level set is sound in JS");

  // Issue 8a: single-spread `{ ...a }` on primitive record -> ALLOWED!
  assert.equal(checkAliasesOfSource([
    "export interface Box { count: number }",
    "export function target(a: Box): number {",
    "  const b = { ...a };",
    "  b.count = 5;",
    "  return a.count + b.count;",
    "}",
  ].join("\n")).length, 0, "single-spread clone of primitive record is sound");

  // Issue 8b: non-null assertion clones `[...a!]`, `new Map(m!)`, `new Set(s!)` -> ALLOWED!
  assert.equal(checkAliasesOfSource([
    "export function target(a?: number[], m?: Map<string, number>, s?: Set<number>): number {",
    "  const a2 = [...a!];",
    "  a2.push(1);",
    "  const m2 = new Map(m!);",
    '  m2.set("k", 2);',
    "  const s2 = new Set(s!);",
    "  s2.add(3);",
    "  return (a !== undefined ? a.length : 0) + a2.length + (m !== undefined ? m.size : 0) + m2.size + (s !== undefined ? s.size : 0) + s2.size;",
    "}",
  ].join("\n")).length, 0, "non-null clones must not be falsely flagged");

  // Issue 9a: class `this.items` aliasing -> REJECTED!
  assert.ok(checkAliasesOfSource([
    "export class Counter {",
    "  items: number[] = [];",
    "  bump(): number {",
    "    //@ verify",
    "    const before = this.items.length;",
    "    const b = this.items;",
    "    b.push(2);",
    "    return this.items.length - before;",
    "  }",
    "}",
  ].join("\n")).length >= 1, "class this.field live-alias mutation must be caught");

  // Issue 9b: `for (const arr of m.values()) { arr.push(1); }` -> REJECTED when `m` is read after!
  assert.ok(checkAliasesOfSource([
    "export function target(m: Map<string, number[]>): number {",
    "  for (const arr of m.values()) {",
    "    arr.push(1);",
    "  }",
    "  return m.size;",
    "}",
  ].join("\n")).length >= 1, "for..of over m.values() mutating element while m is live must be caught");

  // Issue 9c: live-alias mutation inside lambda body -> REJECTED!
  assert.ok(checkAliasesOfSource([
    "export function target(a: number[], xs: number[]): number {",
    "  const b = a;",
    "  const ys = xs.map(x => { b.push(x); return x; });",
    "  return a.length + ys.length;",
    "}",
  ].join("\n")).length >= 1, "live-alias mutation inside lambda must be caught");
});
