import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");

test("issue #338: loose nullish checks and negated strict/loose sentinel checks narrow Option<T> and Nullish<T>", () => {
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-fix-338-"));
  try {
    const f = path.join(workDir, "negated_presence.ts");
    writeFileSync(f, [
      "//@ backend dafny",
      "export interface Box { v?: number; n: number | null; u?: number | null }",
      "",
      "export function negEqUndef(x?: number): number {",
      "  //@ verify",
      "  //@ ensures x !== undefined ==> \\result === x + 1",
      "  if (!(x === undefined)) return x + 1;",
      "  return 0;",
      "}",
      "",
      "export function negNeqUndefEarly(x?: number): number {",
      "  //@ verify",
      "  //@ ensures x !== undefined ==> \\result === x + 2",
      "  if (!(x !== undefined)) return 0;",
      "  return x + 2;",
      "}",
      "",
      "export function negEqNull(x: number | null): number {",
      "  //@ verify",
      "  //@ ensures x !== null ==> \\result === x + 3",
      "  if (!(x === null)) return x + 3;",
      "  return 0;",
      "}",
      "",
      "export function negLooseNull(x?: number): number {",
      "  //@ verify",
      "  //@ ensures x !== undefined ==> \\result === x + 4",
      "  if (!(x == null)) return x + 4;",
      "  return 0;",
      "}",
      "",
      "export function negLooseNullish(x: number | null | undefined): number {",
      "  //@ verify",
      "  //@ ensures x != null ==> \\result === x + 5",
      "  if (!(x == null)) return x + 5;",
      "  return 0;",
      "}",
      "",
      "export function negStrictNullishTwoStep(x: number | null | undefined): number {",
      "  //@ verify",
      "  //@ ensures x != null ==> \\result === x + 6",
      "  if (!(x === null) && !(x === undefined)) return x + 6;",
      "  return 0;",
      "}",
      "",
      "export function negFieldPath(b: Box): number {",
      "  //@ verify",
      "  if (!(b.v === undefined)) return b.v + 1;",
      "  if (!(b.n === null)) return b.n + 2;",
      "  if (!(b.u == null)) return b.u + 3;",
      "  return 0;",
      "}",
      "",
      "export function looseChecksAll(x?: number, y?: number): number {",
      "  //@ verify",
      "  if (x == null) return 0;",
      "  if (y != undefined) return x + y;",
      "  return x;",
      "}",
    ].join("\n"));

    const res = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", f], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 120_000,
    });
    assert.equal(res.status, 0, `negated_presence.ts failed:\n${res.stdout}\n${res.stderr}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
