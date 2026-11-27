import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");

test("issue #402: narrowed and non-null values coerce cleanly into nullable Set, Map, and Array operations", () => {
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-fix-402-"));
  try {
    const f = path.join(workDir, "nullable_collections.ts");
    writeFileSync(f, [
      "//@ backend dafny",
      "export interface Box { key: string | null }",
      "",
      "// Exact reproducer from issue #402 (with spec checking `in` coercion too)",
      "export function keeps(key: string | null, keys: Set<string | null>): boolean {",
      "  //@ verify",
      "  //@ ensures key === null ==> \\result === true",
      "  //@ ensures key !== null ==> \\result === !(key in keys)",
      "  return key === null || !keys.has(key);",
      "}",
      "",
      "// Non-narrowed literal and null into Set<string | null>",
      "export function hasLiteralAndNull(keys: Set<string | null>): boolean {",
      "  //@ verify",
      "  return keys.has(\"hello\") || keys.has(null);",
      "}",
      "",
      "// Early-return narrowing into Set.has / Set.add / Set.delete",
      "export function setOpsAfterEarlyReturn(key: string | null, keys: Set<string | null>): Set<string | null> {",
      "  //@ verify",
      "  if (key === null) return keys;",
      "  if (keys.has(key)) {",
      "    keys.delete(key);",
      "  } else {",
      "    keys.add(key);",
      "  }",
      "  return keys;",
      "}",
      "",
      "// Nested optional path: preserve outer box.value while avoiding redundant Some((box.value.key).value)",
      "export function keepsNested(box: Box | null, keys: Set<string | null>): boolean {",
      "  //@ verify",
      "  return box === null || box.key === null || !keys.has(box.key);",
      "}",
      "",
      "// Nullish<string> set with full narrowing, partial narrowing, and literals",
      "export function keepsNullish(key: string | null | undefined, keys: Set<string | null | undefined>): boolean {",
      "  //@ verify",
      "  return key === null || key === undefined || !keys.has(key);",
      "}",
      "",
      "export function keepsNullishPartial(key: string | null | undefined, keys: Set<string | null | undefined>): boolean {",
      "  //@ verify",
      "  return key === null || !keys.has(key);",
      "}",
      "",
      "export function hasNullishLiterals(keys: Set<string | null | undefined>): boolean {",
      "  //@ verify",
      "  return keys.has(\"a\") || keys.has(null) || keys.has(undefined);",
      "}",
      "",
      "// Cross-storage narrowing: Nullish<string> narrowed to string, passed into Option<string> set",
      "export function keepsNullishInOptSet(key: string | null | undefined, keys: Set<string | null>): boolean {",
      "  //@ verify",
      "  return key === null || key === undefined || !keys.has(key);",
      "}",
      "",
      "// Nullable Map keys and values: has, get, set, delete",
      "export function mapOps(key: string | null, val: number | null, m: Map<string | null, number | null>, counts: Map<string | null, number>): Map<string | null, number | null> {",
      "  //@ verify",
      "  if (key === null) return m;",
      "  const c = counts.get(key);",
      "  if (c !== undefined) {",
      "    m.set(key, c);",
      "  } else if (m.has(key)) {",
      "    m.delete(key);",
      "  } else if (val !== null) {",
      "    m.set(key, val);",
      "  }",
      "  return m;",
      "}",
      "",
      "// Nullable Array elements: includes, indexOf, push, unshift, index write (array.with)",
      "export function arrayOps(key: string | null, xs: (string | null)[]): boolean {",
      "  //@ verify",
      "  //@ requires xs.length > 0",
      "  if (key === null) return xs.includes(null);",
      "  const found = xs.includes(key) && xs.indexOf(key) >= 0;",
      "  xs.push(key);",
      "  xs.unshift(\"head\");",
      "  xs[0] = key;",
      "  return found && xs.includes(key);",
      "}",
      "",
      "// Optional-chaining call on nullable Set",
      "export function optChainSetHas(key: string | null, keys: Set<string | null> | null): boolean {",
      "  //@ verify",
      "  if (key === null) return false;",
      "  return keys?.has(key) ?? false;",
      "}",
    ].join("\n"));

    const res = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", f], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 120_000,
    });
    assert.equal(res.status, 0, `nullable_collections.ts Dafny check failed:\n${res.stdout}\n${res.stderr}`);

    const dfy = readFileSync(path.join(workDir, "nullable_collections.dfy"), "utf8");
    assert.match(dfy, /function keeps\(.*\n\{\n  \(\(match key .* \|\| !\(\(key in keys\)\)\)/,
      `expected clean 'key in keys' without redundant Some(key.value), got:\n${dfy}`);
    assert.match(dfy, /box\.value\.key in keys/,
      `expected 'box.value.key in keys', got:\n${dfy}`);
    assert.match(dfy, /Some\("hello"\) in keys/,
      `expected 'Some("hello") in keys', got:\n${dfy}`);
    assert.match(dfy, /Some\(key\.value\) in keys/,
      `expected cross-storage 'Some(key.value) in keys' for Nullish->Option, got:\n${dfy}`);

    // Verify Lean generation for the core issue #402 reproducer too
    const fLean = path.join(workDir, "keeps_lean.ts");
    writeFileSync(fLean, [
      "export function keeps(key: string | null, keys: Set<string | null>): boolean {",
      "  //@ verify",
      "  return key === null || !keys.has(key);",
      "}",
      "export function hasLiteral(keys: Set<string | null>): boolean {",
      "  //@ verify",
      "  return keys.has(\"hello\");",
      "}",
    ].join("\n"));
    const leanRes = spawnSync(process.execPath, [compiledCli, "gen", "--backend=lean", fLean], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    });
    assert.equal(leanRes.status, 0, `keeps_lean.ts Lean gen failed:\n${leanRes.stdout}\n${leanRes.stderr}`);
    const leanTypes = readFileSync(path.join(workDir, "keeps_lean.types.lean"), "utf8");
    assert.match(leanTypes, /keys\.contains key/,
      `expected clean 'keys.contains key' in Lean, got:\n${leanTypes}`);
    assert.match(leanTypes, /keys\.contains \(some "hello"\)/,
      `expected 'keys.contains (some "hello")' in Lean, got:\n${leanTypes}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
