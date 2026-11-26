import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  extendFieldPlace,
  extendUnwrapPlace,
  extendVariantPlace,
  makeVarPlace,
  placeDepth,
  placeHasUnwrap,
  placeHasVariant,
  placeIsVar,
  placeRoot,
  placesMayOverlap,
} from "../src/places.ts";
import {
  createImperativeCounts,
  evaluateImperativeProgram,
  type ImperativeProgram,
} from "../fuzz/imperative-oracle.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleLean } from "../src/transform.ts";
import { emitLeanFile } from "../src/lean-emit.ts";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

test("places.ts pure PlacePath operations and non-overlap soundness (#49)", () => {
  const a = makeVarPlace("a");
  const b = makeVarPlace("b");
  assert.equal(placeRoot(a), "a");
  assert.equal(placeDepth(a), 0);
  assert.equal(placeIsVar(a), true);
  assert.equal(placesMayOverlap(a, b), false);

  const aItems = extendFieldPlace(extendUnwrapPlace(a), "items");
  const aCount = extendFieldPlace(extendUnwrapPlace(a), "count");
  assert.equal(placeRoot(aItems), "a");
  assert.equal(placeDepth(aItems), 2);
  assert.equal(placeHasUnwrap(aItems), true);
  assert.equal(placeHasVariant(aItems), false);
  assert.equal(placesMayOverlap(aItems, aCount), false);
  assert.equal(placesMayOverlap(aItems, aItems), true);

  const uA = extendVariantPlace(makeVarPlace("u"), "a");
  const uB = extendVariantPlace(makeVarPlace("u"), "b");
  assert.equal(placeHasVariant(uA), true);
  assert.equal(placesMayOverlap(uA, uB), false);
});

test("tools/src/places.ts self-verifies cleanly via lsc check --backend=dafny (#49)", () => {
  const res = spawnSync(
    process.execPath,
    [compiledCli, "check", "--backend=dafny", path.join(repoRoot, "tools/src/places.ts")],
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

test("unified Place write-back verifies #350, optional arr[i]=v, nested Box.items.push, union switch push, nested field assign, and opt pop (#49)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m3a-places-"));
  const programs: ImperativeProgram[] = [
    {
      family: "mutation",
      label: "issue-350-opt-array-push",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(arr?: number[]): number {",
        "  if (arr !== undefined) {",
        "    arr.push(9);",
        "  }",
        "  return arr !== undefined ? arr.length : 0;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int-array", value: [1, 2] }] },
        { args: [{ kind: "opt-int-array", value: undefined }] },
      ],
    },
    {
      family: "mutation",
      label: "opt-array-index-assign-post-branch",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(arr?: number[]): number {",
        "  if (arr !== undefined && arr.length > 0) {",
        "    arr[0] = 10;",
        "  }",
        "  return arr !== undefined && arr.length > 0 ? arr[0] : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int-array", value: [1, 2] }] },
        { args: [{ kind: "opt-int-array", value: undefined }] },
      ],
    },
    {
      family: "mutation",
      label: "nested-opt-box-push",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box): number {",
        "  if (b !== undefined && b.items !== undefined) {",
        "    b.items.push(7);",
        "  }",
        "  return b !== undefined && b.items !== undefined ? b.items.length : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-box", value: { items: [1, 2], count: 1 } }] },
        { args: [{ kind: "opt-box", value: { items: undefined, count: 1 } }] },
      ],
    },
    {
      family: "union",
      label: "union-switch-mutate-post-branch",
      fnName: "target",
      returnKind: "number",
      tsText: [
        'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
        "export function target(u: Item): number {",
        "  switch (u.kind) {",
        '    case "a": return u.v;',
        '    case "b": u.items.push(5); break;',
        "  }",
        '  return u.kind === "b" ? u.items.length : -1;',
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "union-ab", value: { kind: "b", items: [1, 2] } }] },
        { args: [{ kind: "union-ab", value: { kind: "a", v: 3 } }] },
      ],
    },
    {
      family: "reassign",
      label: "nested-opt-field-assign",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box): number {",
        "  if (b !== undefined && b.count !== undefined) {",
        "    b.count = b.count + 4;",
        "  }",
        "  return b !== undefined && b.count !== undefined ? b.count : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-box", value: { items: [1], count: 3 } }] },
        { args: [{ kind: "opt-box", value: undefined }] },
      ],
    },
    {
      family: "mutation",
      label: "opt-array-pop-post-branch",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(arr?: number[]): number {",
        "  let popped = 0;",
        "  if (arr !== undefined && arr.length > 0) {",
        "    const last = arr.pop();",
        "    popped = last !== undefined ? last : 0;",
        "  }",
        "  return (arr !== undefined ? arr.length : 0) + popped;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int-array", value: [3, 7] }] },
        { args: [{ kind: "opt-int-array", value: undefined }] },
      ],
    },
  ];

  try {
    for (const prog of programs) {
      const out = evaluateImperativeProgram(prog, {
        project,
        workDir,
        counts: createImperativeCounts(),
        timeoutSec: 15,
        stages: ["pre", "opt"],
      });
      assert.equal(out.ok, true, `${prog.label} failed (${out.oracle}): ${out.detail}`);
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("non-Place mutating collection call fails closed with clear diagnostic (#49)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m3a-nonplace-"));
  try {
    const nonPlace: ImperativeProgram = {
      family: "mutation",
      label: "non-place-push",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function getArr(): number[] { return [1, 2]; }",
        "export function target(): number {",
        "  getArr().push(3);",
        "  return 0;",
        "}",
      ].join("\n"),
      inputs: [{ args: [] }],
    };
    const out = evaluateImperativeProgram(nonPlace, {
      project,
      workDir,
      counts: createImperativeCounts(),
      timeoutSec: 15,
    });
    assert.equal(out.ok, false);
    assert.equal(out.oracle, "rejected");
    assert.match(out.detail, /not a writable Place rooted at a variable/);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("review regressions (#49): union variant field/index assign, optional field assign/clear, Array.isArray synth-union push, narrowed m.get(k)?.push, and Lean let-mut shadowing", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m3a-rev-"));
  const programs: ImperativeProgram[] = [
    // Issue 1a: union variant field assignment + same-arm read (was soundness-refuted!)
    {
      family: "union",
      label: "union-switch-field-assign-same-arm",
      fnName: "target",
      returnKind: "number",
      tsText: [
        'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
        "export function target(u: Item): number {",
        "  switch (u.kind) {",
        '    case "a":',
        "      u.v = 99;",
        "      return u.v;",
        '    case "b":',
        "      return u.items.length;",
        "  }",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "union-ab", value: { kind: "a", v: 3 } }] }],
    },
    // Issue 1b: union variant array index assignment + same-arm read
    {
      family: "union",
      label: "union-if-index-assign-same-arm",
      fnName: "target",
      returnKind: "number",
      tsText: [
        'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
        "export function target(u: Item): number {",
        '  if (u.kind === "b" && u.items.length > 0) {',
        "    u.items[0] = 10;",
        "    return u.items[0];",
        "  }",
        "  return -1;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "union-ab", value: { kind: "b", items: [1, 2] } }] }],
    },
    // Issue 2a: optional field assignment without narrowing the field itself (`b.count = 5`)
    {
      family: "reassign",
      label: "opt-field-assign-unwrapped-container",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box): number {",
        "  if (b !== undefined) {",
        "    b.count = 5;",
        "  }",
        "  return b !== undefined && b.count !== undefined ? b.count : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-box", value: { items: [1], count: undefined } }] },
        { args: [{ kind: "opt-box", value: undefined }] },
      ],
    },
    // Issue 2b: clearing a narrowed optional field (`b.count = undefined`)
    {
      family: "reassign",
      label: "opt-field-assign-undefined",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box): number {",
        "  if (b !== undefined && b.count !== undefined) {",
        "    b.count = undefined;",
        "  }",
        "  return b !== undefined && b.count !== undefined ? b.count : -1;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "opt-box", value: { items: [1], count: 7 } }] }],
    },
    // Issue 2c: assigning an optional variable to a narrowed optional field (`b.count = x`)
    {
      family: "reassign",
      label: "opt-field-assign-optional-var",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box, x?: number): number {",
        "  if (b !== undefined && b.count !== undefined) {",
        "    b.count = x;",
        "  }",
        "  return b !== undefined && b.count !== undefined ? b.count : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-box", value: { items: [1], count: 7 } }, { kind: "opt-int", value: 42 }] },
        { args: [{ kind: "opt-box", value: { items: [1], count: 7 } }, { kind: "opt-int", value: undefined }] },
      ],
    },
    // Issue 4: statement-level `m.get(k)?.push(v)` inside `someMatch` on optional map
    {
      family: "mutation",
      label: "opt-map-optchain-push-post-branch",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(m?: Map<string, number[]>): number {",
        "  if (m !== undefined) {",
        '    m.get("a")?.push(1);',
        "  }",
        '  const got = m !== undefined ? m.get("a") : undefined;',
        "  return got !== undefined ? got.length : 0;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "arr-map", value: [["a", [5, 6]]] }] }],
    },
  ];

  // Note: `m?: Map<string, number[]>` needs Option.Some(map[...]); test Issue 3 (`Array.isArray`)
  // and Issue 4 directly via Dafny `lsc check` too so their exact false-proof contracts fail/pass.
  try {
    for (const prog of programs.slice(0, 5)) {
      const out = evaluateImperativeProgram(prog, {
        project,
        workDir,
        counts: createImperativeCounts(),
        timeoutSec: 15,
        stages: ["pre", "opt"],
      });
      assert.equal(out.ok, true, `${prog.label} failed (${out.oracle}): ${out.detail}`);
    }

    // Issue 3 (`Array.isArray(x)` synth-union push): prove `after - before === 1` in Dafny!
    const synthSrc = [
      "export function target(x: number[] | string): number {",
      "  //@ ensures Array.isArray(x) ==> \\result === 1",
      "  const before = Array.isArray(x) ? x.length : 0;",
      "  if (Array.isArray(x)) {",
      "    x.push(99);",
      "  }",
      "  const after = Array.isArray(x) ? x.length : 0;",
      "  return after - before;",
      "}",
    ].join("\n");
    const synthFile = path.join(workDir, "synth_push.ts");
    writeFileSync(synthFile, synthSrc);
    const synthRes = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", synthFile], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    });
    assert.equal(synthRes.status, 0, `${synthRes.stdout}\n${synthRes.stderr}`);

    // Issue 4 (`if (m !== undefined) { m.get("a")?.push(1); }`): prove length increments by 1!
    const optMapSrc = [
      "export function target(m?: Map<string, number[]>): number {",
      '  //@ ensures m !== undefined && m.has("a") ==> \\result === 1',
      '  const before = m !== undefined ? (m.get("a")?.length ?? 0) : 0;',
      "  if (m !== undefined) {",
      '    m.get("a")?.push(1);',
      "  }",
      '  const after = m !== undefined ? (m.get("a")?.length ?? 0) : 0;',
      "  return after - before;",
      "}",
    ].join("\n");
    const optMapFile = path.join(workDir, "opt_map_push.ts");
    writeFileSync(optMapFile, optMapSrc);
    const optMapRes = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", optMapFile], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    });
    assert.equal(optMapRes.status, 0, `${optMapRes.stdout}\n${optMapRes.stderr}`);

    // Note 12: Lean `let mut` shadowing on mutated `someMatch` and `switch` binders.
    const leanTs = [
      'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
      "export function pushOpt(arr?: number[]): number {",
      "  if (arr !== undefined) { arr.push(1); }",
      "  return arr !== undefined ? arr.length : 0;",
      "}",
      "export function pushUnion(u: Item): number {",
      "  switch (u.kind) {",
      '    case "a": return u.v;',
      '    case "b": u.items.push(1); break;',
      "  }",
      '  return u.kind === "b" ? u.items.length : 0;',
      "}",
    ].join("\n");
    const sf = project.createSourceFile("lean_wb.ts", leanTs, { overwrite: true });
    const leanDef = emitLeanFile(transformModuleLean(narrowModule(resolveModule(extractModule(sf)))).defFile);
    assert.match(leanDef, /let mut _arr_val/, "Lean should shadow mutated someMatch binder with let mut");
    assert.match(leanDef, /arr := Option\.some _arr_val/, "Lean should write back Option.some");
    assert.match(leanDef, /let mut _u_items/, "Lean should shadow mutated union variant binder with let mut");
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
