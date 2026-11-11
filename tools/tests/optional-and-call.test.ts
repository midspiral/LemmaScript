import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  callArg, callArgIfElse, callArgTernary, nestedCallArg, nestedCallArgIfElse, type Box,
} from "../fixtures/optional-and-call.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function fixture() {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/optional-and-call.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-optional-and-call-"));
  try {
    const proof = join(dir, "optional-and-call.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const boxes: Box[] = [{}, { inner: {} }, { inner: { value: 5 } }, { inner: { value: 1 } }];

test("JavaScript: the call runs only once the optional is present", () => {
  assert.deepEqual([undefined, 5, 1].map(o => callArg(o, 2)), [false, true, false]);
  for (const fn of [callArgIfElse, callArgTernary]) {
    assert.deepEqual([undefined, 5, 1].map(o => fn(o, 2)), [0, 1, 0]);
  }
  assert.deepEqual(boxes.map(a => nestedCallArg(a, 2)), [false, false, true, false]);
  assert.deepEqual(boxes.map(a => nestedCallArgIfElse(a, 2)), [0, 0, 1, 0]);
});

test("Dafny passes the narrowed value to the call", () => {
  const { typesFile, defFile } = transformModuleDafny(fixture());
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  const facts = `
lemma Values()
  ensures !callArg(None, 2) && callArg(Some(5), 2) && !callArg(Some(1), 2)
  ensures callArgIfElse(None, 2) == 0 && callArgIfElse(Some(5), 2) == 1 && callArgIfElse(Some(1), 2) == 0
  ensures callArgTernary(None, 2) == 0 && callArgTernary(Some(5), 2) == 1 && callArgTernary(Some(1), 2) == 0
  ensures !nestedCallArg(Box(None), 2) && !nestedCallArg(Box(Some(Leaf(None))), 2)
  ensures nestedCallArg(Box(Some(Leaf(Some(5)))), 2) && !nestedCallArg(Box(Some(Leaf(Some(1)))), 2)
  ensures nestedCallArgIfElse(Box(None), 2) == 0 && nestedCallArgIfElse(Box(Some(Leaf(None))), 2) == 0
  ensures nestedCallArgIfElse(Box(Some(Leaf(Some(5)))), 2) == 1 && nestedCallArgIfElse(Box(Some(Leaf(Some(1)))), 2) == 0
{}
`;
  const ok = verify(output + facts);
  assert.equal(ok.status, 0, output + ok.output);
});

test("Lean passes the narrowed value to the call", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(fixture());
  const output = [typesFile, defFile].filter(f => !!f).map(f => emitLeanFile(f!)).join("\n");
  assert.doesNotMatch(output, /idn o\b/, output);
  assert.doesNotMatch(output, /idn a\.inner/, output);
  assert.doesNotMatch(output, /\ba\.inner\.value\b/, output);
});
