import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  belowOrUnset, atMostOrUnset, aboveOrUnset, atLeastOrUnset, optionalOnLeft,
} from "../fixtures/optional-comparison-order.ts";
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
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/optional-comparison-order.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

// Each fixture function has an unguarded `x op opt` contract line. The
// optional-comparison rule binds the matched value on the left, so it must
// become `v op' x` with the operator mirrored; `opt op x` keeps it.
const expected: [string, string][] = [
  ["belowOrUnset", ">"], ["atMostOrUnset", ">="], ["aboveOrUnset", "<"], ["atLeastOrUnset", "<="], ["optionalOnLeft", ">"],
];

// The bodies guard the comparison with `opt === null ||`, which narrows `opt`,
// so they read the binder directly with the source operator.
const bodies: [string, string][] = [
  ["belowOrUnset", "x < i_opt_val"], ["atMostOrUnset", "x <= i_opt_val"], ["aboveOrUnset", "x > i_opt_val"],
  ["atLeastOrUnset", "x >= i_opt_val"], ["optionalOnLeft", "i_opt_val > x"],
];

const LEAN_OP: Record<string, string> = { ">=": "≥", "<=": "≤" };

function bodyOf(text: string, header: string): string {
  const start = text.indexOf(header);
  assert.ok(start >= 0, `missing ${header}`);
  const next = text.slice(start + 1).search(/\n(?:function|lemma|def|method) /);
  return next < 0 ? text.slice(start) : text.slice(start, start + 1 + next);
}

test("comparisons with an optional on the right keep their runtime meaning", () => {
  assert.equal(belowOrUnset(1, 5), true);
  assert.equal(belowOrUnset(5, 1), false);
  assert.equal(atMostOrUnset(5, 5), true);
  assert.equal(aboveOrUnset(5, 1), true);
  assert.equal(atLeastOrUnset(4, 5), false);
  assert.equal(optionalOnLeft(1, 5), true);
});

test("Dafny mirrors the operator when the optional is on the right", () => {
  const { typesFile, defFile } = transformModuleDafny(fixture());
  const text = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  for (const [name, op] of expected) {
    assert.ok(bodyOf(text, `lemma ${name}_ensures(`).includes(`(i_value ${op} x)`), name);
  }
  for (const [name, cmp] of bodies) {
    assert.ok(bodyOf(text, `function ${name}(`).includes(`(${cmp})`), name);
  }
});

test("Lean mirrors the operator when the optional is on the right", () => {
  resetLeanModule();
  const { defFile } = transformModuleLean(fixture());
  const text = emitLeanFile(defFile);
  for (const [name, op] of expected) {
    assert.ok(bodyOf(text, `method ${name} `).includes(`_value ${LEAN_OP[op] ?? op} x`), name);
  }
});
