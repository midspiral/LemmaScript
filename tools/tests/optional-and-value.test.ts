import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  belowSet, nullable, arithmetic, both, field, inContract,
  unsetOrAbove, zeroOrAbove, orEarlyReturn, orTernary, andIfElse, lowest, countAbove,
} from "../fixtures/optional-and-value.ts";
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
  const source = project.addSourceFileAtPath(fileURLToPath(new URL("../fixtures/optional-and-value.ts", import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function bodyOf(text: string, header: string): string {
  const start = text.indexOf(header);
  assert.ok(start >= 0, `missing ${header}`);
  const next = text.slice(start + 1).search(/\n(?:function|lemma|def|method) /);
  return next < 0 ? text.slice(start) : text.slice(start, start + 1 + next);
}

// The narrowed value is read through the match binder, never as the optional:
// after `x !== undefined &&` and after `x === undefined ||` (or `!x ||`).
// (`lowest` only compares its optional, so it keeps the comparison lowering.)
const expected: [string, string, string][] = [
  ["belowSet", "x < i_opt_val", "x < _opt_val"],
  ["nullable", "x < i_opt_val", "x < _opt_val"],
  ["arithmetic", "(i_opt_val + 1) > x", "_opt_val + 1 > x"],
  ["both", "x < (i_a_val + i_b_val)", "x < _a_val + _b_val"],
  ["field", "i_box_v_val > 0", "_box_v_val > 0"],
  ["unsetOrAbove", "(i_opt_val + 1) > x", "_opt_val + 1 > x"],
  ["zeroOrAbove", "(i_opt_val + 1) > x", "_opt_val + 1 > x"],
  ["orEarlyReturn", "(i_opt_val + 1) > x", "_opt_val + 1 > x"],
  ["orTernary", "(i_opt_val + 1) > x", "_opt_val + 1 > x"],
  ["andIfElse", "(i_opt_val + 1) > x", "_opt_val + 1 > x"],
];

test("a presence check guards the rest of an && value at runtime", () => {
  assert.equal(belowSet(1, 5), true);
  assert.equal(belowSet(1), false);
  assert.equal(nullable(1, null), false);
  assert.equal(arithmetic(5, 5), true);
  assert.equal(both(1, 1, 1), true);
  assert.equal(both(1, 1), false);
  assert.equal(field({ v: 0 }), false);
  assert.equal(inContract(1, 5), true);
  assert.equal(unsetOrAbove(6), true);
  assert.equal(unsetOrAbove(6, 5), false);
  assert.equal(zeroOrAbove(6, 0), true);
  assert.equal(orEarlyReturn(6, 5), 0);
  assert.equal(orTernary(6), 1);
  assert.equal(andIfElse(5, 5), 1);
  assert.deepEqual([lowest([]), lowest([3, 1, 2])], [null, 1]);
  assert.deepEqual([countAbove([1, 5, 9]), countAbove([1, 5, 9], 4)], [3, 2]);
});

test("Lean decides a match used as an if condition as a Bool", () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(fixture());
  assert.ok(typesFile);
  assert.ok(bodyOf(emitLeanFile(typesFile), "def orTernary ").includes("| .none => true) : Bool) then"));
  assert.ok(bodyOf(emitLeanFile(defFile), "method countAbove ").includes("| .none => true) : Bool) then"));
});

test("Dafny binds the narrowed optional in an && value", () => {
  const { typesFile, defFile } = transformModuleDafny(fixture());
  const text = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  for (const [name, dafny] of expected) {
    assert.ok(bodyOf(text, `function ${name}(`).includes(dafny), name);
  }
});

test("Lean binds the narrowed optional in an && value", () => {
  resetLeanModule();
  const { typesFile } = transformModuleLean(fixture());
  assert.ok(typesFile);
  const text = emitLeanFile(typesFile);
  for (const [name, , lean] of expected) {
    assert.ok(bodyOf(text, `def ${name} `).includes(lean), name);
  }
});
