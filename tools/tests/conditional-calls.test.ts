import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  checkedIncrement, chooseThen, chooseElse, chooseBoth, guardedAnd, guardedOr,
  nestedChoice, choiceArgument, optionalChoice,
} from "../../examples/conditionalCalls.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import type { Stmt } from "../src/ir.ts";

function fixture(source?: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = source === undefined
    ? project.addSourceFileAtPath(fileURLToPath(new URL("../../examples/conditionalCalls.ts", import.meta.url)))
    : project.createSourceFile("conditional.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

test("source calls only the selected branch, including nested and optional results", () => {
  assert.throws(() => checkedIncrement(false, 0), /unselected call/);
  for (const enabled of [false, true]) {
    assert.equal(chooseThen(enabled), enabled ? 1 : -1);
    assert.equal(chooseElse(enabled), enabled ? -1 : 1);
    assert.equal(chooseBoth(enabled), enabled ? 1 : 2);
    assert.equal(guardedAnd(enabled), enabled);
    assert.equal(guardedOr(enabled), true);
    assert.equal(choiceArgument(enabled), enabled ? 2 : 0);
    assert.equal(optionalChoice(enabled), enabled ? 1 : undefined);
    for (const second of [false, true])
      assert.equal(nestedChoice(enabled, second), enabled ? second ? 1 : 2 : 3);
  }
});

// Inspect both backends' statement trees: every call must stay under a guard,
// and each source call must appear exactly once (even if its arm is nested).
function callDepths(stmts: Stmt[], depth = 0): number[] {
  return stmts.flatMap(s => {
    if (s.kind === "let-bind" && s.value.kind === "app" && s.value.fn === "checkedIncrement") return [depth];
    if (s.kind === "if") return [...callDepths(s.then, depth + 1), ...callDepths(s.else, depth + 1)];
    return [];
  });
}

for (const [backend, transform] of [["Dafny", transformModuleDafny], ["Lean", transformModuleLean]] as const) {
  test(`${backend} keeps lifted calls under their source guards`, () => {
    const { defFile } = transform(fixture());
    for (const [name, depths] of [
      ["chooseThen", [1]], ["chooseElse", [1]], ["chooseBoth", [1, 1]],
      ["guardedAnd", [1]], ["guardedOr", [1]], ["nestedChoice", [2, 2, 1]],
      ["choiceArgument", [1, 0]], ["optionalChoice", [1]],
    ] as const) {
      const method = defFile.decls.find(d => d.kind === "method" && d.name === name);
      assert.ok(method?.kind === "method", name);
      assert.deepEqual(callDepths(method.body), depths, name);
    }
  });

  test(`${backend} evaluates the left call once before selecting the right call`, () => {
    const mod = fixture(`
      function checkedIncrement(enabled: boolean): boolean {
        let value = enabled; value = !value; return !value;
      }
      export function condition(enabled: boolean): boolean {
        return checkedIncrement(enabled) && checkedIncrement(enabled);
      }
    `);
    const method = transform(mod).defFile.decls.find(d => d.kind === "method" && d.name === "condition");
    assert.ok(method?.kind === "method");
    assert.deepEqual(callDepths(method.body), [0, 1]);
  });
}

test("a negative conditional arm is stored as an integer", () => {
  const { defFile } = transformModuleDafny(fixture());
  const text = emitDafnyFile(defFile);
  assert.match(text, /var i_branch\d+: int := \*/);
  assert.doesNotMatch(text, /var i_branch\d+: nat/);
  resetLeanModule();
  const lean = emitLeanFile(transformModuleLean(fixture()).defFile);
  assert.match(lean, /let mut _branch\d+ : Int/);
  assert.doesNotMatch(lean, /let mut _branch\d+ : Nat/);
});

test("new temporary names cannot capture source bindings", () => {
  const mod = fixture(`
    function next(enabled: boolean): boolean { let n = 0; n += 1; return enabled; }
    export function choose(_branch0: boolean): boolean { return _branch0 && next(_branch0); }
  `);
  const method = transformModuleDafny(mod).defFile.decls.find(d => d.kind === "method" && d.name === "choose");
  assert.ok(method?.kind === "method");
  const temps = method.body.filter(s => s.kind === "let");
  assert.ok(temps.length > 0);
  assert.ok(temps.every(s => s.name !== "_branch0"));
});
