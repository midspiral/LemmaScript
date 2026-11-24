import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { peepholeModule } from "../src/peephole.ts";
import * as runtime from "../fixtures/optional-assignment-narrowing.ts";
import * as unions from "../fixtures/optional-union-guard.ts";
import * as lookups from "../fixtures/optional-lookup-bindings.ts";

const fixture = readFileSync(new URL("../fixtures/optional-assignment-narrowing.ts", import.meta.url), "utf8");
const lookupFixture = readFileSync(new URL("../fixtures/optional-lookup-bindings.ts", import.meta.url), "utf8");
const rejectedCall = `
function rejected(): number {
  //@ requires false
  let value = 0;
  value++;
  return value;
}
`;
const skippedCalls = rejectedCall + `
export function orDefault(value: number | undefined): number {
  //@ requires value === 3
  //@ ensures \\result === 3
  return value || rejected();
}
export function nullishDefault(value: number | undefined): number {
  //@ requires value === 0
  //@ ensures \\result === 0
  return value ?? rejected();
}
export function andValue(value: number | undefined): number | undefined {
  //@ requires value === undefined
  //@ ensures \\result === undefined
  return value && rejected();
}
export function optionalCall(values: number[] | undefined): boolean | undefined {
  //@ requires values === undefined
  //@ ensures \\result === undefined
  return values?.includes(rejected());
}
export function skippedMutation(): number {
  //@ ensures \\result === 0
  const values = new Map<string, number[]>();
  values.get("missing")?.push(rejected());
  return values.size;
}
`;
const requiredComparison = rejectedCall + `
export function compareOptional(value: number | undefined): boolean {
  //@ requires value === undefined
  return value === rejected();
}
`;
const absentReads = [
  "export function readAbsent(p: number | undefined): number { return p!; }",
  'export function readMissingKey(values: Map<string, number>): number { return values.get("missing")!; }',
];
const specHelpers = `
export function helperArgument(value: number | undefined): boolean {
  //@ ensures \\result === (value !== undefined && narrowingPositive(value!))
  return value !== undefined && value > 0;
}
export function helperConjunction(value: number): boolean {
  //@ ensures \\result === (narrowingPositive(value) && narrowingPositive(value + 1) && narrowingPositive(value + 2))
  return value > 0;
}
export function helperComparison(value: number | undefined): boolean {
  //@ ensures \\result === (value === narrowingZero())
  return value === 0;
}
`;
const dafnyHelpers = `
ghost predicate narrowingPositive(value: int) { value > 0 }
ghost function narrowingZero(): int { 0 }
`;
const leanHelpers = `
def narrowingPositive (value : Int) : Bool := decide (value > 0)
def narrowingZero : Int := 0
`;

function typed(text: string, strictNullChecks = true) {
  const project = new Project({ compilerOptions: {
    strict: true, strictNullChecks, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("optional-assignment.ts", text);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return narrowModule(resolveModule(extractModule(source)));
}

function generate(text: string, strictNullChecks = true): string {
  const { typesFile, defFile } = transformModuleDafny(typed(text, strictNullChecks));
  return emitDafnyFile(peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "dafny"));
}

function verify(text: string, strictNullChecks = true, helpers = "") {
  const dir = mkdtempSync(join(tmpdir(), "lsc-optional-assignment-"));
  try {
    const path = join(dir, "test.dfy");
    writeFileSync(path, helpers + generate(text, strictNullChecks));
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=10", path],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("optional assignment narrowing agrees with JavaScript, including later absent writes", () => {
  for (const flag of [false, true]) {
    for (const fn of [runtime.coalescedNull, runtime.coalescedUndefined, runtime.conditionalReset]) {
      assert.equal(fn(flag), flag ? 7 : 5);
    }
    assert.equal(runtime.optionalFallback(flag), flag ? 5 : undefined);
  }
  assert.equal(runtime.repeatedWrites(), 8);
  assert.equal(runtime.compoundWrites(), 10);
  assert.equal(runtime.nestedReads(), 8);
  assert.equal(runtime.reassignedParameter(3), 7);
  assert.equal(runtime.clearAfterGuard(3), 9);
  assert.equal(runtime.clearAfterGuard(undefined), 9);
  assert.equal(runtime.mutateOptionalArray(), 1);
  assert.equal(runtime.mutateOptionalField(), 2);
  assert.equal(runtime.optionalLoop(), 9);
  assert.equal(runtime.mutateOptionalChain(), 2);
  assert.equal(runtime.mutateLookupArray(), 2);
  assert.equal(runtime.replaceParent(), 9);
  assert.equal(runtime.updateOptionalRecord(), 9);
  assert.equal(runtime.optionalBuiltinArgument(), 3);
  assert.equal(runtime.spreadOptional(), 3);
  assert.equal(runtime.optionalCountdown(), 0);
  assert.equal(runtime.optionalForOf(), 7);
  assert.equal(runtime.clearIterable(), 2);
  assert.equal(runtime.falsyValues(), 9);
  assert.equal(runtime.optionalTag(undefined), false);
  assert.equal(runtime.optionalTag({ type: "compaction" }), false);
  assert.equal(runtime.optionalTag({ type: "message", value: 7 }), true);
  assert.deepEqual(runtime.guardedCallback(3), [4, 5]);
  assert.deepEqual(runtime.guardedCallback(undefined), []);
  assert.equal(runtime.guardedCell(undefined), 7);
  for (const value of [-1, 0, 5]) assert.equal(runtime.guardedCell({ value }), value < 0 ? 7 : value);
  const result = verify(fixture);
  assert.equal(result.status, 0, result.output);
});

test("an optional guard executes before a union check on its payload", () => {
  for (const fn of [unions.optionalUnion, unions.optionalUnionTernary]) {
    assert.equal(fn(undefined), 0);
    assert.equal(fn({ values: 7 }), 0);
    assert.equal(fn({ values: [1, 2] }), 2);
  }
  const text = readFileSync(new URL("../fixtures/optional-union-guard.ts", import.meta.url), "utf8");
  const result = verify(text);
  assert.equal(result.status, 0, result.output);
});

for (const strictNullChecks of [true, false]) {
  test(`lookup bindings preserve absence with strictNullChecks=${strictNullChecks}`, () => {
    assert.equal(lookups.guardedLookup({}, "missing"), -1);
    assert.equal(lookups.guardedLookup({ present: 5 }, "present"), 5);
    assert.equal(lookups.annotatedLookup({}, "missing"), 7);
    assert.equal(lookups.annotatedLookup({ present: 5 }, "present"), 5);
    assert.deepEqual(lookups.lastMatch([], 7), { value: 7 });
    const last = { value: 7 };
    assert.equal(lookups.lastMatch([{ value: 7 }, { value: 5 }, last], 7), last);
    const result = verify(lookupFixture, strictNullChecks);
    assert.equal(result.status, 0, result.output);
  });
}

test("assignment narrowing does not prove a false postcondition", () => {
  const result = verify(fixture.replace("flag ==> \\result === 7", "flag ==> \\result === 5"));
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /postcondition could not be proved/);
  assert.doesNotMatch(result.output, /resolution\/type errors|timed out/);
});

test("a non-null assertion still requires the optional to be present", () => {
  for (const source of absentReads) {
    const result = verify(source);
    assert.notEqual(result.status, 0, result.output);
    assert.match(result.output, /destructor.*value/);
    assert.doesNotMatch(result.output, /resolution\/type errors|timed out/);
  }
});

test("defaults and short-circuit expressions keep calls in the selected branch", () => {
  const result = verify(skippedCalls);
  assert.equal(result.status, 0, result.output);
});

test("both operands of an optional comparison execute, even when the optional is absent", () => {
  for (const text of [requiredComparison, requiredComparison.replace("value === rejected()", "rejected() === value")]) {
    const result = verify(text);
    assert.notEqual(result.status, 0, result.output);
    assert.match(result.output, /precondition.*(?:proved|hold)|could not prove.*precondition/);
    assert.doesNotMatch(result.output, /resolution|type errors|timed out/);
  }
});

test("a guard does not justify a payload read after clearing storage", () => {
  const result = verify(`export function cleared(value: number | undefined): number {
    if (value !== undefined) { value = undefined; return value!; }
    return 0;
  }`);
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /destructor.*value/);
  assert.doesNotMatch(result.output, /resolution|type errors|timed out/);
});

test("optional mutations without a modeled write-back are rejected", () => {
  for (const operation of ["values.pop()", "values.shift()", "values?.pop()", "values?.shift()", "values.push(3)", "values?.push(3)"]) {
    const source = `export function unsupported(values: number[] | undefined): number | undefined {
      if (values === undefined) return 0;
      return ${operation};
    }`;
    assert.throws(() => generate(source), /storage update|mutation through optional storage/);
    assert.throws(() => transformModuleLean(typed(source)), /storage update|mutation through optional storage/);
  }
});

test("an evolving inferred local requires a storage annotation", () => {
  assert.throws(() => generate(`export function evolving(): number {
    let value;
    value = 7;
    return value;
  }`), /stable storage type.*explicit type annotation/);
});

test("backend specification helpers infer saved values and accept checked payload arguments", () => {
  const result = verify(specHelpers, true, dafnyHelpers);
  assert.equal(result.status, 0, result.output);
  const falseClaim = verify(specHelpers.replace("return value > 0;", "return value >= 0;"), true, dafnyHelpers);
  assert.notEqual(falseClaim.status, 0, falseClaim.output);
  assert.match(falseClaim.output, /postcondition could not be proved/);
  assert.doesNotMatch(falseClaim.output, /resolution\/type errors|timed out/);
});

test("Lean proves optional assignment narrowing and rejects an absent payload", {
  skip: !existsSync(new URL("../../.lake/build/lib/lean/LemmaScript/Option.olean", import.meta.url)),
}, () => {
  const dir = mkdtempSync(join(tmpdir(), "lsc-optional-assignment-lean-"));
  try {
    for (const [text, valid] of [
      [fixture, true],
      [lookupFixture.slice(0, lookupFixture.indexOf("interface Cell")), true],
      [skippedCalls, true],
      [specHelpers, true],
      [specHelpers.replace("return value > 0;", "return value >= 0;"), false],
      [requiredComparison, false],
      [fixture.replace("flag ==> \\result === 7", "flag ==> \\result === 5"), false],
      [`export function cleared(value: number | undefined): number {
        if (value !== undefined) { value = undefined; return value!; }
        return 0;
      }`, false],
      ...absentReads.map(source => [source, false] as const),
    ] as const) {
      const mod = typed(text);
      const { typesFile, defFile } = transformModuleLean(mod);
      resetLeanModule();
      const output = emitLeanFile({ ...defFile, imports: ["LemmaScript"],
        decls: [...(typesFile?.decls ?? []), ...defFile.decls] })
        .replace("import LemmaScript\n", "import LemmaScript\n" + leanHelpers);
      // Normalize specification lets before Velvet compares the helper contracts.
      const proofs = mod.functions.map(f => f.name.startsWith("helper") ? `
prove_correct ${f.name} by
  simp only []
  velvet_vcgen [${f.name}] with finish [Pure.${f.name}, narrowingPositive, narrowingZero]
` : f.name === "optionalTag" ? `
prove_correct optionalTag by
  velvet_vcgen [optionalTag] with
    (expose_names
     tactic =>
       cases entry with
       | none => simp [Pure.optionalTag]
       | some value => cases value <;> simp [Pure.optionalTag, TaggedEntry_type])
` : f.name === "optionalCountdown" ? `
prove_correct optionalCountdown by
  velvet_vcgen [optionalCountdown] with
    (expose_names
     tactic =>
       try have positive : 0 < a := by simpa [h] using h_loop
       try cases value
       all_goals simp_all [Option.isSome] <;> omega)
` : `prove_correct ${f.name} by\n  velvet_vcgen [${f.name}] with finish${f.name === "falsyValues" ? " [String.length_eq_zero_iff]" : f.name === "mutateLookupArray" ? " [Array.size_append]" : ""}\n`).join("\n");
      const path = join(dir, "Assignments.lean");
      const callbackValues = text === fixture ? `
example (value : Int) : guardedCallback (some value) = some #[1 + value, 2 + value] := by
  simp [guardedCallback, LemmaScript.optionValue, Array.mapM_eq_mapM_toList]
` : "";
      writeFileSync(path, output + "\n" + proofs + callbackValues);
      const result = spawnSync("lake", ["env", "lean", path], {
        cwd: fileURLToPath(new URL("../../", import.meta.url)), encoding: "utf8", timeout: 60_000,
      });
      assert.ifError(result.error);
      const log = result.stdout + result.stderr;
      assert.equal(result.status === 0, valid, log + output);
      if (!valid) assert.match(log, /unsolved goals|`finish` failed/);
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
