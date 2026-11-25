import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import {
  BOOL_POSITIONS,
  POSITIONS,
  dafnyResolveText,
  renderModule,
  type FnSpec,
} from "../fuzz/narrowing-fuzz.ts";
import {
  SEMANTIC_SCHEMA,
  argToDafny,
  argToJs,
  createSemanticCounts,
  evaluateSemanticCase,
  replaySavedSemanticCase,
  replaySemanticSeedPath,
  runSemanticCampaign,
  validateConcreteArg,
  type BoxInput,
  type ConcreteCallInput,
  type SavedSemanticCase,
} from "../fuzz/semantic-oracle.ts";

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

function makeBox(opts: { inner?: number | "empty" | "absent"; b?: number; v?: number }): BoxInput {
  return {
    inner:
      opts.inner === undefined || opts.inner === "absent"
        ? { kind: "undefined" }
        : opts.inner === "empty"
          ? { kind: "leaf", leaf: { value: { kind: "undefined" } } }
          : { kind: "leaf", leaf: { value: { kind: "number", value: opts.inner } } },
    b: opts.b === undefined ? { kind: "undefined" } : { kind: "number", value: opts.b },
    v: opts.v === undefined ? { kind: "undefined" } : { kind: "number", value: opts.v },
  };
}

test("strict input validation rejects null/undefined mismatches, -0, fractions, and out-of-range ints (#13)", () => {
  assert.equal(validateConcreteArg({ kind: "optional", value: { kind: "undefined" } }, "o"), null);
  assert.equal(validateConcreteArg({ kind: "nullable", value: { kind: "null" } }, "n"), null);
  assert.match(validateConcreteArg({ kind: "optional", value: { kind: "null" } }, "o") ?? "", /cannot accept null/);
  assert.match(validateConcreteArg({ kind: "nullable", value: { kind: "undefined" } }, "n") ?? "", /cannot accept undefined/);
  assert.match(validateConcreteArg({ kind: "number", value: -0 }, "x") ?? "", /-0/);
  assert.match(validateConcreteArg({ kind: "number", value: 1.5 }, "x") ?? "", /safe integer/);
  assert.match(validateConcreteArg({ kind: "number", value: 101 }, "x") ?? "", /outside bounded domain/);

  // Present zero maps explicitly to Option.Some(0), never Option.None.
  assert.equal(argToJs({ kind: "optional", value: { kind: "number", value: 0 } }), 0);
  assert.equal(argToDafny({ kind: "optional", value: { kind: "number", value: 0 } }), "Option.Some(0)");
  assert.equal(argToDafny({ kind: "nullable", value: { kind: "null" } }), "Option.None");
});

test("supported positions on midspiral/main verify on both pre and opt, while #268 returnAnd is caught (#13)", () => {
  // On unmodified midspiral/main (f991de5), 9 of the 13 positions compile cleanly;
  // returnAnd, constAnd, callArg, and ifElse hit open upstream bug midspiral/LemmaScript#268.
  const mainSupportedPositions = POSITIONS.filter(
    p => p !== "returnAnd" && p !== "constAnd" && p !== "callArg" && p !== "ifElse",
  );
  const specs: FnSpec[] = mainSupportedPositions.map((position, idx) => ({
    targets: idx === 0 ? [0] : idx === 1 ? [3, 4] : idx === 2 ? [2] : idx === 3 ? [8] : [0],
    truthy: [false, false, false, false, false, false],
    position,
    use: idx % 5,
    ensures: true, // must be omitted by omitEnsures in semantic mode
  }));

  const tsText = renderModule(specs, { omitEnsures: true });
  assert.ok(!tsText.includes("//@ ensures"), "semantic-mode source must omit arbitrary //@ ensures");

  const inputs: ConcreteCallInput[] = [
    // f0: returnOr (boolean) on single optional o
    { fn: "f0", paramNames: ["x", "o"], args: [{ kind: "number", value: 5 }, { kind: "optional", value: { kind: "undefined" } }] },
    { fn: "f0", paramNames: ["x", "o"], args: [{ kind: "number", value: -5 }, { kind: "optional", value: { kind: "number", value: 3 } }] },
    // f1: ifThen on colliding names a_b and a.b with distinct values + zero cases
    {
      fn: "f1",
      paramNames: ["x", "a", "a_b"],
      args: [{ kind: "number", value: 5 }, { kind: "box", box: makeBox({ b: 7 }) }, { kind: "optional", value: { kind: "number", value: 3 } }],
    },
    {
      fn: "f1",
      paramNames: ["x", "a", "a_b"],
      args: [{ kind: "number", value: -5 }, { kind: "box", box: makeBox({ b: 0 }) }, { kind: "optional", value: { kind: "number", value: 0 } }],
    },
    // f2: ternaryBool on nullable n (null, present 0, present negative)
    { fn: "f2", paramNames: ["x", "n"], args: [{ kind: "number", value: 0 }, { kind: "nullable", value: { kind: "null" } }] },
    { fn: "f2", paramNames: ["x", "n"], args: [{ kind: "number", value: -3 }, { kind: "nullable", value: { kind: "number", value: 0 } }] },
    { fn: "f2", paramNames: ["x", "n"], args: [{ kind: "number", value: -10 }, { kind: "nullable", value: { kind: "number", value: -4 } }] },
    // f3: ternaryValue on box.inner.value (absent box, absent inner, absent value, present value)
    { fn: "f3", paramNames: ["x", "box"], args: [{ kind: "number", value: 1 }, { kind: "optional-box", value: { kind: "undefined" } }] },
    { fn: "f3", paramNames: ["x", "box"], args: [{ kind: "number", value: 1 }, { kind: "optional-box", value: { kind: "box", box: makeBox({ inner: "absent" }) } }] },
    { fn: "f3", paramNames: ["x", "box"], args: [{ kind: "number", value: 1 }, { kind: "optional-box", value: { kind: "box", box: makeBox({ inner: "empty" }) } }] },
    { fn: "f3", paramNames: ["x", "box"], args: [{ kind: "number", value: -2 }, { kind: "optional-box", value: { kind: "box", box: makeBox({ inner: 5 }) } }] },
  ];

  // Remaining supported positions f4..f8 (absent, present 0, present negative/positive)
  for (let i = 4; i < mainSupportedPositions.length; i++) {
    inputs.push(
      { fn: `f${i}`, paramNames: ["x", "o"], args: [{ kind: "number", value: 4 }, { kind: "optional", value: { kind: "undefined" } }] },
      { fn: `f${i}`, paramNames: ["x", "o"], args: [{ kind: "number", value: -2 }, { kind: "optional", value: { kind: "number", value: 0 } }] },
      { fn: `f${i}`, paramNames: ["x", "o"], args: [{ kind: "number", value: -5 }, { kind: "optional", value: { kind: "number", value: 9 } }] },
    );
  }

  const returnKinds = new Map<string, "boolean" | "number">(
    mainSupportedPositions.map((p, i) => [`f${i}`, BOOL_POSITIONS.has(p) ? "boolean" : "number"]),
  );

  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-sem13-allpos-"));
  try {
    const project = makeProject();
    const counts = createSemanticCounts();
    const outcome = evaluateSemanticCase(tsText, inputs, returnKinds, { project, workDir, counts });
    assert.equal(outcome.ok, true, `${outcome.signature}\n${outcome.detail}`);
    assert.equal(counts.comparisonsAttempted, inputs.length);
    assert.equal(counts.comparisonsCompleted, inputs.length);
    assert.equal(counts.pre.completed, 1);
    assert.equal(counts.opt.completed, 1);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("negative controls: wrong boolean and wrong integer expected values fail verification (#13)", () => {
  const specs: FnSpec[] = [
    { targets: [0], truthy: [false, false, false, false, false, false], position: "returnOr", use: 0, ensures: false },
    { targets: [0], truthy: [false, false, false, false, false, false], position: "ifValue", use: 0, ensures: false },
  ];
  const tsText = renderModule(specs, { omitEnsures: true });
  const returnKinds = new Map<string, "boolean" | "number">([["f0", "boolean"], ["f1", "number"]]);

  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-sem13-neg-"));
  try {
    const project = makeProject();
    // Boolean wrong-value control
    const boolCounts = createSemanticCounts();
    const boolRes = evaluateSemanticCase(
      tsText,
      [{ fn: "f0", paramNames: ["x", "o"], args: [{ kind: "number", value: 2 }, { kind: "optional", value: { kind: "number", value: 5 } }] }],
      returnKinds,
      { project, workDir, counts: boolCounts },
      { overrideExpected: (_fn, _idx, exp) => ({ kind: "boolean", value: !(exp as { kind: "boolean"; value: boolean }).value }) },
    );
    assert.equal(boolRes.ok, false);
    assert.equal(boolRes.oracle, "semantic-both");
    assert.equal(boolRes.stage, "both");
    assert.equal(boolCounts.comparisonsCompleted, 0);
    assert.ok(boolRes.failedAssertions?.some(f => f.fn === "f0" && f.stage === "pre"));
    assert.ok(boolRes.failedAssertions?.some(f => f.fn === "f0" && f.stage === "opt"));

    // Integer wrong-value control
    const intCounts = createSemanticCounts();
    const intRes = evaluateSemanticCase(
      tsText,
      [{ fn: "f1", paramNames: ["x", "o"], args: [{ kind: "number", value: 2 }, { kind: "optional", value: { kind: "number", value: 5 } }] }],
      returnKinds,
      { project, workDir, counts: intCounts },
      { overrideExpected: (_fn, _idx, exp) => ({ kind: "number", value: (exp as { kind: "number"; value: number }).value + 1 }) },
    );
    assert.equal(intRes.ok, false);
    assert.equal(intRes.oracle, "semantic-both");
    assert.equal(intRes.stage, "both");
    assert.equal(intCounts.comparisonsCompleted, 0);
    assert.ok(intRes.failedAssertions?.some(f => f.fn === "f1" && f.assertion.includes("== 6")));
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("historical bug control: detects midspiral/LemmaScript#230 wrong-value binder collision while Dafny resolves (#13)", () => {
  // Source combining colliding names `a_b` and `a.b`.
  const tsText = renderModule([
    { targets: [3, 4], truthy: [false, false, false, false, false, false], position: "ifValue", use: 0, ensures: false },
  ], { omitEnsures: true });

  const input: ConcreteCallInput = {
    fn: "f0",
    paramNames: ["x", "a", "a_b"],
    args: [
      { kind: "number", value: 0 },
      { kind: "box", box: makeBox({ b: 7 }) },
      { kind: "optional", value: { kind: "number", value: 3 } },
    ],
  };
  const returnKinds = new Map<string, "boolean" | "number">([["f0", "number"]]);

  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-sem13-230-"));
  try {
    const project = makeProject();

    // 1. Corrected compiler verifies expected value 10 (3 + 7) on both pre and opt.
    const cleanCounts = createSemanticCounts();
    const cleanRes = evaluateSemanticCase(tsText, [input], returnKinds, { project, workDir, counts: cleanCounts });
    assert.equal(cleanRes.ok, true, `${cleanRes.signature}\n${cleanRes.detail}`);
    assert.equal(cleanRes.checks[0].expected.value, 10);

    // 2. Controlled test-only reintroduction of #230: collapse the outer `a_b`
    // binder (`i_a_b_val'`) onto the inner `a.b` binder (`i_a_b_val`) so both
    // operands read the shadowed inner binder (returning 7 + 7 = 14 instead of
    // 3 + 7 = 10), while still resolving cleanly in Dafny with 0 errors.
    const introduce230 = (dfy: string): string => {
      const m = dfy.match(/case Some\(([^)]+)\) =>\s*match a\.b\s*\{\s*case Some\(([^)]+)\) =>/);
      assert.ok(m, `Expected nested Some(a_b) / match a.b Some(...) pattern in generated Dafny:\n${dfy}`);
      const [, outerBinder, innerBinder] = m;
      assert.notEqual(outerBinder, innerBinder, "fixed compiler must use distinct binders");
      return dfy.replaceAll(outerBinder, innerBinder);
    };

    // Confirm the mutated Dafny still resolves with 0 resolution/type errors.
    const mutatedPre = introduce230(cleanRes.preDfy!);
    const resolved = dafnyResolveText(mutatedPre, workDir, "pre");
    assert.equal(resolved.status, "ok", `mutated #230 Dafny must still resolve: ${resolved.detail}`);

    // Confirm the semantic oracle catches the wrong-value bug independently of checkNarrowedModule.
    const bugCounts = createSemanticCounts();
    const bugRes = evaluateSemanticCase(
      tsText,
      [input],
      returnKinds,
      { project, workDir, counts: bugCounts },
      {
        postEmitPreSemantic: introduce230,
        postEmitOptSemantic: introduce230,
      },
    );
    assert.equal(bugRes.ok, false);
    assert.equal(bugRes.oracle, "semantic-both");
    assert.equal(bugRes.stage, "both");
    assert.equal(bugRes.checks[0].expected.value, 10);
    assert.ok(bugRes.failedAssertions?.some(f => f.fn === "f0" && f.assertion.includes("== 10")));
    assert.doesNotMatch(bugRes.detail ?? "", /resolution\/type errors/);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("shrinking preserves semantic-opt stage and saved/seed-path replay reproduce without reshrinking (#13)", () => {
  const outDir = mkdtempSync(path.join(tmpdir(), "lsc-sem13-shrink-"));
  // Controlled optimization-only semantic defect: perturb the fallback `0` return
  // in optimized `ifThen` output only (`case None => 0` / `else 0` -> `99`).
  const optOnlyDefect = (optDfy: string) =>
    optDfy.replace(/(else|case None =>)\s+0\b/g, "$1\n        99");
  try {
    const summary = runSemanticCampaign({
      seed: 1,
      runs: 12,
      classes: 1,
      inputsPerFn: 2,
      positions: ["ifThen"],
      minutes: 2,
      out: outDir,
      hooks: { postEmitOptimized: optOnlyDefect },
    });
    assert.equal(summary.failureClasses, 1);
    assert.equal(summary.saved.length, 1);
    const saved = summary.saved[0];
    assert.equal(saved.schema, SEMANTIC_SCHEMA);
    assert.equal(saved.oracle, "semantic-opt");
    assert.equal(saved.stage, "opt");
    assert.ok(existsSync(path.join(outDir, "1.ts")));
    assert.ok(existsSync(path.join(outDir, "1.pre.semantic.dfy")));
    assert.ok(existsSync(path.join(outDir, "1.opt.semantic.dfy")));
    assert.ok(existsSync(path.join(outDir, "1.semantic.json")));

    // Verify saved JSON preserves explicit missing-value tags and tool versions.
    const rawJson = JSON.parse(readFileSync(path.join(outDir, "1.semantic.json"), "utf8")) as SavedSemanticCase;
    assert.equal(rawJson.oracle, "semantic-opt");
    assert.ok(rawJson.versions.node.startsWith("v"));
    assert.ok(rawJson.versions.dafny.length > 0);
    assert.deepEqual(rawJson.generatorOptions.intRange, [-100, 100]);

    // Saved-case replay reproduces the exact semantic-opt failure with the defect, and passes without it.
    const replayedFail = replaySavedSemanticCase(path.join(outDir, "1.semantic.json"), {
      postEmitOptimized: optOnlyDefect,
    });
    assert.equal(replayedFail.ok, false);
    assert.equal(replayedFail.oracle, "semantic-opt");
    assert.equal(replayedFail.stage, "opt");

    const replayedClean = replaySavedSemanticCase(path.join(outDir, "1.semantic.json"));
    assert.equal(replayedClean.ok, true, `${replayedClean.signature}\n${replayedClean.detail}`);

    // Seed/path replay reproduces the exact semantic-opt failure.
    const seedReplay = replaySemanticSeedPath({
      seed: saved.seed,
      path: saved.path,
      runs: 12,
      inputsPerFn: 2,
      positions: ["ifThen"],
      hooks: { postEmitOptimized: optOnlyDefect },
    });
    assert.equal(seedReplay.passed, false);
    assert.equal(seedReplay.outcome?.oracle, "semantic-opt");
  } finally {
    rmSync(outDir, { recursive: true, force: true });
  }
});

test("timeouts cannot become successful semantic comparisons (#13)", () => {
  const tsText = renderModule([
    { targets: [0], truthy: [false, false, false, false, false, false], position: "ifValue", use: 0, ensures: false },
  ], { omitEnsures: true });
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-sem13-timeout-"));
  try {
    const project = makeProject();
    const counts = createSemanticCounts();
    const res = evaluateSemanticCase(
      tsText,
      [{ fn: "f0", paramNames: ["x", "o"], args: [{ kind: "number", value: 1 }, { kind: "optional", value: { kind: "number", value: 2 } }] }],
      new Map([["f0", "number"]]),
      { project, workDir, counts },
      {
        verifyDafny: (_dfy, stage) =>
          stage === "opt"
            ? { status: "timeout", verifiedCount: 0, errorCount: 0, failedLemmas: [], output: "timed out" }
            : { status: "ok", verifiedCount: 1, errorCount: 0, failedLemmas: [], output: "Dafny program verifier finished with 1 verified, 0 errors" },
      },
    );
    assert.equal(res.ok, false);
    assert.equal(res.oracle, "timeout");
    assert.equal(res.stage, "opt");
    assert.equal(counts.comparisonsCompleted, 0);
    assert.equal(counts.pre.completed, 1);
    assert.equal(counts.opt.completed, 0);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
