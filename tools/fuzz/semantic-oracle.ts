/**
 * Bounded semantic-comparison oracle for the narrowing fuzzer (`robertpenner/LemmaScript#13`).
 *
 * Generates concrete finite safe-integer inputs (with explicit absent/present
 * optional and nullable encodings), executes the generated TypeScript
 * independently of LemmaScript's IR/emitters to obtain expected boolean or
 * integer results, and asks `dafny verify` to verify those concrete result
 * assertions against both pre-optimization and production-optimized Dafny
 * produced by `compileDafnyVariants` (`robertpenner/LemmaScript#12`).
 *
 * Input domain:
 *   - Integer range: [-100, 100] (negative, zero, positive, distinct values for
 *     colliding names such as `a_b` and `a.b`). Every generated expression in
 *     `renderFn` (`t1 + t2`, `+ 1`, `- x`, `* 2`) stays within [-400, 400],
 *     strictly inside exact JavaScript safe integers with no fractions, no
 *     non-finite numbers, and no `-0`.
 *   - Optional `number` (`o?`, `p?`, `a_b?`, `Leaf.value?`, `Box.b?`, `Box.v?`):
 *     `{ kind: "undefined" }` -> JS `undefined` -> Dafny `Option.None`;
 *     `{ kind: "number", value }` -> JS `value` -> Dafny `Option.Some(value)`.
 *   - Nullable `number | null` (`n`):
 *     `{ kind: "null" }` -> JS `null` -> Dafny `Option.None`;
 *     `{ kind: "number", value }` -> JS `value` -> Dafny `Option.Some(value)`.
 *   - Required `Box` (`a`): Dafny `Box(inner, b, v)` with optional `Leaf` / `int` fields.
 *   - Optional `Box` (`box?`): `{ kind: "undefined" }` -> JS `undefined` -> Dafny `Option.None`;
 *     `{ kind: "box", box }` -> JS `{ ... }` -> Dafny `Option.Some(Box(...))`.
 */

import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import vm from "node:vm";
import fc from "fast-check";
import ts from "typescript";
import { Project, ScriptTarget } from "ts-morph";
import {
  BOOL_POSITIONS,
  PARAMS,
  POSITIONS,
  TARGETS,
  compileDafnyVariants,
  moduleArb,
  normalize,
  renderModule,
  type DafnyStage,
  type EvaluateHooks,
  type FailureStage,
  type FnSpec,
  type Position,
} from "./narrowing-fuzz.js";

export const SEMANTIC_SCHEMA = "lemmascript-narrowing-semantic-case/1";
export const SEMANTIC_INT_MIN = -100;
export const SEMANTIC_INT_MAX = 100;

export type MaybeInt =
  | { kind: "undefined" }
  | { kind: "null" }
  | { kind: "number"; value: number };

export interface LeafInput {
  value: MaybeInt;
}

export interface BoxInput {
  inner: { kind: "undefined" } | { kind: "leaf"; leaf: LeafInput };
  b: MaybeInt;
  v: MaybeInt;
}

export type ConcreteArg =
  | { kind: "number"; value: number }
  | { kind: "nullable"; value: MaybeInt }
  | { kind: "optional"; value: MaybeInt }
  | { kind: "box"; box: BoxInput }
  | { kind: "optional-box"; value: { kind: "undefined" } | { kind: "box"; box: BoxInput } };

export interface ConcreteCallInput {
  fn: string;
  paramNames: string[];
  args: ConcreteArg[];
}

export type ExpectedValue =
  | { kind: "boolean"; value: boolean }
  | { kind: "number"; value: number };

export interface SemanticCheckCase {
  fn: string;
  inputIndex: number;
  lemmaName: string;
  input: ConcreteCallInput;
  expected: ExpectedValue;
  assertion: string;
}

export type SemanticOracleKind =
  | "invalid-ts"
  | "invalid-input"
  | "rejected"
  | "dafny-pre"
  | "dafny-opt"
  | "dafny-both"
  | "semantic-pre"
  | "semantic-opt"
  | "semantic-both"
  | "timeout"
  | "tool-error";

export interface FailedAssertionReport {
  stage: DafnyStage;
  fn: string;
  inputIndex: number;
  lemmaName: string;
  input: ConcreteCallInput;
  expected: ExpectedValue;
  assertion: string;
  diagnostics: string;
}

export interface SemanticOutcome {
  ok: boolean;
  oracle?: SemanticOracleKind;
  stage?: FailureStage;
  signature?: string;
  detail?: string;
  source: string;
  checks: SemanticCheckCase[];
  preDfy?: string;
  optDfy?: string;
  preSemanticDfy?: string;
  optSemanticDfy?: string;
  optChanged?: boolean;
  failedAssertions?: FailedAssertionReport[];
}

export interface SemanticStageCount {
  attempted: number;
  completed: number;
  skipped: Record<string, number>;
}

export interface SemanticCounts {
  modules: number;
  comparisonsAttempted: number;
  comparisonsCompleted: number;
  dafnyCalls: number;
  optChanged: number;
  pre: SemanticStageCount;
  opt: SemanticStageCount;
}

export interface DafnyVerifyResult {
  status: "ok" | "resolve-error" | "verify-error" | "timeout" | "tool-error";
  verifiedCount: number;
  errorCount: number;
  failedLemmas: string[];
  output: string;
}

export interface SemanticEvaluateHooks extends EvaluateHooks {
  verifyTimeLimitSec?: number;
  verifyTimeoutMs?: number;
  execTimeoutMs?: number;
  overrideExpected?: (fn: string, inputIndex: number, expected: ExpectedValue) => ExpectedValue;
  postEmitPreSemantic?: (dfy: string) => string;
  postEmitOptSemantic?: (dfy: string) => string;
  verifyDafny?: (dfy: string, stage: DafnyStage, expectedChecks: SemanticCheckCase[]) => DafnyVerifyResult;
}

export interface SavedSemanticCase {
  schema: string;
  classIndex: number;
  oracle: SemanticOracleKind;
  stage: FailureStage | null;
  signature: string;
  optChanged: boolean;
  seed: number;
  path: string;
  generatorOptions: {
    positions: readonly Position[];
    inputsPerFn: number;
    intRange: [number, number];
  };
  versions: {
    node: string;
    lemmascript: string;
    dafny: string;
  };
  replayCommands: {
    seedPath: string;
    savedCase: string;
  };
  source: string;
  checks: SemanticCheckCase[];
  failedAssertions: FailedAssertionReport[];
  files: {
    ts: string;
    preSemanticDfy: string | null;
    optSemanticDfy: string | null;
    caseJson: string;
  };
}

export interface SemanticCampaignOptions {
  seed: number;
  runs: number;
  classes: number;
  inputsPerFn: number;
  positions: readonly Position[];
  minutes: number;
  out: string;
  verifyTimeLimitSec?: number;
  hooks?: SemanticEvaluateHooks;
}

export interface SemanticCampaignSummary {
  seed: number;
  failureClasses: number;
  rejectionClasses: number;
  stop: string;
  partial: boolean;
  elapsedSeconds: number;
  counts: SemanticCounts;
  saved: SavedSemanticCase[];
  out: string;
}

export function createSemanticCounts(): SemanticCounts {
  return {
    modules: 0,
    comparisonsAttempted: 0,
    comparisonsCompleted: 0,
    dafnyCalls: 0,
    optChanged: 0,
    pre: { attempted: 0, completed: 0, skipped: {} },
    opt: { attempted: 0, completed: 0, skipped: {} },
  };
}

function recordSkip(stage: SemanticStageCount, reason: string): void {
  stage.skipped[reason] = (stage.skipped[reason] ?? 0) + 1;
}

export function isCanonicalSafeInt(v: unknown): v is number {
  return typeof v === "number" && Number.isSafeInteger(v) && !Object.is(v, -0);
}

// ── Concrete input generation & validation ──────────────────

const INTERESTING_INTS = [-100, -7, -2, -1, 0, 1, 2, 3, 7, 13, 100] as const;

export function safeIntArb(): fc.Arbitrary<number> {
  return fc.oneof(
    { weight: 3, arbitrary: fc.constantFrom(...INTERESTING_INTS) },
    { weight: 2, arbitrary: fc.integer({ min: SEMANTIC_INT_MIN, max: SEMANTIC_INT_MAX }) },
  );
}

export function optionalIntArb(): fc.Arbitrary<MaybeInt> {
  return fc.oneof(
    { weight: 2, arbitrary: fc.constant<MaybeInt>({ kind: "undefined" }) },
    { weight: 5, arbitrary: safeIntArb().map((value): MaybeInt => ({ kind: "number", value })) },
  );
}

export function nullableIntArb(): fc.Arbitrary<MaybeInt> {
  return fc.oneof(
    { weight: 2, arbitrary: fc.constant<MaybeInt>({ kind: "null" }) },
    { weight: 5, arbitrary: safeIntArb().map((value): MaybeInt => ({ kind: "number", value })) },
  );
}

export function leafInputArb(): fc.Arbitrary<LeafInput> {
  return fc.record({ value: optionalIntArb() });
}

export function boxInputArb(): fc.Arbitrary<BoxInput> {
  const innerArb: fc.Arbitrary<BoxInput["inner"]> = fc.oneof(
    { weight: 2, arbitrary: fc.constant<BoxInput["inner"]>({ kind: "undefined" }) },
    { weight: 5, arbitrary: leafInputArb().map((leaf): BoxInput["inner"] => ({ kind: "leaf", leaf })) },
  );
  return fc.record({
    inner: innerArb,
    b: optionalIntArb(),
    v: optionalIntArb(),
  });
}

export interface RawInputRow {
  x: number;
  n: MaybeInt;
  a: BoxInput;
  o: MaybeInt;
  p: MaybeInt;
  a_b: MaybeInt;
  box: { kind: "undefined" } | { kind: "box"; box: BoxInput };
}

export function rawInputRowArb(): fc.Arbitrary<RawInputRow> {
  const optBoxArb: fc.Arbitrary<RawInputRow["box"]> = fc.oneof(
    { weight: 2, arbitrary: fc.constant<RawInputRow["box"]>({ kind: "undefined" }) },
    { weight: 5, arbitrary: boxInputArb().map((box): RawInputRow["box"] => ({ kind: "box", box })) },
  );
  return fc.record({
    x: safeIntArb(),
    n: nullableIntArb(),
    a: boxInputArb(),
    o: optionalIntArb(),
    p: optionalIntArb(),
    a_b: optionalIntArb(),
    box: optBoxArb,
  });
}

export function semanticSampleArb(
  positions: readonly Position[],
  inputsPerFn: number,
): fc.Arbitrary<{ fns: FnSpec[]; inputRows: RawInputRow[][] }> {
  return fc.record({
    fns: moduleArb(positions),
    inputRows: fc.array(
      fc.array(rawInputRowArb(), { minLength: inputsPerFn, maxLength: inputsPerFn }),
      { minLength: 3, maxLength: 3 },
    ),
  });
}

/** Parameter list for a generated `FnSpec`, matching `renderFn`'s exact declaration order. */
export function fnParamRoots(spec: FnSpec): string[] {
  const targets = spec.targets.map(i => TARGETS[i]);
  const roots = new Set<string>();
  for (const t of targets) {
    for (const pre of t.prereqs) roots.add(pre.split(".")[0]);
    roots.add(t.path.split(".")[0]);
  }
  return ["x", ...Object.keys(PARAMS).filter(r => roots.has(r))];
}

/** Bind a `RawInputRow` to the exact parameters declared by `spec`. */
export function bindConcreteInput(spec: FnSpec, fnName: string, row: RawInputRow): ConcreteCallInput {
  const paramNames = fnParamRoots(spec);
  const args: ConcreteArg[] = paramNames.map(name => {
    switch (name) {
      case "x": return { kind: "number", value: row.x };
      case "n": return { kind: "nullable", value: row.n };
      case "a": return { kind: "box", box: row.a };
      case "o": return { kind: "optional", value: row.o };
      case "p": return { kind: "optional", value: row.p };
      case "a_b": return { kind: "optional", value: row.a_b };
      case "box": return { kind: "optional-box", value: row.box };
      default: throw new Error(`Unknown generated parameter: ${name}`);
    }
  });
  return { fn: fnName, paramNames, args };
}

/** Validate concrete arguments strictly (no silent coercion between null/undefined/invalid numbers). */
export function validateConcreteArg(arg: ConcreteArg, label: string): string | null {
  const checkInt = (v: number, where: string): string | null => {
    if (!isCanonicalSafeInt(v)) return `${where}: expected canonical safe integer, got ${Object.is(v, -0) ? "-0" : String(v)}`;
    if (v < SEMANTIC_INT_MIN || v > SEMANTIC_INT_MAX) {
      return `${where}: integer ${v} outside bounded domain [${SEMANTIC_INT_MIN}, ${SEMANTIC_INT_MAX}]`;
    }
    return null;
  };
  const checkOptional = (m: MaybeInt, where: string): string | null => {
    if (m.kind === "undefined") return null;
    if (m.kind === "number") return checkInt(m.value, where);
    return `${where}: optional number parameter cannot accept null`;
  };
  const checkBox = (b: BoxInput, where: string): string | null => {
    if (b.inner.kind === "leaf") {
      const err = checkOptional(b.inner.leaf.value, `${where}.inner.value`);
      if (err) return err;
    }
    return checkOptional(b.b, `${where}.b`) ?? checkOptional(b.v, `${where}.v`);
  };

  switch (arg.kind) {
    case "number": return checkInt(arg.value, label);
    case "nullable":
      if (arg.value.kind === "null") return null;
      if (arg.value.kind === "number") return checkInt(arg.value.value, label);
      return `${label}: nullable number parameter cannot accept undefined`;
    case "optional":
      return checkOptional(arg.value, label);
    case "box":
      return checkBox(arg.box, label);
    case "optional-box":
      return arg.value.kind === "undefined" ? null : checkBox(arg.value.box, label);
  }
}

export function argToJs(arg: ConcreteArg): unknown {
  const optToJs = (m: MaybeInt): number | undefined => (m.kind === "number" ? m.value : undefined);
  const boxToJs = (b: BoxInput): Record<string, unknown> => {
    const out: Record<string, unknown> = {};
    if (b.inner.kind === "leaf") {
      const leaf: Record<string, unknown> = {};
      const lv = optToJs(b.inner.leaf.value);
      if (lv !== undefined) leaf.value = lv;
      out.inner = leaf;
    }
    const bv = optToJs(b.b);
    if (bv !== undefined) out.b = bv;
    const vv = optToJs(b.v);
    if (vv !== undefined) out.v = vv;
    return out;
  };
  switch (arg.kind) {
    case "number": return arg.value;
    case "nullable": return arg.value.kind === "number" ? arg.value.value : null;
    case "optional": return optToJs(arg.value);
    case "box": return boxToJs(arg.box);
    case "optional-box": return arg.value.kind === "box" ? boxToJs(arg.value.box) : undefined;
  }
}

export function dafnyInt(v: number): string {
  return v < 0 ? `(${v})` : `${v}`;
}

export function argToDafny(arg: ConcreteArg): string {
  const maybeToDafny = (m: MaybeInt): string =>
    m.kind === "number" ? `Option.Some(${dafnyInt(m.value)})` : "Option.None";
  const leafToDafny = (l: LeafInput): string => `Leaf(${maybeToDafny(l.value)})`;
  const boxToDafny = (b: BoxInput): string => {
    const inner = b.inner.kind === "leaf" ? `Option.Some(${leafToDafny(b.inner.leaf)})` : "Option.None";
    return `Box(${inner}, ${maybeToDafny(b.b)}, ${maybeToDafny(b.v)})`;
  };
  switch (arg.kind) {
    case "number": return dafnyInt(arg.value);
    case "nullable": return maybeToDafny(arg.value);
    case "optional": return maybeToDafny(arg.value);
    case "box": return boxToDafny(arg.box);
    case "optional-box":
      return arg.value.kind === "box" ? `Option.Some(${boxToDafny(arg.value.box)})` : "Option.None";
  }
}

export function expectedToDafny(expected: ExpectedValue): string {
  return expected.kind === "boolean" ? (expected.value ? "true" : "false") : dafnyInt(expected.value);
}

// ── Independent TypeScript execution ────────────────────────

export function executeTypeScriptChecks(
  tsText: string,
  inputs: ConcreteCallInput[],
  expectedReturnKinds: Map<string, "boolean" | "number">,
  execTimeoutMs = 2_000,
): { ok: true; checks: SemanticCheckCase[] } | { ok: false; oracle: "invalid-ts" | "invalid-input" | "timeout" | "tool-error"; detail: string } {
  for (const inp of inputs) {
    for (let i = 0; i < inp.args.length; i++) {
      const err = validateConcreteArg(inp.args[i], `${inp.fn}.${inp.paramNames[i]}`);
      if (err) return { ok: false, oracle: "invalid-input", detail: err };
    }
  }

  const transpiled = ts.transpileModule(tsText, {
    compilerOptions: {
      target: ts.ScriptTarget.ES2022,
      module: ts.ModuleKind.CommonJS,
      strict: true,
    },
    reportDiagnostics: true,
  });
  if (transpiled.diagnostics && transpiled.diagnostics.length > 0) {
    const msg = transpiled.diagnostics
      .map(d => ts.flattenDiagnosticMessageText(d.messageText, "\n"))
      .join("\n");
    return { ok: false, oracle: "invalid-ts", detail: msg };
  }

  const exportsObj: Record<string, unknown> = {};
  const moduleObj = { exports: exportsObj };
  const sandbox = { exports: exportsObj, module: moduleObj };
  try {
    vm.runInNewContext(transpiled.outputText, sandbox, { timeout: execTimeoutMs });
  } catch (e) {
    const msg = e instanceof Error ? e.message : String(e);
    if (/Script execution timed out/i.test(msg)) {
      return { ok: false, oracle: "timeout", detail: `TypeScript module execution timed out: ${msg}` };
    }
    return { ok: false, oracle: "tool-error", detail: `TypeScript module execution failed: ${msg}` };
  }

  const checks: SemanticCheckCase[] = [];
  const perFnIndex = new Map<string, number>();

  for (const inp of inputs) {
    const fnVal = moduleObj.exports[inp.fn];
    if (typeof fnVal !== "function") {
      return { ok: false, oracle: "tool-error", detail: `Exported function '${inp.fn}' not found after transpiling TypeScript` };
    }
    const inputIndex = perFnIndex.get(inp.fn) ?? 0;
    perFnIndex.set(inp.fn, inputIndex + 1);

    let result: unknown;
    try {
      const jsArgs = inp.args.map(argToJs);
      const callSandbox = { fn: fnVal, args: jsArgs, out: undefined as unknown };
      vm.runInNewContext("out = fn(...args);", callSandbox, { timeout: execTimeoutMs });
      result = callSandbox.out;
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      if (/Script execution timed out/i.test(msg)) {
        return { ok: false, oracle: "timeout", detail: `TypeScript execution of ${inp.fn} timed out: ${msg}` };
      }
      return { ok: false, oracle: "tool-error", detail: `TypeScript execution of ${inp.fn} threw: ${msg}` };
    }

    const expectedKind = expectedReturnKinds.get(inp.fn);
    let expected: ExpectedValue;
    if (typeof result === "boolean") {
      if (expectedKind && expectedKind !== "boolean") {
        return { ok: false, oracle: "invalid-ts", detail: `${inp.fn} returned boolean, expected ${expectedKind}` };
      }
      expected = { kind: "boolean", value: result };
    } else if (isCanonicalSafeInt(result)) {
      if (expectedKind && expectedKind !== "number") {
        return { ok: false, oracle: "invalid-ts", detail: `${inp.fn} returned number, expected ${expectedKind}` };
      }
      expected = { kind: "number", value: result };
    } else {
      return {
        ok: false,
        oracle: "invalid-input",
        detail: `${inp.fn} produced unsupported runtime result: ${Object.is(result, -0) ? "-0" : String(result)}`,
      };
    }

    const lemmaName = `SemanticCheck_${inp.fn}_${inputIndex}`;
    const callExpr = `${inp.fn}(${inp.args.map(argToDafny).join(", ")})`;
    const assertion = `${callExpr} == ${expectedToDafny(expected)}`;
    checks.push({ fn: inp.fn, inputIndex, lemmaName, input: inp, expected, assertion });
  }

  return { ok: true, checks };
}

// ── Dafny assertion emission & verification ─────────────────

export function appendSemanticAssertions(
  dfy: string,
  checks: SemanticCheckCase[],
): { text: string; lemmaLines: Map<string, { start: number; end: number }> } {
  const baseLines = dfy.trimEnd().split("\n");
  const lemmaLines = new Map<string, { start: number; end: number }>();
  const out = [...baseLines, "", "// ── Semantic comparison assertions (concrete inputs) ──"];

  for (const c of checks) {
    const isMethod = new RegExp(`^method\\s+${c.fn}\\b`, "m").test(dfy);
    const start = out.length + 1; // 1-based Dafny line number
    if (isMethod) {
      out.push(`method ${c.lemmaName}() {`);
      out.push(`  var r := ${c.input.fn}(${c.input.args.map(argToDafny).join(", ")});`);
      out.push(`  assert r == ${expectedToDafny(c.expected)};`);
      out.push("}");
    } else {
      out.push(`lemma ${c.lemmaName}()`);
      out.push(`  ensures ${c.assertion}`);
      out.push("{}");
    }
    const end = out.length;
    lemmaLines.set(c.lemmaName, { start, end });
  }

  return { text: out.join("\n") + "\n", lemmaLines };
}

function attributeFailedLemmas(
  output: string,
  lemmaLines: Map<string, { start: number; end: number }>,
): string[] {
  const found = new Set<string>();
  const lineRe = /\((\d+),\d+\): Error:/g;
  let m: RegExpExecArray | null;
  while ((m = lineRe.exec(output)) !== null) {
    const lineNo = Number(m[1]);
    for (const [name, range] of lemmaLines.entries()) {
      if (lineNo >= range.start && lineNo <= range.end) {
        found.add(name);
      }
    }
  }
  for (const name of lemmaLines.keys()) {
    if (output.includes(name)) found.add(name);
  }
  return [...found];
}

export function dafnyVerifySemantic(
  semanticDfy: string,
  lemmaLines: Map<string, { start: number; end: number }>,
  workDir: string,
  stage: DafnyStage,
  expectedChecks: SemanticCheckCase[],
  counts?: SemanticCounts,
  verifyTimeLimitSec = 15,
  verifyTimeoutMs = 120_000,
): DafnyVerifyResult {
  const file = path.join(workDir, `semantic.${stage}.dfy`);
  writeFileSync(file, semanticDfy);
  if (counts) counts.dafnyCalls++;

  const result = spawnSync(
    "dafny",
    ["verify", `--verification-time-limit=${verifyTimeLimitSec}`, file],
    { encoding: "utf8", timeout: verifyTimeoutMs },
  );

  if (result.error) {
    const code = (result.error as NodeJS.ErrnoException).code;
    if (code === "ETIMEDOUT") {
      return {
        status: "timeout",
        verifiedCount: 0,
        errorCount: 0,
        failedLemmas: [],
        output: `dafny verify (${stage}) timed out after ${verifyTimeoutMs}ms`,
      };
    }
    return {
      status: "tool-error",
      verifiedCount: 0,
      errorCount: 0,
      failedLemmas: [],
      output: `dafny verify (${stage}) failed to run: ${result.error.message}`,
    };
  }

  if (result.signal) {
    return {
      status: "timeout",
      verifiedCount: 0,
      errorCount: 0,
      failedLemmas: [],
      output: `dafny verify (${stage}) terminated by signal ${result.signal}`,
    };
  }

  const output = (result.stdout + result.stderr).replaceAll(workDir + path.sep, "").trim();
  const summaryMatch = output.match(/Dafny program verifier finished with (\d+) verified, (\d+) error/);
  const verifiedCount = summaryMatch ? Number(summaryMatch[1]) : 0;
  const errorCount = summaryMatch ? Number(summaryMatch[2]) : 0;

  if (/timed out|Verification out of resource|TimeoutException/i.test(output)) {
    return { status: "timeout", verifiedCount, errorCount, failedLemmas: [], output };
  }

  if (result.status === 0) {
    // Guard against vacuously skipped assertions: Dafny must verify at least one
    // obligation per concrete semantic check.
    if (!summaryMatch || verifiedCount < expectedChecks.length || errorCount !== 0) {
      return {
        status: "tool-error",
        verifiedCount,
        errorCount,
        failedLemmas: [],
        output: `Unexpected Dafny verify summary (expected >= ${expectedChecks.length} verified, 0 errors):\n${output}`,
      };
    }
    return { status: "ok", verifiedCount, errorCount, failedLemmas: [], output };
  }

  if (/resolution\/type errors|parse errors detected/i.test(output) || !summaryMatch) {
    return { status: "resolve-error", verifiedCount, errorCount, failedLemmas: [], output };
  }

  const failedLemmas = attributeFailedLemmas(output, lemmaLines);
  return { status: "verify-error", verifiedCount, errorCount, failedLemmas, output };
}

// ── End-to-end semantic evaluation ──────────────────────────

function createProject(): Project {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

export function evaluateSemanticCase(
  tsText: string,
  inputs: ConcreteCallInput[],
  expectedReturnKinds: Map<string, "boolean" | "number">,
  env: { project: Project; workDir: string; counts: SemanticCounts },
  hooks?: SemanticEvaluateHooks,
): SemanticOutcome {
  env.counts.comparisonsAttempted += inputs.length;

  // Step 1: Compile through production pipeline (pre-opt + opt), also catching invalid-ts / rejected.
  const compiledRes = compileDafnyVariants(tsText, env.project, hooks);
  if (!compiledRes.ok) {
    recordSkip(env.counts.pre, compiledRes.failure.oracle);
    recordSkip(env.counts.opt, compiledRes.failure.oracle);
    return {
      ok: false,
      oracle: compiledRes.failure.oracle === "invalid-ts" ? "invalid-ts" : "rejected",
      signature: compiledRes.failure.signature,
      detail: compiledRes.failure.detail,
      source: tsText,
      checks: [],
    };
  }

  const { preDfy, optDfy, optChanged } = compiledRes.compiled;
  if (optChanged) env.counts.optChanged++;

  // Step 2: Execute original TypeScript independently to obtain expected results.
  const execRes = executeTypeScriptChecks(tsText, inputs, expectedReturnKinds, hooks?.execTimeoutMs ?? 2_000);
  if (!execRes.ok) {
    recordSkip(env.counts.pre, execRes.oracle);
    recordSkip(env.counts.opt, execRes.oracle);
    return {
      ok: false,
      oracle: execRes.oracle,
      signature: `${execRes.oracle}: ${normalize(execRes.detail.split("\n")[0])}`,
      detail: execRes.detail,
      source: tsText,
      checks: [],
      preDfy,
      optDfy,
      optChanged,
    };
  }

  let checks = execRes.checks;
  if (hooks?.overrideExpected) {
    checks = checks.map(c => {
      const next = hooks.overrideExpected!(c.fn, c.inputIndex, c.expected);
      const callExpr = `${c.input.fn}(${c.input.args.map(argToDafny).join(", ")})`;
      return { ...c, expected: next, assertion: `${callExpr} == ${expectedToDafny(next)}` };
    });
  }

  // Step 3: Append semantic assertions and verify both pre-optimization and optimized Dafny.
  const preBuilt = appendSemanticAssertions(preDfy, checks);
  const optBuilt = appendSemanticAssertions(optDfy, checks);
  const preSemanticDfy = hooks?.postEmitPreSemantic ? hooks.postEmitPreSemantic(preBuilt.text) : preBuilt.text;
  const optSemanticDfy = hooks?.postEmitOptSemantic ? hooks.postEmitOptSemantic(optBuilt.text) : optBuilt.text;

  const verifyStage = (stage: DafnyStage, dfy: string, lemmaLines: Map<string, { start: number; end: number }>) => {
    if (hooks?.verifyDafny) return hooks.verifyDafny(dfy, stage, checks);
    return dafnyVerifySemantic(
      dfy,
      lemmaLines,
      env.workDir,
      stage,
      checks,
      env.counts,
      hooks?.verifyTimeLimitSec ?? 15,
      hooks?.verifyTimeoutMs ?? 120_000,
    );
  };

  env.counts.pre.attempted++;
  const preRes = verifyStage("pre", preSemanticDfy, preBuilt.lemmaLines);
  if (preRes.status === "ok" || preRes.status === "resolve-error" || preRes.status === "verify-error") {
    env.counts.pre.completed++;
  }

  env.counts.opt.attempted++;
  const optRes = verifyStage("opt", optSemanticDfy, optBuilt.lemmaLines);
  if (optRes.status === "ok" || optRes.status === "resolve-error" || optRes.status === "verify-error") {
    env.counts.opt.completed++;
  }

  if (preRes.status === "ok" && optRes.status === "ok") {
    env.counts.comparisonsCompleted += checks.length;
    return {
      ok: true,
      source: tsText,
      checks,
      preDfy,
      optDfy,
      preSemanticDfy,
      optSemanticDfy,
      optChanged,
    };
  }

  if (preRes.status === "timeout" || optRes.status === "timeout") {
    const stage: FailureStage =
      preRes.status === "timeout" && optRes.status === "timeout" ? "both"
      : preRes.status === "timeout" ? "pre" : "opt";
    const detail = [preRes.output, optRes.output].filter(Boolean).join("\n");
    return {
      ok: false,
      oracle: "timeout",
      stage,
      signature: `timeout (${stage}): ${normalize(detail.split("\n")[0])}`,
      detail,
      source: tsText,
      checks,
      preDfy,
      optDfy,
      preSemanticDfy,
      optSemanticDfy,
      optChanged,
    };
  }

  if (preRes.status === "tool-error" || optRes.status === "tool-error") {
    const stage: FailureStage =
      preRes.status === "tool-error" && optRes.status === "tool-error" ? "both"
      : preRes.status === "tool-error" ? "pre" : "opt";
    const detail = [preRes.output, optRes.output].filter(Boolean).join("\n");
    return {
      ok: false,
      oracle: "tool-error",
      stage,
      signature: `tool-error (${stage}): ${normalize(detail.split("\n")[0])}`,
      detail,
      source: tsText,
      checks,
      preDfy,
      optDfy,
      preSemanticDfy,
      optSemanticDfy,
      optChanged,
    };
  }

  if (preRes.status === "resolve-error" || optRes.status === "resolve-error") {
    const stage: FailureStage =
      preRes.status === "resolve-error" && optRes.status === "resolve-error" ? "both"
      : preRes.status === "resolve-error" ? "pre" : "opt";
    const oracle: SemanticOracleKind = stage === "both" ? "dafny-both" : stage === "pre" ? "dafny-pre" : "dafny-opt";
    const primary = stage === "opt" ? optRes.output : preRes.output;
    const first = primary.split("\n").find(l => / Error: /.test(l)) ?? primary.split("\n")[0];
    return {
      ok: false,
      oracle,
      stage,
      signature: `${oracle}: ${normalize(first.replace(/^.*? Error: /, ""))}`,
      detail: `pre (${preRes.status}):\n${preRes.output}\nopt (${optRes.status}):\n${optRes.output}`,
      source: tsText,
      checks,
      preDfy,
      optDfy,
      preSemanticDfy,
      optSemanticDfy,
      optChanged,
    };
  }

  // Verification assertion failure (semantic mismatch or unprovable concrete assertion).
  // Report failed assertions and Dafny diagnostics; never invent an actual model value.
  const stage: FailureStage =
    preRes.status === "verify-error" && optRes.status === "verify-error" ? "both"
    : preRes.status === "verify-error" ? "pre" : "opt";
  const oracle: SemanticOracleKind = stage === "both" ? "semantic-both" : stage === "pre" ? "semantic-pre" : "semantic-opt";

  const failedAssertions: FailedAssertionReport[] = [];
  const collectFailed = (s: DafnyStage, res: DafnyVerifyResult) => {
    if (res.status !== "verify-error") return;
    const matched = res.failedLemmas.length > 0
      ? checks.filter(c => res.failedLemmas.includes(c.lemmaName))
      : checks;
    for (const c of matched) {
      failedAssertions.push({
        stage: s,
        fn: c.fn,
        inputIndex: c.inputIndex,
        lemmaName: c.lemmaName,
        input: c.input,
        expected: c.expected,
        assertion: c.assertion,
        diagnostics: res.output,
      });
    }
  };
  collectFailed("pre", preRes);
  collectFailed("opt", optRes);

  const firstFail = failedAssertions[0];
  const detailLines = [
    `Semantic verification failed at stage: ${stage}`,
    ...failedAssertions.map(f =>
      `  [${f.stage}] ${f.fn} (input #${f.inputIndex}): assertion \`${f.assertion}\` failed (expected ${f.expected.kind} ${f.expected.value}; concrete input: ${JSON.stringify(f.input.args)})`),
    `pre (${preRes.status}):\n${preRes.output}`,
    `opt (${optRes.status}):\n${optRes.output}`,
  ];
  return {
    ok: false,
    oracle,
    stage,
    signature: `${oracle}: ${firstFail ? `${firstFail.fn} (${firstFail.expected.kind})` : "assertion failed"}`,
    detail: detailLines.join("\n"),
    source: tsText,
    checks,
    preDfy,
    optDfy,
    preSemanticDfy,
    optSemanticDfy,
    optChanged,
    failedAssertions,
  };
}

// ── Versions & Replay ───────────────────────────────────────

function toolVersions(): { node: string; lemmascript: string; dafny: string } {
  let lemmascript = "unknown";
  try {
    const pkg = JSON.parse(readFileSync(new URL("../../package.json", import.meta.url), "utf8"));
    lemmascript = String(pkg.version ?? "unknown");
  } catch { /* ignore */ }
  let dafny = "unknown";
  try {
    const res = spawnSync("dafny", ["--version"], { encoding: "utf8", timeout: 10_000 });
    if (res.status === 0) dafny = (res.stdout + res.stderr).trim().split("\n")[0];
  } catch { /* ignore */ }
  return { node: process.version, lemmascript, dafny };
}

function buildInputsForModule(
  fns: FnSpec[],
  inputRows: RawInputRow[][],
): { inputs: ConcreteCallInput[]; returnKinds: Map<string, "boolean" | "number"> } {
  const inputs: ConcreteCallInput[] = [];
  const returnKinds = new Map<string, "boolean" | "number">();
  for (let i = 0; i < fns.length; i++) {
    const fnName = `f${i}`;
    returnKinds.set(fnName, BOOL_POSITIONS.has(fns[i].position) ? "boolean" : "number");
    const rows = inputRows[i] ?? [];
    for (const row of rows) {
      inputs.push(bindConcreteInput(fns[i], fnName, row));
    }
  }
  return { inputs, returnKinds };
}

function formatSkipped(skipped: Record<string, number>): string {
  const entries = Object.entries(skipped);
  if (entries.length === 0) return "0";
  const total = entries.reduce((acc, [, n]) => acc + n, 0);
  const reasons = entries.sort(([a], [b]) => a.localeCompare(b)).map(([k, n]) => `${k}=${n}`).join(", ");
  return `${total} (${reasons})`;
}

export function replaySavedSemanticCase(
  casePath: string,
  hooks?: SemanticEvaluateHooks,
): SemanticOutcome {
  const saved = JSON.parse(readFileSync(casePath, "utf8")) as SavedSemanticCase;
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-semantic-replay-"));
  try {
    const project = createProject();
    const counts = createSemanticCounts();
    const inputs = saved.checks.map(c => c.input);
    const returnKinds = new Map<string, "boolean" | "number">();
    for (const c of saved.checks) returnKinds.set(c.fn, c.expected.kind);
    return evaluateSemanticCase(saved.source, inputs, returnKinds, { project, workDir, counts }, hooks);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
}

export function replaySemanticSeedPath(opts: {
  seed: number;
  path: string;
  runs: number;
  inputsPerFn: number;
  positions: readonly Position[];
  hooks?: SemanticEvaluateHooks;
}): { passed: boolean; outcome?: SemanticOutcome } {
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-semantic-seed-replay-"));
  try {
    const project = createProject();
    const counts = createSemanticCounts();
    const arb = semanticSampleArb(opts.positions, opts.inputsPerFn);
    let lastOutcome: SemanticOutcome | undefined;
    const result = fc.check(
      fc.property(arb, ({ fns, inputRows }) => {
        const tsText = renderModule(fns, { omitEnsures: true });
        const { inputs, returnKinds } = buildInputsForModule(fns, inputRows);
        lastOutcome = evaluateSemanticCase(tsText, inputs, returnKinds, { project, workDir, counts }, opts.hooks);
        return lastOutcome.ok;
      }),
      { seed: opts.seed, path: opts.path, numRuns: opts.runs, endOnFailure: true },
    );
    if (!result.failed) return { passed: true };
    return { passed: false, outcome: lastOutcome };
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
}

export function runSemanticCampaign(opts: SemanticCampaignOptions): SemanticCampaignSummary {
  mkdirSync(opts.out, { recursive: true });
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-semantic-fuzz-"));
  const project = createProject();
  const counts = createSemanticCounts();
  const versions = toolVersions();
  const cache = new Map<string, SemanticOutcome>();

  const evalSample = (fns: FnSpec[], inputRows: RawInputRow[][]): SemanticOutcome => {
    const tsText = renderModule(fns, { omitEnsures: true });
    const { inputs, returnKinds } = buildInputsForModule(fns, inputRows);
    const key = tsText + "\0" + JSON.stringify(inputs);
    let outcome = cache.get(key);
    if (!outcome) {
      counts.modules++;
      outcome = evaluateSemanticCase(tsText, inputs, returnKinds, { project, workDir, counts }, {
        verifyTimeLimitSec: opts.verifyTimeLimitSec ?? 15,
        ...opts.hooks,
      });
      cache.set(key, outcome);
    }
    return outcome;
  };

  const arb = semanticSampleArb(opts.positions, opts.inputsPerFn);
  const started = Date.now();
  const deadline = started + opts.minutes * 60_000;
  const seen = new Set<string>();
  const saved: SavedSemanticCase[] = [];
  let rejections = 0;
  let partial = false;
  let stop = "class limit reached";
  const allPositions = opts.positions.length === POSITIONS.length &&
    opts.positions.every((p, i) => p === POSITIONS[i]);
  const positionsArg = allPositions ? "" : ` --positions ${opts.positions.join(",")}`;

  try {
    for (let round = 0; seen.size < opts.classes; round++) {
      const remaining = deadline - Date.now();
      if (remaining <= 0) { stop = "time limit reached"; partial = true; break; }
      const roundSeed = opts.seed + round;
      let lockedOracle: SemanticOracleKind | null = null;
      const result = fc.check(
        fc.property(arb, ({ fns, inputRows }) => {
          const outcome = evalSample(fns, inputRows);
          if (outcome.ok || !outcome.signature || !outcome.oracle || seen.has(outcome.signature)) return true;
          if (lockedOracle === null) {
            lockedOracle = outcome.oracle;
            return false;
          }
          return outcome.oracle !== lockedOracle;
        }),
        { seed: roundSeed, numRuns: opts.runs, interruptAfterTimeLimit: remaining, markInterruptAsFailure: false },
      );

      if (!result.failed || !result.counterexample) {
        if (result.interrupted) {
          stop = "time limit reached";
          partial = true;
        } else {
          stop = `round with seed ${roundSeed} found no new class in ${opts.runs} runs`;
        }
        break;
      }

      const [{ fns, inputRows }] = result.counterexample;
      const outcome = evalSample(fns, inputRows);
      if (outcome.ok || !outcome.signature || !outcome.oracle) continue;
      seen.add(outcome.signature);
      const rejection = outcome.oracle === "rejected";
      if (rejection) rejections++;

      const n = seen.size;
      const tsPath = path.join(opts.out, `${n}.ts`);
      const prePath = outcome.preSemanticDfy !== undefined ? path.join(opts.out, `${n}.pre.semantic.dfy`) : null;
      const optPath = outcome.optSemanticDfy !== undefined ? path.join(opts.out, `${n}.opt.semantic.dfy`) : null;
      const casePath = path.join(opts.out, `${n}.semantic.json`);
      writeFileSync(tsPath, outcome.source);
      if (prePath && outcome.preSemanticDfy !== undefined) writeFileSync(prePath, outcome.preSemanticDfy);
      if (optPath && outcome.optSemanticDfy !== undefined) writeFileSync(optPath, outcome.optSemanticDfy);

      const seedPathCmd = `npm run fuzz:semantic -- --seed ${roundSeed} --inputs-per-fn ${opts.inputsPerFn}${positionsArg} --path ${result.counterexamplePath}`;
      const savedCaseCmd = `npm run fuzz:semantic -- --case ${casePath}`;
      const record: SavedSemanticCase = {
        schema: SEMANTIC_SCHEMA,
        classIndex: n,
        oracle: outcome.oracle,
        stage: outcome.stage ?? null,
        signature: outcome.signature,
        optChanged: outcome.optChanged ?? false,
        seed: roundSeed,
        path: result.counterexamplePath ?? "",
        generatorOptions: {
          positions: opts.positions,
          inputsPerFn: opts.inputsPerFn,
          intRange: [SEMANTIC_INT_MIN, SEMANTIC_INT_MAX],
        },
        versions,
        replayCommands: {
          seedPath: seedPathCmd,
          savedCase: savedCaseCmd,
        },
        source: outcome.source,
        checks: outcome.checks,
        failedAssertions: outcome.failedAssertions ?? [],
        files: {
          ts: path.basename(tsPath),
          preSemanticDfy: prePath ? path.basename(prePath) : null,
          optSemanticDfy: optPath ? path.basename(optPath) : null,
          caseJson: path.basename(casePath),
        },
      };
      writeFileSync(casePath, JSON.stringify(record, null, 2) + "\n");
      saved.push(record);
      console.log(`── semantic class ${n}${rejection ? " (rejection)" : ""}: replay with ${seedPathCmd} ──\n${outcome.source}\n${outcome.signature}\n${outcome.detail}\n`);
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }

  const elapsedSeconds = Number(((Date.now() - started) / 1000).toFixed(1));
  console.log(
    `[semantic] ${seen.size - rejections} failure classes, ${rejections} rejection classes; seed ${opts.seed}; ` +
    `stopped: ${stop}${partial ? " (partial coverage)" : ""}`,
  );
  console.log(
    `[semantic] ${counts.modules} distinct (module,input) samples (${counts.optChanged} changed by peephole), ` +
    `${counts.comparisonsAttempted} comparisons attempted / ${counts.comparisonsCompleted} completed, ` +
    `pre: ${counts.pre.attempted} attempted / ${counts.pre.completed} completed / skipped ${formatSkipped(counts.pre.skipped)}, ` +
    `opt: ${counts.opt.attempted} attempted / ${counts.opt.completed} completed / skipped ${formatSkipped(counts.opt.skipped)}, ` +
    `${counts.dafnyCalls} dafny verify calls, ${elapsedSeconds.toFixed(1)}s`,
  );
  console.log(`[semantic] artifacts saved to ${opts.out}`);
  return {
    seed: opts.seed,
    failureClasses: seen.size - rejections,
    rejectionClasses: rejections,
    stop,
    partial,
    elapsedSeconds,
    counts,
    saved,
    out: opts.out,
  };
}
