/**
 * Imperative, mutation, nullish, union, and aliasing semantic soundness oracle
 * for the narrowing fuzzer (`midspiral/LemmaScript#387`, `robertpenner/LemmaScript#46`).
 *
 * Extends the pure optional-number oracle in `semantic-oracle.ts` with:
 *   1. Negated-postcondition refutation (`soundness-refuted`): when Node returns
 *      `v_js`, asserts `r != v_js` in Dafny; if `dafny verify` succeeds, flags a
 *      critical soundness failure (false proof).
 *   2. Precondition-drop oracle (`precondition-dropped`): executes a `guard(ok, v)`
 *      helper with `//@ requires ok`; when Node hits `guard(false)`, requires
 *      `dafny verify` to reject the call.
 *   3. Imperative `fast-check` generator covering reassignments, optional
 *      array/record/map mutations, shadowed bindings + fuel-bounded `while`
 *      loops, discriminated unions, `null` vs. `undefined` + falsy traps,
 *      live-alias vs. dead-source move vs. read-only alias pairs, and
 *      evaluated vs. short-circuited `guard(false)` positions.
 *   4. Batched `dafny run --no-verify` fast screening mode packing multiple
 *      compiled cases into one `.dfy` with a `Main()` driver.
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
  compileDafnyVariants,
  normalize,
  type DafnyStage,
  type EvaluateHooks,
  type FailureStage,
} from "./narrowing-fuzz.js";
import { checkNarrowedModule, type NarrowViolation } from "../src/narrow-checks.js";

export const IMPERATIVE_SCHEMA = "lemmascript-imperative-semantic-case/1";

export const IMPERATIVE_FAMILIES = [
  "reassign",
  "mutation",
  "loop-shadow",
  "union",
  "nullish-falsy",
  "aliasing",
  "guard-eval",
] as const;

export type ImperativeFamily = (typeof IMPERATIVE_FAMILIES)[number];

export type ImperativeArg =
  | { kind: "int"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "opt-int"; value: number | undefined }
  | { kind: "opt-str"; value: string | undefined }
  | { kind: "opt-bool"; value: boolean | undefined }
  | { kind: "nullish-int"; value: number | null | undefined }
  | { kind: "int-array"; value: number[] }
  | { kind: "opt-int-array"; value: number[] | undefined }
  | { kind: "opt-box"; value: { items?: number[]; count?: number } | undefined }
  | { kind: "int-map"; value: Array<[string, number]> }
  | { kind: "arr-map"; value: Array<[string, number[]]> }
  | { kind: "union-ab"; value: { kind: "a"; v: number } | { kind: "b"; items: number[] } };

export interface ImperativeInput {
  args: ImperativeArg[];
}

export interface ImperativeProgram {
  family: ImperativeFamily;
  label: string;
  tsText: string;
  fnName: string;
  returnKind: "number" | "boolean";
  inputs: ImperativeInput[];
  /** True when the program intentionally exhibits live-alias mutation. */
  isLiveAliasMutation?: boolean;
}

export type NodeExecOutcome =
  | { kind: "value"; value: number | boolean }
  | { kind: "precondition-violated"; detail: string }
  | { kind: "runtime-error"; detail: string };

export type ImperativeOracleKind =
  | "soundness-refuted"
  | "precondition-dropped"
  | "semantic-mismatch"
  | "dafny-resolve"
  | "rejected"
  | "invalid-ts"
  | "timeout"
  | "tool-error";

export interface ImperativeCheckDetail {
  inputIndex: number;
  nodeOutcome: NodeExecOutcome;
  dafnyArgs: string[];
  stage: DafnyStage;
  status: "ok" | "soundness-refuted" | "precondition-dropped" | "semantic-mismatch" | "resolve-error" | "timeout" | "tool-error";
  detail: string;
}

export interface ImperativeOutcome {
  ok: boolean;
  oracle?: ImperativeOracleKind;
  stage?: FailureStage;
  signature: string;
  detail: string;
  family: ImperativeFamily;
  label: string;
  preDfy?: string;
  optDfy?: string;
  optChanged?: boolean;
  irViolations?: NarrowViolation[];
  checks: ImperativeCheckDetail[];
}

export interface SavedImperativeCase {
  schema: typeof IMPERATIVE_SCHEMA;
  family: ImperativeFamily;
  label: string;
  fnName: string;
  returnKind: "number" | "boolean";
  tsText: string;
  inputs: ImperativeInput[];
  oracle: ImperativeOracleKind | "ok";
  stage: FailureStage | null;
  signature: string;
  detail: string;
  checks: ImperativeCheckDetail[];
}

export interface ImperativeCounts {
  programs: number;
  dafnyCalls: number;
  soundnessRefuted: number;
  preconditionDropped: number;
  semanticMismatch: number;
  dafnyResolve: number;
  rejected: number;
  invalidTs: number;
  timeout: number;
  toolError: number;
  passed: number;
}

export function createImperativeCounts(): ImperativeCounts {
  return {
    programs: 0,
    dafnyCalls: 0,
    soundnessRefuted: 0,
    preconditionDropped: 0,
    semanticMismatch: 0,
    dafnyResolve: 0,
    rejected: 0,
    invalidTs: 0,
    timeout: 0,
    toolError: 0,
    passed: 0,
  };
}

// ── Value encoding (JS <-> Dafny) ───────────────────────────

function dafnyInt(n: number): string {
  return n < 0 ? `(${n})` : String(n);
}

function dafnyStr(s: string): string {
  return JSON.stringify(s);
}

function dafnyOption(inner: string | null): string {
  return inner === null ? "Option.None" : `Option.Some(${inner})`;
}

export function imperativeArgToJs(arg: ImperativeArg): unknown {
  switch (arg.kind) {
    case "int": return arg.value;
    case "bool": return arg.value;
    case "opt-int": return arg.value;
    case "opt-str": return arg.value;
    case "opt-bool": return arg.value;
    case "nullish-int": return arg.value;
    case "int-array": return [...arg.value];
    case "opt-int-array": return arg.value === undefined ? undefined : [...arg.value];
    case "opt-box":
      return arg.value === undefined
        ? undefined
        : {
            items: arg.value.items === undefined ? undefined : [...arg.value.items],
            count: arg.value.count,
          };
    case "int-map": return new Map(arg.value);
    case "arr-map": return new Map(arg.value.map(([k, arr]) => [k, [...arr]]));
    case "union-ab":
      return arg.value.kind === "a"
        ? { kind: "a", v: arg.value.v }
        : { kind: "b", items: [...arg.value.items] };
  }
}

export function imperativeArgToDafny(arg: ImperativeArg, dfySource: string): string {
  switch (arg.kind) {
    case "int": return dafnyInt(arg.value);
    case "bool": return arg.value ? "true" : "false";
    case "opt-int": return dafnyOption(arg.value === undefined ? null : dafnyInt(arg.value));
    case "opt-str": return dafnyOption(arg.value === undefined ? null : dafnyStr(arg.value));
    case "opt-bool": return dafnyOption(arg.value === undefined ? null : (arg.value ? "true" : "false"));
    case "nullish-int": {
      if (dfySource.includes("datatype Nullish<")) {
        if (arg.value === undefined) return "Nullish.Undefined";
        if (arg.value === null) return "Nullish.Null";
        return `Nullish.Value(${dafnyInt(arg.value)})`;
      }
      // On current main, null and undefined both encode as Option.None.
      return arg.value === undefined || arg.value === null
        ? "Option.None"
        : `Option.Some(${dafnyInt(arg.value)})`;
    }
    case "int-array": return `[${arg.value.map(dafnyInt).join(", ")}]`;
    case "opt-int-array":
      return dafnyOption(
        arg.value === undefined ? null : `[${arg.value.map(dafnyInt).join(", ")}]`,
      );
    case "opt-box": {
      if (arg.value === undefined) return "Option.None";
      const items = dafnyOption(
        arg.value.items === undefined ? null : `[${arg.value.items.map(dafnyInt).join(", ")}]`,
      );
      const count = dafnyOption(arg.value.count === undefined ? null : dafnyInt(arg.value.count));
      return `Option.Some(Box(${items}, ${count}))`;
    }
    case "int-map":
      return `map[${arg.value.map(([k, v]) => `${dafnyStr(k)} := ${dafnyInt(v)}`).join(", ")}]`;
    case "arr-map":
      return `map[${arg.value.map(([k, arr]) => `${dafnyStr(k)} := [${arr.map(dafnyInt).join(", ")}]`).join(", ")}]`;
    case "union-ab": {
      // Detect the generated union constructor names in emitted Dafny.
      if (arg.value.kind === "a") {
        const m = dfySource.match(/\b(\w+)\s*\(\s*v\s*:/);
        const ctor = m ? m[1] : "a";
        return `${ctor}(${dafnyInt(arg.value.v)})`;
      }
      const m = dfySource.match(/\b(\w+)\s*\(\s*items\s*:/);
      const ctor = m ? m[1] : "b";
      return `${ctor}([${arg.value.items.map(dafnyInt).join(", ")}])`;
    }
  }
}

// ── Node execution ──────────────────────────────────────────

const PRECONDITION_MARKER = "__LS_PRECONDITION_VIOLATED__";

export function executeImperativeInNode(
  tsText: string,
  fnName: string,
  input: ImperativeInput,
  returnKind: "number" | "boolean",
): NodeExecOutcome {
  // Instrument `guard(ok, v)` so JS throws a tagged precondition error when ok is false,
  // matching `//@ requires ok`.
  const instrumented = tsText.replace(
    /export function guard\(ok: boolean, v: number\): number \{[^}]*\}/,
    `export function guard(ok: boolean, v: number): number { if (!ok) throw new Error(${JSON.stringify(PRECONDITION_MARKER)}); return v; }`,
  );
  const transpiled = ts.transpileModule(instrumented, {
    compilerOptions: {
      module: ts.ModuleKind.CommonJS,
      target: ts.ScriptTarget.ES2022,
      strict: true,
    },
    reportDiagnostics: false,
  });
  const exportsObj: Record<string, unknown> = {};
  const moduleObj = { exports: exportsObj };
  try {
    vm.runInNewContext(
      transpiled.outputText,
      { exports: exportsObj, module: moduleObj, Map, Set, Array, Number, Boolean, String, Math, Error },
      { timeout: 2000 },
    );
    const fn = moduleObj.exports[fnName];
    if (typeof fn !== "function") {
      return { kind: "runtime-error", detail: `exported function ${fnName} not found` };
    }
    const jsArgs = input.args.map(imperativeArgToJs);
    const result = fn(...jsArgs);
    if (returnKind === "boolean") {
      if (typeof result !== "boolean") {
        return { kind: "runtime-error", detail: `expected boolean return, got ${typeof result}` };
      }
      return { kind: "value", value: result };
    }
    if (typeof result !== "number" || !Number.isSafeInteger(result)) {
      return { kind: "runtime-error", detail: `expected safe integer return, got ${String(result)}` };
    }
    return { kind: "value", value: Object.is(result, -0) ? 0 : result };
  } catch (e) {
    const msg = e instanceof Error ? e.message : String(e);
    if (msg.includes(PRECONDITION_MARKER)) {
      return { kind: "precondition-violated", detail: msg };
    }
    return { kind: "runtime-error", detail: msg };
  }
}

// ── Dafny harness & verification ────────────────────────────

function splitTopLevelCommas(raw: string): string[] {
  const out: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < raw.length; i++) {
    const ch = raw[i];
    if (ch === "<" || ch === "(" || ch === "[") depth++;
    else if (ch === ">" || ch === ")" || ch === "]") depth--;
    else if (ch === "," && depth === 0) {
      out.push(raw.slice(start, i));
      start = i + 1;
    }
  }
  out.push(raw.slice(start));
  return out;
}

function parseTargetHeader(
  dfy: string,
  fnName: string,
): { declKind: "method" | "function"; headerStart: number; bodyStart: number; paramNames: string[]; retName: string | null; header: string } | null {
  const re = new RegExp(`(^|\\n)(method|function)\\s+${fnName}\\s*\\(([^)]*)\\)([^\\n{]*)\\n?\\s*\\{`);
  const m = re.exec(dfy);
  if (!m) return null;
  const declKind = m[2] as "method" | "function";
  const rawParams = m[3].trim();
  const paramNames = rawParams === ""
    ? []
    : splitTopLevelCommas(rawParams).map(p => p.trim().split(":")[0].trim());
  const retMatch = m[4].match(/returns\s*\(\s*(\w+)\s*:/);
  const retName = retMatch ? retMatch[1] : null;
  const headerStart = m.index + m[1].length;
  const bodyStart = m.index + m[0].length - 1; // points at '{'
  const header = dfy.slice(headerStart, bodyStart).trimEnd();
  return { declKind, headerStart, bodyStart, paramNames, retName, header };
}

function extractBalancedBraceBlock(src: string, openBraceIdx: number): string | null {
  if (src[openBraceIdx] !== "{") return null;
  let depth = 0;
  for (let i = openBraceIdx; i < src.length; i++) {
    const ch = src[i];
    if (ch === "{") depth++;
    else if (ch === "}") {
      depth--;
      if (depth === 0) return src.slice(openBraceIdx, i + 1);
    }
  }
  return null;
}

function dafnyExpectedLiteral(v: number | boolean): string {
  return typeof v === "boolean" ? (v ? "true" : "false") : dafnyInt(v);
}

/**
 * Specialize `target` into a self-contained `SemanticOracleCheck_<i>` declaration
 * carrying `requires param == concreteArg` and (for value checks) `ensures` directly
 * on the cloned body. This verifies BOTH imperative Dafny `method` bodies (which
 * cannot be unfolded by external callers without `ensures`) and pure `function`
 * bodies (including concrete-input precondition checks like #349).
 */
function buildSpecializedDafnyCheck(
  dfy: string,
  fnName: string,
  dafnyArgs: string[],
  mode: { kind: "positive"; expected: number | boolean }
      | { kind: "refute"; expected: number | boolean }
      | { kind: "precondition-must-fail" },
  checkIdx: number,
): { symbol: string; text: string } | null {
  const parsed = parseTargetHeader(dfy, fnName);
  if (!parsed || parsed.paramNames.length !== dafnyArgs.length) return null;
  const body = extractBalancedBraceBlock(dfy, parsed.bodyStart);
  if (!body) return null;

  const symbol = `SemanticOracleCheck_${checkIdx}`;
  const renamedHeader = parsed.header.replace(
    new RegExp(`^(${parsed.declKind}\\s+)${fnName}\\b`),
    `$1${symbol}`,
  );
  const reqLines = parsed.paramNames.map((p, idx) => `  requires ${p} == ${dafnyArgs[idx]}`);

  const specLines: string[] = [...reqLines];
  if (mode.kind === "positive" || mode.kind === "refute") {
    const lit = dafnyExpectedLiteral(mode.expected);
    const op = mode.kind === "positive" ? "==" : "!=";
    if (parsed.declKind === "method") {
      const resName = parsed.retName ?? "res";
      specLines.push(`  ensures ${resName} ${op} ${lit}`);
    } else {
      specLines.push(`  ensures ${symbol}(${parsed.paramNames.join(", ")}) ${op} ${lit}`);
    }
  }

  // Replace direct recursive calls if any are absent; standard generated targets are non-recursive.
  const specialized = `\n${renamedHeader}\n${specLines.join("\n")}\n${body}\n`;
  return { symbol, text: dfy + specialized };
}

function runDafnyVerifyText(
  dfyText: string,
  workDir: string,
  fileName: string,
  counts: ImperativeCounts,
  timeoutSec: number,
  filterSymbol?: string,
): { status: "verified" | "verify-error" | "resolve-error" | "timeout" | "tool-error"; detail: string } {
  const filePath = path.join(workDir, fileName);
  writeFileSync(filePath, dfyText);
  counts.dafnyCalls++;
  const args = ["verify", `--verification-time-limit:${timeoutSec}`];
  if (filterSymbol) args.push(`--filter-symbol=${filterSymbol}`);
  args.push(filePath);
  const res = spawnSync("dafny", args, {
    encoding: "utf8",
    timeout: (timeoutSec + 15) * 1000,
    maxBuffer: 10 * 1024 * 1024,
  });
  const out = `${res.stdout ?? ""}\n${res.stderr ?? ""}`.trim();
  if (res.error) {
    if ((res.error as NodeJS.ErrnoException).code === "ETIMEDOUT") {
      return { status: "timeout", detail: out || "dafny verify timed out" };
    }
    return { status: "tool-error", detail: res.error.message };
  }
  if (res.signal) {
    if (res.signal === "SIGTERM" || res.signal === "SIGKILL") {
      return { status: "timeout", detail: `terminated by timeout signal ${res.signal}` };
    }
    return { status: "tool-error", detail: `dafny crashed with signal ${res.signal}${out ? `\n${out}` : ""}` };
  }
  if (out.includes("timed out")) {
    return { status: "timeout", detail: out };
  }
  if (res.status === 0 && /finished with \d+ verified, 0 errors/.test(out)) {
    return { status: "verified", detail: out };
  }
  if (res.status === 2 || /resolution\/type errors detected|parse errors detected/i.test(out)) {
    return { status: "resolve-error", detail: out };
  }
  if (res.status === 4 || /finished with \d+ verified, [1-9]\d* errors/.test(out)) {
    return { status: "verify-error", detail: out };
  }
  return { status: "tool-error", detail: out || `dafny exited with ${res.status}` };
}

function checkTypeScriptValid(tsText: string, project: Project): string | null {
  const sf = project.createSourceFile("imp_check.ts", tsText, { overwrite: true });
  try {
    const diags = sf.getPreEmitDiagnostics();
    if (diags.length === 0) return null;
    return diags.map(d => ts.flattenDiagnosticMessageText(d.getMessageText(), "\n")).join("\n");
  } finally {
    project.removeSourceFile(sf);
  }
}

export function evaluateImperativeProgram(
  program: ImperativeProgram,
  env: { project: Project; workDir: string; counts: ImperativeCounts; timeoutSec?: number; stages?: DafnyStage[] },
  hooks?: EvaluateHooks,
): ImperativeOutcome {
  env.counts.programs++;
  const timeoutSec = env.timeoutSec ?? 15;
  const stages: DafnyStage[] = env.stages ?? ["pre", "opt"];

  const tsErr = checkTypeScriptValid(program.tsText, env.project);
  if (tsErr) {
    env.counts.invalidTs++;
    return {
      ok: false,
      oracle: "invalid-ts",
      signature: `invalid-ts (${program.family}/${program.label}): ${normalize(tsErr.split("\n")[0])}`,
      detail: tsErr,
      family: program.family,
      label: program.label,
      checks: [],
    };
  }

  const compiledRes = compileDafnyVariants(program.tsText, env.project, hooks);
  if (!compiledRes.ok) {
    env.counts.rejected++;
    return {
      ok: false,
      oracle: "rejected",
      signature: `${compiledRes.failure.signature} (${program.family}/${program.label})`,
      detail: compiledRes.failure.detail,
      family: program.family,
      label: program.label,
      checks: [],
    };
  }

  const { narrowed, userNames, preDfy, optDfy, optChanged } = compiledRes.compiled;
  const irViolations = checkNarrowedModule(narrowed, userNames);
  const checks: ImperativeCheckDetail[] = [];

  let worstOracle: ImperativeOracleKind | null = null;
  let worstStage: FailureStage | undefined;
  let worstDetail = "";

  const severity: Record<ImperativeOracleKind, number> = {
    "soundness-refuted": 100,
    "precondition-dropped": 95,
    "semantic-mismatch": 60,
    "dafny-resolve": 40,
    "timeout": 30,
    "tool-error": 25,
    "rejected": 10,
    "invalid-ts": 10,
  };

  const recordIssue = (oracle: ImperativeOracleKind, stage: DafnyStage, detail: string) => {
    if (!worstOracle || severity[oracle] > severity[worstOracle]) {
      worstOracle = oracle;
      worstStage = stage;
      worstDetail = detail;
    } else if (oracle === worstOracle && worstStage && worstStage !== stage) {
      worstStage = "both";
    }
  };

  for (const stage of stages) {
    const dfy = stage === "pre" ? preDfy : optDfy;
    for (let i = 0; i < program.inputs.length; i++) {
      const inp = program.inputs[i];
      const nodeOutcome = executeImperativeInNode(program.tsText, program.fnName, inp, program.returnKind);
      if (nodeOutcome.kind === "runtime-error") {
        env.counts.invalidTs++;
        return {
          ok: false,
          oracle: "invalid-ts",
          signature: `invalid-ts runtime (${program.family}/${program.label}): ${normalize(nodeOutcome.detail)}`,
          detail: nodeOutcome.detail,
          family: program.family,
          label: program.label,
          preDfy,
          optDfy,
          optChanged,
          checks,
        };
      }
      const dafnyArgs = inp.args.map(a => imperativeArgToDafny(a, dfy));

      if (nodeOutcome.kind === "precondition-violated") {
        const harness = buildSpecializedDafnyCheck(dfy, program.fnName, dafnyArgs, { kind: "precondition-must-fail" }, i);
        if (!harness) {
          checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "resolve-error", detail: `target ${program.fnName} missing in emitted Dafny` });
          recordIssue("dafny-resolve", stage, `target ${program.fnName} missing`);
          continue;
        }
        const res = runDafnyVerifyText(
          harness.text,
          env.workDir,
          `imp_${stage}_precond_${i}.dfy`,
          env.counts,
          timeoutSec,
          harness.symbol,
        );
        if (res.status === "verified") {
          // CRITICAL: JS hit guard(false), yet Dafny verified the call with 0 errors!
          checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "precondition-dropped", detail: res.detail });
          recordIssue("precondition-dropped", stage, `Node violated guard(false) on input #${i} (${dafnyArgs.join(", ")}), but Dafny verified with 0 errors.`);
        } else if (res.status === "verify-error") {
          // Expected: Dafny caught the violated precondition.
          checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "ok", detail: "precondition violation caught by Dafny" });
        } else if (res.status === "resolve-error") {
          checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "resolve-error", detail: res.detail });
          recordIssue("dafny-resolve", stage, res.detail);
        } else if (res.status === "timeout") {
          checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "timeout", detail: res.detail });
          recordIssue("timeout", stage, res.detail);
        } else {
          checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "tool-error", detail: res.detail });
          recordIssue("tool-error", stage, res.detail);
        }
        continue;
      }

      // Normal return value v_js: run (1) negated-postcondition refutation check, then (2) positive agreement.
      const vJs = nodeOutcome.value;
      const refuteHarness = buildSpecializedDafnyCheck(dfy, program.fnName, dafnyArgs, { kind: "refute", expected: vJs }, i);
      if (!refuteHarness) {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "resolve-error", detail: `target ${program.fnName} missing in emitted Dafny` });
        recordIssue("dafny-resolve", stage, `target ${program.fnName} missing`);
        continue;
      }
      const refuteRes = runDafnyVerifyText(
        refuteHarness.text,
        env.workDir,
        `imp_${stage}_refute_${i}.dfy`,
        env.counts,
        timeoutSec,
        refuteHarness.symbol,
      );
      if (refuteRes.status === "verified") {
        // CRITICAL SOUNDNESS BUG: Dafny proved result != v_js!
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "soundness-refuted", detail: refuteRes.detail });
        recordIssue(
          "soundness-refuted",
          stage,
          `CRITICAL: Node returned ${String(vJs)} for ${program.fnName}(${dafnyArgs.join(", ")}), yet Dafny proved result != ${dafnyExpectedLiteral(vJs)}.`,
        );
        continue;
      }
      if (refuteRes.status === "resolve-error") {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "resolve-error", detail: refuteRes.detail });
        recordIssue("dafny-resolve", stage, refuteRes.detail);
        continue;
      }
      if (refuteRes.status === "timeout") {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "timeout", detail: refuteRes.detail });
        recordIssue("timeout", stage, refuteRes.detail);
        continue;
      }
      if (refuteRes.status === "tool-error") {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "tool-error", detail: refuteRes.detail });
        recordIssue("tool-error", stage, refuteRes.detail);
        continue;
      }

      // Refutation failed as expected; now check positive agreement `result == v_js`.
      const posHarness = buildSpecializedDafnyCheck(dfy, program.fnName, dafnyArgs, { kind: "positive", expected: vJs }, i)!;
      const posRes = runDafnyVerifyText(
        posHarness.text,
        env.workDir,
        `imp_${stage}_pos_${i}.dfy`,
        env.counts,
        timeoutSec,
        posHarness.symbol,
      );
      if (posRes.status === "verified") {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "ok", detail: "verified" });
      } else if (posRes.status === "verify-error") {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "semantic-mismatch", detail: posRes.detail });
        recordIssue("semantic-mismatch", stage, `Dafny could not prove ${program.fnName}(${dafnyArgs.join(", ")}) == ${dafnyExpectedLiteral(vJs)}.`);
      } else if (posRes.status === "resolve-error") {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "resolve-error", detail: posRes.detail });
        recordIssue("dafny-resolve", stage, posRes.detail);
      } else if (posRes.status === "timeout") {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "timeout", detail: posRes.detail });
        recordIssue("timeout", stage, posRes.detail);
      } else {
        checks.push({ inputIndex: i, nodeOutcome, dafnyArgs, stage, status: "tool-error", detail: posRes.detail });
        recordIssue("tool-error", stage, posRes.detail);
      }
    }
  }

  if (!worstOracle) {
    env.counts.passed++;
    return {
      ok: true,
      signature: `ok (${program.family}/${program.label})`,
      detail: `${checks.length} checks verified (refutation rejected, positive proved)`,
      family: program.family,
      label: program.label,
      preDfy,
      optDfy,
      optChanged,
      irViolations,
      checks,
    };
  }

  switch (worstOracle) {
    case "soundness-refuted": env.counts.soundnessRefuted++; break;
    case "precondition-dropped": env.counts.preconditionDropped++; break;
    case "semantic-mismatch": env.counts.semanticMismatch++; break;
    case "dafny-resolve": env.counts.dafnyResolve++; break;
    case "timeout": env.counts.timeout++; break;
    case "tool-error": env.counts.toolError++; break;
  }

  return {
    ok: false,
    oracle: worstOracle,
    stage: worstStage,
    signature: `${worstOracle} (${program.family}/${program.label})`,
    detail: worstDetail,
    family: program.family,
    label: program.label,
    preDfy,
    optDfy,
    optChanged,
    irViolations,
    checks,
  };
}

// ── Lossless .semantic.json save & replay ───────────────────

export function saveImperativeCase(
  filePath: string,
  program: ImperativeProgram,
  outcome: ImperativeOutcome,
): SavedImperativeCase {
  const saved: SavedImperativeCase = {
    schema: IMPERATIVE_SCHEMA,
    family: program.family,
    label: program.label,
    fnName: program.fnName,
    returnKind: program.returnKind,
    tsText: program.tsText,
    inputs: program.inputs,
    oracle: outcome.ok ? "ok" : (outcome.oracle ?? "tool-error"),
    stage: outcome.stage ?? null,
    signature: outcome.signature,
    detail: outcome.detail,
    checks: outcome.checks,
  };
  mkdirSync(path.dirname(filePath), { recursive: true });
  writeFileSync(filePath, JSON.stringify(saved, null, 2) + "\n");
  return saved;
}

export function replaySavedImperativeCase(
  casePath: string,
  opts?: { timeoutSec?: number; stages?: DafnyStage[] },
): ImperativeOutcome {
  const raw = JSON.parse(readFileSync(casePath, "utf8")) as SavedImperativeCase;
  if (raw.schema !== IMPERATIVE_SCHEMA) {
    throw new Error(`Unsupported imperative semantic case schema: ${String((raw as { schema?: unknown }).schema)}`);
  }
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-imp-replay-"));
  try {
    const counts = createImperativeCounts();
    return evaluateImperativeProgram(
      {
        family: raw.family,
        label: raw.label,
        fnName: raw.fnName,
        returnKind: raw.returnKind,
        tsText: raw.tsText,
        inputs: raw.inputs,
      },
      { project, workDir, counts, timeoutSec: opts?.timeoutSec ?? 15, stages: opts?.stages ?? ["pre", "opt"] },
    );
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
}

// ── Batched `dafny run --no-verify` fast screening mode ─────

export interface BatchedScreenEntry {
  id: string;
  dfy: string;
  fnName: string;
  dafnyArgs: string[];
  expectedJs: number | boolean;
}

export interface BatchedScreenResult {
  ok: boolean;
  divergences: Array<{ id: string; expected: string; actual: string }>;
  matched: number;
  error?: string;
}

/**
 * Pack multiple compiled Dafny modules + concrete inputs into a single `.dfy`
 * with a `Main()` driver and execute `dafny run --no-verify` once.
 * Returns any cases whose Dafny runtime output differs from Node's expected value.
 */
/**
 * Extract top-level datatype names and constructor names declared in emitted Dafny
 * so `Main()` can qualify every constructor argument (including union variants like `a(...)`/`b(...)`).
 */
function extractDafnyDatatypeSymbols(dfy: string): string[] {
  const syms = new Set<string>(["Option", "Nullish", "Box"]);
  const dtRe = /^\s*datatype\s+(\w+)(?:<[^>]*>)?\s*=\s*(.+)$/gm;
  let m: RegExpExecArray | null;
  while ((m = dtRe.exec(dfy)) !== null) {
    syms.add(m[1]);
    for (const arm of m[2].split("|")) {
      const cm = arm.trim().match(/^(\w+)/);
      if (cm) syms.add(cm[1]);
    }
  }
  return [...syms];
}

function qualifyDafnyArgForModule(arg: string, modName: string, symbols: string[]): string {
  if (symbols.length === 0) return arg;
  const escaped = symbols.map(s => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")).join("|");
  // Single pass: preserve string literals; qualify bare datatype names (`Option.Some`, `Nullish.None`)
  // and bare constructor calls (`a(5)`, `b([1])`, `Box(...)`) not already preceded by `.`.
  const re = new RegExp(`"(?:[^"\\\\]|\\\\.)*"|(?<!\\.)\\b(${escaped})(?=\\s*(?:\\(|\\.))`, "g");
  return arg.replace(re, (full, ident: string | undefined) => (ident ? `${modName}.${ident}` : full));
}

export function runBatchedDafnyFastScreen(
  entries: BatchedScreenEntry[],
  workDir: string,
  timeoutSec = 30,
): BatchedScreenResult {
  if (entries.length === 0) return { ok: true, divergences: [], matched: 0 };

  const moduleBlocks: string[] = [];
  const mainLines: string[] = [];

  for (let i = 0; i < entries.length; i++) {
    const e = entries[i];
    const modName = `Case_${i}`;
    const parsed = parseTargetHeader(e.dfy, e.fnName);
    if (!parsed) {
      return { ok: false, divergences: [], matched: 0, error: `Case ${e.id}: target ${e.fnName} not found in Dafny output` };
    }
    const indented = e.dfy
      .split("\n")
      .map(line => `  ${line}`)
      .join("\n");
    moduleBlocks.push(`module ${modName} {\n${indented}\n}`);
    const dtSyms = extractDafnyDatatypeSymbols(e.dfy);
    const qualifiedArgs = e.dafnyArgs
      .map(a => qualifyDafnyArgForModule(a, modName, dtSyms))
      .join(", ");
    mainLines.push(`  var r_${i} := ${modName}.${e.fnName}(${qualifiedArgs});`);
    mainLines.push(`  print "CASE ${i} ", r_${i}, "\\n";`);
  }

  const combined = `${moduleBlocks.join("\n\n")}\n\nmethod Main() {\n${mainLines.join("\n")}\n}\n`;
  const filePath = path.join(workDir, "batched_screen.dfy");
  writeFileSync(filePath, combined);

  const res = spawnSync("dafny", ["run", "--no-verify", filePath], {
    encoding: "utf8",
    timeout: timeoutSec * 1000,
    maxBuffer: 10 * 1024 * 1024,
  });
  const stdout = res.stdout ?? "";
  const stderr = res.stderr ?? "";
  if (res.error || res.status !== 0) {
    return {
      ok: false,
      divergences: [],
      matched: 0,
      error: res.error?.message || `${stdout}\n${stderr}`.trim() || `dafny run exited ${res.status}`,
    };
  }

  const observed = new Map<number, string>();
  for (const line of stdout.split(/\r?\n/)) {
    const m = line.match(/^CASE\s+(\d+)\s+(.*)$/);
    if (m) observed.set(Number(m[1]), m[2].trim());
  }

  const divergences: Array<{ id: string; expected: string; actual: string }> = [];
  let matched = 0;
  for (let i = 0; i < entries.length; i++) {
    const expected = String(entries[i].expectedJs);
    const actual = observed.get(i);
    if (actual === undefined) {
      return { ok: false, divergences, matched, error: `missing CASE ${i} in dafny run output` };
    }
    if (actual !== expected) {
      divergences.push({ id: entries[i].id, expected, actual });
    } else {
      matched++;
    }
  }
  return { ok: divergences.length === 0, divergences, matched };
}

// ── Imperative, Mutation, Union, Nullish & Aliasing Generator ─

const smallIntArb = fc.integer({ min: -10, max: 10 });
const smallArrArb = fc.array(smallIntArb, { minLength: 0, maxLength: 3 });

function genReassignProgram(): fc.Arbitrary<ImperativeProgram> {
  return fc.record({
    variant: fc.constantFrom("present-to-absent", "absent-to-present", "present-to-present", "nested-field-reassign"),
    c1: smallIntArb,
    c2: smallIntArb,
    x0: fc.option(smallIntArb, { nil: undefined }),
    x1: fc.option(smallIntArb, { nil: undefined }),
  }).map(({ variant, c1, c2, x0, x1 }) => {
    if (variant === "present-to-absent") {
      return {
        family: "reassign",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(x?: number): number {",
          "  let v: number | undefined = x;",
          "  if (v !== undefined) {",
          `    if (v > ${c1}) {`,
          "      v = undefined;",
          "    }",
          "  }",
          `  return v !== undefined ? v + ${c2} : -1;`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "opt-int", value: x0 }] }, { args: [{ kind: "opt-int", value: c1 + 2 }] }],
      };
    }
    if (variant === "absent-to-present") {
      return {
        family: "reassign",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(x?: number): number {",
          "  let v: number | undefined = x;",
          "  if (v === undefined) {",
          `    v = ${c1};`,
          "  }",
          `  return v + ${c2};`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "opt-int", value: undefined }] }, { args: [{ kind: "opt-int", value: x1 ?? 3 }] }],
      };
    }
    if (variant === "present-to-present") {
      return {
        family: "reassign",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(x?: number): number {",
          "  let v: number | undefined = x;",
          "  if (v !== undefined) {",
          `    v = v + ${c1};`,
          `    return v + ${c2};`,
          "  }",
          "  return 0;",
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "opt-int", value: undefined }] }, { args: [{ kind: "opt-int", value: x0 ?? 2 }] }],
      };
    }
    return {
      family: "reassign",
      label: variant,
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box): number {",
        "  if (b !== undefined && b.count !== undefined) {",
        `    b.count = b.count + ${c1};`,
        "  }",
        `  return b !== undefined && b.count !== undefined ? b.count : ${c2};`,
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-box", value: undefined }] },
        { args: [{ kind: "opt-box", value: { items: [1], count: x0 } }] },
      ],
    };
  });
}

function genMutationProgram(): fc.Arbitrary<ImperativeProgram> {
  return fc.record({
    variant: fc.constantFrom(
      "opt-array-push",
      "opt-array-pop",
      "array-index-assign",
      "map-set-delete",
      "nested-box-push",
      "map-optchain-push",
    ),
    v: smallIntArb,
    arr: smallArrArb,
  }).map(({ variant, v, arr }) => {
    if (variant === "opt-array-push") {
      return {
        family: "mutation",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(arr?: number[]): number {",
          "  if (arr !== undefined) {",
          `    arr.push(${v});`,
          "  }",
          "  return arr !== undefined ? arr.length : 0;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int-array", value: arr }] },
          { args: [{ kind: "opt-int-array", value: undefined }] },
        ],
      };
    }
    if (variant === "opt-array-pop") {
      return {
        family: "mutation",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(arr?: number[]): number {",
          "  if (arr !== undefined && arr.length > 0) {",
          "    const last = arr.pop();",
          "    return last !== undefined ? last + arr.length : -1;",
          "  }",
          "  return 0;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int-array", value: arr.length > 0 ? arr : [v] }] },
          { args: [{ kind: "opt-int-array", value: [] }] },
        ],
      };
    }
    if (variant === "array-index-assign") {
      return {
        family: "mutation",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(arr?: number[]): number {",
          "  if (arr !== undefined && arr.length > 0) {",
          `    arr[0] = ${v};`,
          "    return arr[0];",
          "  }",
          "  return -1;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int-array", value: arr.length > 0 ? arr : [1] }] },
          { args: [{ kind: "opt-int-array", value: undefined }] },
        ],
      };
    }
    if (variant === "map-set-delete") {
      return {
        family: "mutation",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(m: Map<string, number>): number {",
          `  m.set("k", ${v});`,
          '  if (m.has("del")) {',
          '    m.delete("del");',
          "  }",
          '  const got = m.get("k");',
          '  return got !== undefined && !m.has("del") ? got : -1;',
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "int-map", value: [["del", 1]] }] },
          { args: [{ kind: "int-map", value: [] }] },
        ],
      };
    }
    if (variant === "nested-box-push") {
      return {
        family: "mutation",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export interface Box { items?: number[]; count?: number }",
          "export function target(b?: Box): number {",
          "  if (b !== undefined && b.items !== undefined) {",
          `    b.items.push(${v});`,
          "  }",
          "  return b !== undefined && b.items !== undefined ? b.items.length : -1;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-box", value: { items: arr, count: 1 } }] },
          { args: [{ kind: "opt-box", value: { items: undefined, count: 1 } }] },
        ],
      };
    }
    return {
      family: "mutation",
      label: variant,
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(m: Map<string, number[]>): number {",
        `  m.get("a")?.push(${v});`,
        '  const got = m.get("a");',
        "  return got !== undefined ? got.length : 0;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "arr-map", value: [["a", arr]] }] },
        { args: [{ kind: "arr-map", value: [] }] },
      ],
    };
  });
}

function genLoopShadowProgram(): fc.Arbitrary<ImperativeProgram> {
  return fc.record({
    variant: fc.constantFrom("shadow-const-in-if", "while-presence-countdown"),
    c: fc.integer({ min: 1, max: 4 }),
    x: fc.option(fc.integer({ min: 0, max: 5 }), { nil: undefined }),
  }).map(({ variant, c, x }) => {
    if (variant === "shadow-const-in-if") {
      return {
        family: "loop-shadow",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(x?: number): number {",
          "  if (x !== undefined) {",
          `    const y = x + ${c};`,
          "    if (y > 0) {",
          `      const x = ${c * 10};`,
          "      return x + y;",
          "    }",
          "    return x;",
          "  }",
          "  return -1;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int", value: x ?? 2 }] },
          { args: [{ kind: "opt-int", value: undefined }] },
        ],
      };
    }
    return {
      family: "loop-shadow",
      label: variant,
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(start?: number): number {",
        "  let cur: number | undefined = start;",
        "  let steps = 0;",
        "  let total = 0;",
        `  while (cur !== undefined && steps < ${c}) {`,
        "    total = total + cur;",
        "    steps = steps + 1;",
        "    cur = cur > 0 ? cur - 1 : undefined;",
        "  }",
        "  return total;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int", value: x ?? 2 }] },
        { args: [{ kind: "opt-int", value: undefined }] },
      ],
    };
  });
}

function genUnionProgram(): fc.Arbitrary<ImperativeProgram> {
  return fc.record({
    variant: fc.constantFrom("union-if-read", "union-switch-mutate"),
    v: smallIntArb,
    arr: smallArrArb,
  }).map(({ variant, v, arr }) => {
    if (variant === "union-if-read") {
      return {
        family: "union",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
          "export function target(u: Item): number {",
          '  if (u.kind === "a") {',
          `    return u.v + ${v};`,
          "  }",
          "  return u.items.length;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "union-ab", value: { kind: "a", v } }] },
          { args: [{ kind: "union-ab", value: { kind: "b", items: arr } }] },
        ],
      };
    }
    return {
      family: "union",
      label: variant,
      fnName: "target",
      returnKind: "number",
      tsText: [
        'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
        "export function target(u: Item): number {",
        "  switch (u.kind) {",
        '    case "a":',
        `      return u.v + ${v};`,
        '    case "b":',
        `      u.items.push(${v});`,
        "      break;",
        "  }",
        '  return u.kind === "b" ? u.items.length : -1;',
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "union-ab", value: { kind: "b", items: arr } }] },
        { args: [{ kind: "union-ab", value: { kind: "a", v } }] },
      ],
    };
  });
}

function genNullishFalsyProgram(): fc.Arbitrary<ImperativeProgram> {
  return fc.record({
    variant: fc.constantFrom(
      "null-vs-undefined-eq",
      "null-then-undefined-branch",
      "falsy-zero-vs-undefined",
      "falsy-empty-str-vs-undefined",
      "falsy-false-vs-undefined",
      "falsy-empty-arr-vs-undefined",
      "nullish-coalesce-zero",
    ),
    fallback: fc.integer({ min: 1, max: 10 }),
  }).map(({ variant, fallback }) => {
    if (variant === "null-vs-undefined-eq") {
      return {
        family: "nullish-falsy",
        label: variant,
        fnName: "target",
        returnKind: "boolean",
        tsText: [
          "export function target(x: number | null | undefined): boolean {",
          "  return x === null;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "nullish-int", value: null }] },
          { args: [{ kind: "nullish-int", value: undefined }] },
          { args: [{ kind: "nullish-int", value: 0 }] },
        ],
      };
    }
    if (variant === "null-then-undefined-branch") {
      return {
        family: "nullish-falsy",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(x: number | null | undefined): number {",
          "  if (x === null) return 1;",
          "  if (x === undefined) return 2;",
          "  return x + 10;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "nullish-int", value: null }] },
          { args: [{ kind: "nullish-int", value: undefined }] },
          { args: [{ kind: "nullish-int", value: 0 }] },
        ],
      };
    }
    if (variant === "falsy-zero-vs-undefined") {
      return {
        family: "nullish-falsy",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(x?: number): number {",
          `  if (x) return x + ${fallback};`,
          "  if (x === undefined) return -1;",
          "  return 0;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int", value: 0 }] },
          { args: [{ kind: "opt-int", value: undefined }] },
          { args: [{ kind: "opt-int", value: 3 }] },
        ],
      };
    }
    if (variant === "falsy-empty-str-vs-undefined") {
      return {
        family: "nullish-falsy",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(s?: string): number {",
          `  if (s) return s.length + ${fallback};`,
          "  if (s === undefined) return -1;",
          "  return 0;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-str", value: "" }] },
          { args: [{ kind: "opt-str", value: undefined }] },
          { args: [{ kind: "opt-str", value: "hi" }] },
        ],
      };
    }
    if (variant === "falsy-false-vs-undefined") {
      return {
        family: "nullish-falsy",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(flag?: boolean): number {",
          `  if (flag) return ${fallback};`,
          "  if (flag === undefined) return -1;",
          "  return 0;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-bool", value: false }] },
          { args: [{ kind: "opt-bool", value: undefined }] },
          { args: [{ kind: "opt-bool", value: true }] },
        ],
      };
    }
    if (variant === "falsy-empty-arr-vs-undefined") {
      return {
        family: "nullish-falsy",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          "export function target(arr?: number[]): number {",
          `  if (arr) return arr.length + ${fallback};`,
          "  return -1;",
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int-array", value: [] }] },
          { args: [{ kind: "opt-int-array", value: undefined }] },
        ],
      };
    }
    return {
      family: "nullish-falsy",
      label: variant,
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(x?: number): number {",
        `  return x ?? ${fallback};`,
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int", value: 0 }] },
        { args: [{ kind: "opt-int", value: undefined }] },
      ],
    };
  });
}

function genAliasingProgram(): fc.Arbitrary<ImperativeProgram> {
  return fc.record({
    variant: fc.constantFrom("live-alias-mutation", "dead-source-move", "read-only-alias"),
    v: smallIntArb,
    arr: smallArrArb,
  }).map(({ variant, v, arr }) => {
    if (variant === "live-alias-mutation") {
      return {
        family: "aliasing",
        label: variant,
        fnName: "target",
        returnKind: "number",
        isLiveAliasMutation: true,
        tsText: [
          "export function target(a: number[]): number {",
          "  const b = a;",
          `  b.push(${v});`,
          "  return a.length;",
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "int-array", value: arr }] }],
      };
    }
    if (variant === "dead-source-move") {
      return {
        family: "aliasing",
        label: variant,
        fnName: "target",
        returnKind: "number",
        isLiveAliasMutation: false,
        tsText: [
          "export function target(a: number[]): number {",
          "  const b = a;",
          `  b.push(${v});`,
          "  return b.length;",
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "int-array", value: arr }] }],
      };
    }
    return {
      family: "aliasing",
      label: variant,
      fnName: "target",
      returnKind: "number",
      isLiveAliasMutation: false,
      tsText: [
        "export function target(a: number[]): number {",
        "  const b = a;",
        "  return a.length + b.length;",
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "int-array", value: arr }] }],
    };
  });
}

function genGuardEvalProgram(): fc.Arbitrary<ImperativeProgram> {
  return fc.record({
    variant: fc.constantFrom(
      "eq-rhs-guard-false",
      "neq-rhs-guard-false",
      "le-rhs-guard-false",
      "lt-rhs-guard-false",
      "and-short-circuit-guard-false",
      "or-short-circuit-guard-false",
      "optchain-short-circuit-guard-false",
      "nullish-short-circuit-guard-false",
      "call-arg-guard-false",
    ),
    v: smallIntArb,
  }).map(({ variant, v }) => {
    const guardDef = [
      "//@ requires ok",
      "export function guard(ok: boolean, v: number): number {",
      "  return v;",
      "}",
    ].join("\n");
    if (variant === "eq-rhs-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "boolean",
        tsText: [
          guardDef,
          "export function target(x?: number): boolean {",
          `  return x === guard(false, ${v});`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
      };
    }
    if (variant === "neq-rhs-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "boolean",
        tsText: [
          guardDef,
          "export function target(x?: number): boolean {",
          `  return x !== guard(false, ${v});`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
      };
    }
    if (variant === "le-rhs-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "boolean",
        tsText: [
          guardDef,
          "export function target(x?: number): boolean {",
          `  return x !== undefined && x <= guard(false, ${v});`,
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int", value: undefined }] },
          { args: [{ kind: "opt-int", value: v }] },
        ],
      };
    }
    if (variant === "lt-rhs-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "boolean",
        tsText: [
          guardDef,
          "export function target(x?: number): boolean {",
          `  return x !== undefined && x < guard(false, ${v});`,
          "}",
        ].join("\n"),
        inputs: [
          { args: [{ kind: "opt-int", value: undefined }] },
          { args: [{ kind: "opt-int", value: v - 1 }] },
        ],
      };
    }
    if (variant === "and-short-circuit-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "boolean",
        tsText: [
          guardDef,
          "export function target(flag: boolean): boolean {",
          `  return flag && guard(false, ${v}) > 0;`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "bool", value: false }] }],
      };
    }
    if (variant === "or-short-circuit-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "boolean",
        tsText: [
          guardDef,
          "export function target(flag: boolean): boolean {",
          `  return flag || guard(false, ${v}) > 0;`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "bool", value: true }] }],
      };
    }
    if (variant === "optchain-short-circuit-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          guardDef,
          "export function target(arr?: number[]): number {",
          `  const hit = arr?.[guard(false, 0)];`,
          `  return hit ?? ${v};`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "opt-int-array", value: undefined }] }],
      };
    }
    if (variant === "call-arg-guard-false") {
      return {
        family: "guard-eval",
        label: variant,
        fnName: "target",
        returnKind: "number",
        tsText: [
          guardDef,
          "export function id(n: number): number { return n; }",
          "export function target(x?: number): number {",
          `  return id(guard(false, ${v})) + (x ?? 0);`,
          "}",
        ].join("\n"),
        inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
      };
    }
    return {
      family: "guard-eval",
      label: variant,
      fnName: "target",
      returnKind: "number",
      tsText: [
        guardDef,
        "export function target(x?: number): number {",
        `  return x ?? guard(false, ${v});`,
        "}",
      ].join("\n"),
      inputs: [{ args: [{ kind: "opt-int", value: 5 }] }],
    };
  });
}

export function imperativeProgramArb(
  families: readonly ImperativeFamily[] = IMPERATIVE_FAMILIES,
): fc.Arbitrary<ImperativeProgram> {
  const arbs: fc.Arbitrary<ImperativeProgram>[] = [];
  for (const fam of families) {
    switch (fam) {
      case "reassign": arbs.push(genReassignProgram()); break;
      case "mutation": arbs.push(genMutationProgram()); break;
      case "loop-shadow": arbs.push(genLoopShadowProgram()); break;
      case "union": arbs.push(genUnionProgram()); break;
      case "nullish-falsy": arbs.push(genNullishFalsyProgram()); break;
      case "aliasing": arbs.push(genAliasingProgram()); break;
      case "guard-eval": arbs.push(genGuardEvalProgram()); break;
    }
  }
  return fc.oneof(...arbs);
}

// ── Campaign runner ─────────────────────────────────────────

export interface ImperativeCampaignOptions {
  seed: number;
  runs: number;
  families: readonly ImperativeFamily[];
  out: string;
  timeoutSec: number;
  stages?: DafnyStage[];
  fastRun?: boolean;
}

export interface ImperativeCampaignSummary {
  seed: number;
  runs: number;
  families: readonly ImperativeFamily[];
  counts: ImperativeCounts;
  fastRunScreened?: number;
  fastRunDivergences?: number;
  classes: Array<{
    classIndex: number;
    oracle: ImperativeOracleKind;
    stage: FailureStage | null;
    family: ImperativeFamily;
    label: string;
    signature: string;
    detail: string;
    irViolationCount: number;
    tsFile: string;
    caseFile: string;
  }>;
  elapsedSeconds: number;
}

export function runImperativeCampaign(opts: ImperativeCampaignOptions): ImperativeCampaignSummary {
  const started = Date.now();
  mkdirSync(opts.out, { recursive: true });
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-imp-fuzz-"));
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
  const counts = createImperativeCounts();
  const seen = new Set<string>();
  const classes: ImperativeCampaignSummary["classes"] = [];
  const stages: DafnyStage[] = opts.stages ?? ["pre", "opt"];
  let fastRunScreened = 0;
  let fastRunDivergences = 0;

  try {
    if (opts.fastRun) {
      // Fast-run mode: sample candidate programs, compile them, run batched `dafny run --no-verify`
      // on all value-returning inputs in one invocation, then confirm flagged divergences and
      // precondition-violating inputs with `dafny verify`.
      const samples = fc.sample(imperativeProgramArb(opts.families), {
        seed: opts.seed,
        numRuns: opts.runs,
      });
      const batchEntries: BatchedScreenEntry[] = [];
      const progByEntry = new Map<string, ImperativeProgram>();
      const verifyQueue: ImperativeProgram[] = [];

      for (let pi = 0; pi < samples.length; pi++) {
        const prog = samples[pi];
        const compiled = compileDafnyVariants(prog.tsText, project);
        if (!compiled.ok) {
          verifyQueue.push(prog);
          continue;
        }
        let needsDirectVerify = false;
        for (let ii = 0; ii < prog.inputs.length; ii++) {
          const nodeRes = executeImperativeInNode(prog.tsText, prog.fnName, prog.inputs[ii], prog.returnKind);
          if (nodeRes.kind === "precondition-violated" || nodeRes.kind === "runtime-error") {
            needsDirectVerify = true;
          } else if (nodeRes.kind === "value") {
            const id = `p${pi}_i${ii}`;
            batchEntries.push({
              id,
              dfy: compiled.compiled.optDfy,
              fnName: prog.fnName,
              dafnyArgs: prog.inputs[ii].args.map(a => imperativeArgToDafny(a, compiled.compiled.optDfy)),
              expectedJs: nodeRes.value,
            });
            progByEntry.set(id, prog);
          }
        }
        if (needsDirectVerify) verifyQueue.push(prog);
      }

      if (batchEntries.length > 0) {
        fastRunScreened = batchEntries.length;
        const screen = runBatchedDafnyFastScreen(batchEntries, workDir, Math.max(30, opts.timeoutSec * 2));
        if (screen.error) {
          // Batch contained a program that failed Dafny resolution; fall back to per-program verify.
          for (const prog of samples) {
            if (!verifyQueue.includes(prog)) verifyQueue.push(prog);
          }
        } else {
          fastRunDivergences = screen.divergences.length;
          for (const div of screen.divergences) {
            const prog = progByEntry.get(div.id);
            if (prog && !verifyQueue.includes(prog)) verifyQueue.push(prog);
          }
        }
      }

      for (const prog of verifyQueue) {
        const outcome = evaluateImperativeProgram(prog, {
          project,
          workDir,
          counts,
          timeoutSec: opts.timeoutSec,
          stages,
        });
        const lockKey = `${outcome.signature}@${outcome.stage ?? "none"}`;
        if (!outcome.ok && outcome.oracle && !seen.has(lockKey)) {
          seen.add(lockKey);
          const idx = classes.length + 1;
          const tsFile = path.join(opts.out, `${idx}.ts`);
          const caseFile = path.join(opts.out, `${idx}.semantic.json`);
          writeFileSync(tsFile, prog.tsText + "\n");
          saveImperativeCase(caseFile, prog, outcome);
          classes.push({
            classIndex: idx,
            oracle: outcome.oracle,
            stage: outcome.stage ?? null,
            family: prog.family,
            label: prog.label,
            signature: outcome.signature,
            detail: outcome.detail,
            irViolationCount: outcome.irViolations?.length ?? 0,
            tsFile,
            caseFile,
          });
        }
      }
    } else {
      // Standard verification campaign with stage-locked `fc.check` shrinking per distinct (signature, stage).
      const maxRounds = Math.max(1, Math.min(20, opts.runs));
      let remaining = opts.runs;
      for (let round = 0; round < maxRounds && remaining > 0; round++) {
        let lockedKey: string | null = null;
        let shrunkProg: ImperativeProgram | null = null;
        let shrunkOutcome: ImperativeOutcome | null = null;
        let evalsInRound = 0;
        let shrinkEvals = 0;
        const MAX_SHRINK_EVALS = 12;

        const prop = fc.property(imperativeProgramArb(opts.families), (prog) => {
          evalsInRound++;
          if (lockedKey !== null) {
            if (shrinkEvals >= MAX_SHRINK_EVALS) return true;
            shrinkEvals++;
          }
          const outcome = evaluateImperativeProgram(prog, {
            project,
            workDir,
            counts,
            timeoutSec: opts.timeoutSec,
            stages,
          });
          if (outcome.ok || !outcome.oracle) return true;
          const lockKey = `${outcome.signature}@${outcome.stage ?? "none"}`;
          if (seen.has(lockKey)) return true;
          if (lockedKey === null) {
            lockedKey = lockKey;
            shrunkProg = prog;
            shrunkOutcome = outcome;
            return false;
          }
          if (lockKey === lockedKey) {
            shrunkProg = prog;
            shrunkOutcome = outcome;
            return false;
          }
          return true;
        });

        const checkRes = fc.check(prop, {
          seed: opts.seed + round,
          numRuns: remaining,
          maxSkipsPerRun: 0,
        });
        remaining -= Math.min(remaining, Math.max(1, checkRes.numRuns));

        if (!checkRes.failed || !lockedKey || !shrunkProg || !shrunkOutcome) {
          break;
        }
        const finalProg: ImperativeProgram = shrunkProg;
        const finalOutcome: ImperativeOutcome = shrunkOutcome;
        seen.add(lockedKey);
        const idx = classes.length + 1;
        const tsFile = path.join(opts.out, `${idx}.ts`);
        const caseFile = path.join(opts.out, `${idx}.semantic.json`);
        writeFileSync(tsFile, finalProg.tsText + "\n");
        saveImperativeCase(caseFile, finalProg, finalOutcome);
        classes.push({
          classIndex: idx,
          oracle: finalOutcome.oracle!,
          stage: finalOutcome.stage ?? null,
          family: finalProg.family,
          label: finalProg.label,
          signature: finalOutcome.signature,
          detail: finalOutcome.detail,
          irViolationCount: finalOutcome.irViolations?.length ?? 0,
          tsFile,
          caseFile,
        });
        if (evalsInRound === 0) break;
      }
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }

  return {
    seed: opts.seed,
    runs: opts.runs,
    families: opts.families,
    counts,
    ...(opts.fastRun ? { fastRunScreened, fastRunDivergences } : {}),
    classes,
    elapsedSeconds: Number(((Date.now() - started) / 1000).toFixed(1)),
  };
}
