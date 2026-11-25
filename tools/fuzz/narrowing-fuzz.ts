/**
 * Narrowing fuzzer: generates small TypeScript modules that guard optional
 * values and then use them, compiles each module in-process through both
 * pre-optimization and production-optimized (peephole) Dafny pipelines, and
 * reports modules the compiler mishandles.
 *
 * Each module goes through extract → resolve → narrow → autoHavoc → transform.
 * The narrowed IR is checked by `checkNarrowedModule` (see src/narrow-checks.ts).
 * Modules that pass those checks emit both pre-optimization Dafny and
 * production-optimized Dafny (`peepholeModule` applied separately to `typesFile`
 * and `defFile`, matching `src/lsc.ts`), and run `dafny resolve` on both
 * variants so pre-optimization and optimization regressions are attributed
 * separately (`dafny-pre`, `dafny-opt`, `dafny-both`).
 * A compiler exception is reported as a rejection, a module with TypeScript
 * errors as a generator bug (`invalid-ts`), and Dafny timeouts/errors as
 * `timeout` / `tool-error` (never counted as completed passing checks).
 *
 * Failures are grouped by oracle/stage and a normalized message. Each round
 * runs fast-check and locks the round's failure stage once the first unseen
 * failure is found, so shrinking preserves the stage while keeping `--seed` /
 * `--path` replay exact.
 *
 * Saved artifacts per class `N`:
 *   N.ts        generated TypeScript source
 *   N.pre.dfy   pre-optimization Dafny (when emitted)
 *   N.opt.dfy   production-optimized Dafny (when emitted)
 *   N.meta.json stage, oracle, signature, replay command, and tool metadata
 *
 * Usage (from tools/):
 *   npm run fuzz:narrowing -- [--seed N] [--runs N] [--classes N] [--minutes N] [--out DIR] [--positions P,Q]
 *   npm run fuzz:narrowing -- --seed N --path P   replay one round's counterexample
 *   npm run fuzz:narrowing -- --file DIR/1.ts     run the oracles on a saved module
 *   npm run fuzz:semantic  -- [--seed N] [--runs N] [--inputs-per-fn K] [--classes N] [--minutes N] [--verify-timeout S] [--out DIR] [--positions P,Q]
 *   npm run fuzz:semantic  -- --seed N --inputs-per-fn K --path P   replay one semantic counterexample
 *   npm run fuzz:semantic  -- --case DIR/1.semantic.json            replay a saved semantic case without reshrinking
 *
 * Defaults: seed 1, 150 runs per round, stop after 12 classes or 9 minutes.
 * `--positions` limits the statement forms generated (names in POSITIONS),
 * for example to search past a known bug in `&&`/`||` chains used as values.
 * The replay command printed for each class includes any `--positions` used.
 * `--minutes` is checked between fast-check runs, so one slow `dafny resolve`
 * call can overrun it.
 * Needs `dafny` on PATH. Exits 1 when it reports an oracle failure, timeout,
 * tool error, or generator bug; rejection classes are listed but do not change
 * the exit code.
 */

import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseArgs } from "node:util";
import fc from "fast-check";
import { Project, ScriptTarget, SyntaxKind } from "ts-morph";
import { extractModule } from "../src/extract.js";
import { resolveModule } from "../src/resolve.js";
import { assertNoLiveAliasMutations } from "../src/alias-check-pass.js";
import { narrowModule } from "../src/narrow.js";
import { autoHavocModule } from "../src/autohavoc.js";
import { checkNarrowedModule } from "../src/narrow-checks.js";
import { transformModuleDafny } from "../src/transform.js";
import { peepholeModule } from "../src/peephole.js";
import { emitDafnyFile } from "../src/dafny-emit.js";
import { parseFileOptions, resolveOptions, type LscOptions } from "../src/config.js";
import type { Module } from "../src/ir.js";
import type { TModule } from "../src/typedir.js";

// ── Generated programs ──────────────────────────────────────

/** An optional number reachable from the parameters, and the optional paths that must be guarded before it. */
export interface Target { path: string; prereqs: string[]; nullable: boolean }

export const TARGETS: Target[] = [
  { path: "o", prereqs: [], nullable: false },
  { path: "p", prereqs: [], nullable: false },
  { path: "n", prereqs: [], nullable: true },
  { path: "a_b", prereqs: [], nullable: false },
  { path: "a.b", prereqs: [], nullable: false },
  { path: "a.v", prereqs: [], nullable: false },
  { path: "a.inner.value", prereqs: ["a.inner"], nullable: false },
  { path: "box.b", prereqs: ["box"], nullable: false },
  { path: "box.inner.value", prereqs: ["box", "box.inner"], nullable: false },
];

// Required parameters first: TypeScript rejects a required parameter after an optional one.
export const PARAMS: Record<string, string> = {
  n: "n: number | null", a: "a: Box", o: "o?: number", p: "p?: number", a_b: "a_b?: number", box: "box?: Box",
};

export const POSITIONS = [
  "returnAnd", "constAnd", "callArg", "returnOr", "ifThen", "ifElse", "ternaryBool",
  "ternaryValue", "ifValue", "earlyReturnOr", "guardThenUse", "nestedIf", "constTernary",
] as const;
export type Position = typeof POSITIONS[number];
export const BOOL_POSITIONS: ReadonlySet<Position> = new Set(["returnAnd", "constAnd", "callArg", "returnOr"]);

export interface FnSpec {
  targets: number[];   // indices into TARGETS
  truthy: boolean[];   // per guard, in order: a truthiness test instead of a comparison
  position: Position;
  use: number;
  ensures: boolean;
}

export function moduleArb(positions: readonly Position[]): fc.Arbitrary<FnSpec[]> {
  const fnArb: fc.Arbitrary<FnSpec> = fc.record({
    targets: fc.uniqueArray(fc.nat(TARGETS.length - 1), { minLength: 1, maxLength: 2 }),
    truthy: fc.array(fc.boolean(), { minLength: 6, maxLength: 6 }),
    position: fc.constantFrom(...positions),
    use: fc.nat(4),
    ensures: fc.boolean(),
  });
  return fc.array(fnArb, { minLength: 1, maxLength: 3 });
}

const indent = (s: string) => s.split("\n").map(l => "  " + l).join("\n");

export function renderFn(spec: FnSpec, name: string, opts?: { omitEnsures?: boolean }): string {
  const targets = spec.targets.map(i => TARGETS[i]);
  const guards: { path: string; missing: string }[] = [];
  for (const t of targets) {
    for (const pre of t.prereqs) if (!guards.some(g => g.path === pre)) guards.push({ path: pre, missing: "undefined" });
    guards.push({ path: t.path, missing: t.nullable ? "null" : "undefined" });
  }
  const present = guards.map((g, i) => spec.truthy[i] ? g.path : `${g.path} !== ${g.missing}`);
  const absent = guards.map((g, i) => spec.truthy[i] ? `!${g.path}` : `${g.path} === ${g.missing}`);
  const has = present.join(" && ");
  // A chain used as a boolean value needs boolean operands: `o && x < o` has type number | boolean | undefined.
  const hasBool = guards.map((g, i) => spec.truthy[i] ? `!!${g.path}` : present[i]).join(" && ");
  const lacks = absent.join(" || ");

  const term = targets.map(t => t.path).join(" + ");
  const cond = [`x < ${term}`, `${term} + 1 > x`, `${term} > 0`, `${term} - x > 0`, `idn(${term}) > x`][spec.use];
  const value = [term, `${term} + 1`, `${term} - x`, `idn(${term})`, `${term} * 2`][spec.use];

  let nested = `return ${value};`;
  for (const g of [...present].reverse()) nested = `if (${g}) {\n${indent(nested)}\n}`;

  const body: Record<Position, string> = {
    returnAnd: `return ${hasBool} && ${cond};`,
    constAnd: `const ok = ${hasBool} && ${cond};\nreturn ok;`,
    callArg: `return check(${hasBool} && ${cond});`,
    returnOr: `return ${lacks} || ${cond};`,
    ifThen: `if (${has} && ${cond}) {\n  return 1;\n}\nreturn 0;`,
    ifElse: `if (${has} && ${cond}) {\n  return 1;\n} else {\n  return 0;\n}`,
    ternaryBool: `return ${has} && ${cond} ? 1 : 0;`,
    ternaryValue: `return ${has} ? ${value} : -1;`,
    ifValue: `if (${has}) {\n  return ${value};\n}\nreturn -1;`,
    earlyReturnOr: `if (${lacks} || ${cond}) return 1;\nreturn 0;`,
    guardThenUse: `if (${lacks}) return -1;\nreturn ${value};`,
    nestedIf: `${nested}\nreturn -1;`,
    constTernary: `const y = ${has} ? ${value} : -1;\nreturn y;`,
  };

  const roots = new Set(guards.map(g => g.path.split(".")[0]));
  const params = ["x: number", ...Object.keys(PARAMS).filter(r => roots.has(r)).map(r => PARAMS[r])];
  const returns = BOOL_POSITIONS.has(spec.position) ? "boolean" : "number";
  const ensures = spec.ensures && !opts?.omitEnsures ? `//@ ensures ${has} ==> ${cond}\n` : "";
  return `export function ${name}(${params.join(", ")}): ${returns} {\n${indent(ensures + body[spec.position])}\n}`;
}

export const PRELUDE = `export interface Leaf { value?: number }
export interface Box { inner?: Leaf; b?: number; v?: number }
export function idn(k: number): number { return k; }
export function check(flag: boolean): boolean { return flag; }
`;

export function renderModule(fns: FnSpec[], opts?: { omitEnsures?: boolean }): string {
  return PRELUDE + "\n" + fns.map((f, i) => renderFn(f, `f${i}`, opts)).join("\n\n") + "\n";
}

// ── Oracles ─────────────────────────────────────────────────

export type DafnyStage = "pre" | "opt";
export type FailureStage = DafnyStage | "both";
export type OracleKind =
  | "invalid-ts"
  | "rejected"
  | "checks"
  | "dafny-pre"
  | "dafny-opt"
  | "dafny-both"
  | "timeout"
  | "tool-error";

export interface Failure {
  oracle: OracleKind;
  stage?: FailureStage;
  signature: string;
  detail: string;
  preDfy?: string;
  optDfy?: string;
  optChanged?: boolean;
}

export type Outcome =
  | { ok: true; preDfy: string; optDfy: string; optChanged: boolean }
  | ({ ok: false } & Failure);

export interface StageCount {
  attempted: number;
  completed: number;
  skipped: Record<string, number>;
}

export interface FuzzCounts {
  modules: number;
  dafnyCalls: number;
  optChanged: number;
  pre: StageCount;
  opt: StageCount;
}

export interface DafnyResolveResult {
  status: "ok" | "error" | "timeout" | "tool-error";
  detail: string | null;
}

export interface EvaluateHooks {
  sourceName?: string;
  optimize?: (mod: Module, backend: "dafny") => Module;
  postEmitOptimized?: (optDfy: string, preDfy: string, text: string) => string;
  resolveDafny?: (dfy: string, stage: DafnyStage) => DafnyResolveResult;
  timeoutMs?: number;
}

export interface CompiledVariants {
  narrowed: TModule;
  userNames: Set<string>;
  preDfy: string;
  optDfy: string;
  optChanged: boolean;
  options: LscOptions;
}

export function createCounts(): FuzzCounts {
  return {
    modules: 0,
    dafnyCalls: 0,
    optChanged: 0,
    pre: { attempted: 0, completed: 0, skipped: {} },
    opt: { attempted: 0, completed: 0, skipped: {} },
  };
}

function recordSkip(stage: StageCount, reason: string): void {
  stage.skipped[reason] = (stage.skipped[reason] ?? 0) + 1;
}

function createProject(): Project {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

/** Removes generated names, binders and line/column numbers so one bug gives one signature.
 *  The parameter `a` is matched only before `.`, so the English article survives. */
export function normalize(message: string): string {
  return message
    .replace(/\b_[A-Za-z0-9_]*\b/g, "_")
    .replace(/\b(f\d+|o|p|n|a_b|box|x)\b|\ba(?=\.)/g, "v")
    .replace(/\d+/g, "N")
    .trim();
}

export function dafnyResolveText(
  dfy: string,
  workDir: string,
  stage: DafnyStage,
  counts?: FuzzCounts,
  timeoutMs = 120_000,
): DafnyResolveResult {
  const file = path.join(workDir, `gen.${stage}.dfy`);
  writeFileSync(file, dfy);
  if (counts) counts.dafnyCalls++;
  const result = spawnSync("dafny", ["resolve", file], { encoding: "utf8", timeout: timeoutMs });
  if (result.error) {
    const code = (result.error as NodeJS.ErrnoException).code;
    if (code === "ETIMEDOUT") {
      return { status: "timeout", detail: `dafny resolve (${stage}) timed out after ${timeoutMs}ms` };
    }
    return { status: "tool-error", detail: `dafny resolve (${stage}) failed to run: ${result.error.message}` };
  }
  if (result.signal) {
    return { status: "timeout", detail: `dafny resolve (${stage}) terminated by signal ${result.signal}` };
  }
  if (result.status === 0) return { status: "ok", detail: null };
  const output = (result.stdout + result.stderr).replaceAll(workDir + path.sep, "");
  const errors = output.split("\n").filter(l => / Error: /.test(l));
  return { status: "error", detail: errors.length > 0 ? errors.join("\n") : output.trim() };
}

/**
 * Compile one TypeScript module through the production CLI pipeline and produce
 * both the pre-optimization Dafny text (emitted before peephole) and the
 * production-optimized Dafny text (`peepholeModule` applied separately to
 * `typesFile` and `defFile`, matching `src/lsc.ts`).
 */
export function compileDafnyVariants(
  text: string,
  project: Project,
  hooks?: EvaluateHooks,
): { ok: true; compiled: CompiledVariants } | { ok: false; failure: Failure } {
  const sourceName = hooks?.sourceName ?? "gen.ts";
  const source = project.createSourceFile(sourceName, text, { overwrite: true });
  const diagnostics = project.getPreEmitDiagnostics().map(d => {
    const m = d.getMessageText();
    return typeof m === "string" ? m : m.getMessageText();
  });
  if (diagnostics.length > 0) {
    return {
      ok: false,
      failure: {
        oracle: "invalid-ts",
        signature: `invalid-ts: ${normalize(diagnostics[0])}`,
        detail: diagnostics.join("\n"),
      },
    };
  }
  try {
    const fileOptions = parseFileOptions(text, sourceName);
    const options = resolveOptions(fileOptions, sourceName);
    const raw = extractModule(source, options);
    const resolved = assertNoLiveAliasMutations(resolveModule(raw));
    const narrowed = narrowModule(resolved);
    const typed = autoHavocModule(narrowed);
    const { typesFile, defFile } = transformModuleDafny(typed);
    // Emit pre-optimization Dafny before running peephole so any mutation inside
    // optimization cannot leak into the pre-optimization representation.
    const preMerged: Module = { ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] };
    const preDfy = emitDafnyFile(preMerged, path.basename(sourceName), options);

    const optPass = hooks?.optimize ?? peepholeModule;
    const optTypes = typesFile ? optPass(typesFile, "dafny") : null;
    const optDef = optPass(defFile, "dafny");
    const optMerged: Module = { ...optDef, decls: [...(optTypes?.decls ?? []), ...optDef.decls] };
    let optDfy = emitDafnyFile(optMerged, path.basename(sourceName), options);
    if (hooks?.postEmitOptimized) optDfy = hooks.postEmitOptimized(optDfy, preDfy, text);

    const userNames = new Set(source.getDescendantsOfKind(SyntaxKind.Identifier).map(i => i.getText()));
    return {
      ok: true,
      compiled: { narrowed, userNames, preDfy, optDfy, optChanged: optDfy !== preDfy, options },
    };
  } catch (e) {
    const message = e instanceof Error ? e.message : String(e);
    return {
      ok: false,
      failure: {
        oracle: "rejected",
        signature: `rejected: ${normalize(message.split("\n")[0])}`,
        detail: message,
      },
    };
  }
}

export function evaluateModule(
  text: string,
  env: { project: Project; workDir: string; counts: FuzzCounts },
  hooks?: EvaluateHooks,
): Outcome {
  const compiledRes = compileDafnyVariants(text, env.project, hooks);
  if (!compiledRes.ok) {
    recordSkip(env.counts.pre, compiledRes.failure.oracle);
    recordSkip(env.counts.opt, compiledRes.failure.oracle);
    return { ok: false, ...compiledRes.failure };
  }

  const { narrowed, userNames, preDfy, optDfy, optChanged } = compiledRes.compiled;
  if (optChanged) env.counts.optChanged++;

  const violations = checkNarrowedModule(narrowed, userNames);
  if (violations.length > 0) {
    recordSkip(env.counts.pre, "checks");
    recordSkip(env.counts.opt, "checks");
    return {
      ok: false,
      oracle: "checks",
      signature: `checks: ${violations[0].check}: ${normalize(violations[0].detail)}`,
      detail: violations.map(v => `${v.fn} [${v.check}] ${v.expr} -- ${v.detail}`).join("\n"),
      preDfy,
      optDfy,
      optChanged,
    };
  }

  const resolveFn = hooks?.resolveDafny ?? ((dfy: string, stage: DafnyStage) =>
    dafnyResolveText(dfy, env.workDir, stage, env.counts, hooks?.timeoutMs));

  env.counts.pre.attempted++;
  const preRes = resolveFn(preDfy, "pre");
  if (preRes.status === "ok" || preRes.status === "error") env.counts.pre.completed++;

  env.counts.opt.attempted++;
  const optRes = resolveFn(optDfy, "opt");
  if (optRes.status === "ok" || optRes.status === "error") env.counts.opt.completed++;

  if (preRes.status === "timeout" || optRes.status === "timeout") {
    const stage: FailureStage =
      preRes.status === "timeout" && optRes.status === "timeout" ? "both"
      : preRes.status === "timeout" ? "pre" : "opt";
    const detail = [preRes.detail, optRes.detail].filter(Boolean).join("\n");
    return {
      ok: false,
      oracle: "timeout",
      stage,
      signature: `timeout (${stage}): ${normalize(detail.split("\n")[0])}`,
      detail,
      preDfy,
      optDfy,
      optChanged,
    };
  }

  if (preRes.status === "tool-error" || optRes.status === "tool-error") {
    const stage: FailureStage =
      preRes.status === "tool-error" && optRes.status === "tool-error" ? "both"
      : preRes.status === "tool-error" ? "pre" : "opt";
    const detail = [preRes.detail, optRes.detail].filter(Boolean).join("\n");
    return {
      ok: false,
      oracle: "tool-error",
      stage,
      signature: `tool-error (${stage}): ${normalize(detail.split("\n")[0])}`,
      detail,
      preDfy,
      optDfy,
      optChanged,
    };
  }

  if (preRes.status === "ok" && optRes.status === "ok") {
    return { ok: true, preDfy, optDfy, optChanged };
  }

  if (preRes.status === "ok" && optRes.status === "error") {
    const first = (optRes.detail ?? "").split("\n")[0].replace(/^.*? Error: /, "");
    return {
      ok: false,
      oracle: "dafny-opt",
      stage: "opt",
      signature: `dafny-opt: ${normalize(first)}`,
      detail: `pre-optimization: ok\noptimized:\n${optRes.detail}`,
      preDfy,
      optDfy,
      optChanged,
    };
  }

  if (preRes.status === "error" && optRes.status === "ok") {
    const first = (preRes.detail ?? "").split("\n")[0].replace(/^.*? Error: /, "");
    return {
      ok: false,
      oracle: "dafny-pre",
      stage: "pre",
      signature: `dafny-pre: ${normalize(first)}`,
      detail: `pre-optimization:\n${preRes.detail}\noptimized: ok`,
      preDfy,
      optDfy,
      optChanged,
    };
  }

  const first = (optRes.detail ?? preRes.detail ?? "").split("\n")[0].replace(/^.*? Error: /, "");
  return {
    ok: false,
    oracle: "dafny-both",
    stage: "both",
    signature: `dafny-both: ${normalize(first)}`,
    detail: `pre-optimization:\n${preRes.detail}\noptimized:\n${optRes.detail}`,
    preDfy,
    optDfy,
    optChanged,
  };
}

/** Full report for one module. A module flagged by the checks is also given to Dafny for both variants. */
export function describeOutcome(
  outcome: Outcome,
  resolveFn?: (dfy: string, stage: DafnyStage) => DafnyResolveResult,
): string {
  if (outcome.ok) {
    return `ok: checks pass and dafny resolve accepts both pre-optimization and optimized Dafny (optChanged=${outcome.optChanged})`;
  }
  let report = `${outcome.signature}\n${outcome.detail}`;
  if (outcome.oracle === "checks" && resolveFn) {
    if (outcome.preDfy !== undefined) {
      const pre = resolveFn(outcome.preDfy, "pre");
      report += `\ndafny resolve (pre): ${pre.status === "ok" ? "accepts" : pre.status + "\n" + pre.detail}`;
    }
    if (outcome.optDfy !== undefined) {
      const opt = resolveFn(outcome.optDfy, "opt");
      report += `\ndafny resolve (opt): ${opt.status === "ok" ? "accepts" : opt.status + "\n" + opt.detail}`;
    }
  }
  return report;
}

export interface CampaignOptions {
  seed: number;
  runs: number;
  classes: number;
  positions: readonly Position[];
  minutes: number;
  out: string;
  hooks?: EvaluateHooks;
}

export interface SavedClass {
  classIndex: number;
  oracle: OracleKind;
  stage: FailureStage | null;
  signature: string;
  optChanged: boolean;
  seed: number;
  path: string;
  positions: readonly Position[];
  replayCommand: string;
  files: { ts: string; preDfy: string | null; optDfy: string | null; meta: string };
}

export interface CampaignSummary {
  seed: number;
  failureClasses: number;
  rejectionClasses: number;
  stop: string;
  elapsedSeconds: number;
  counts: FuzzCounts;
  saved: SavedClass[];
  out: string;
}

function formatSkipped(skipped: Record<string, number>): string {
  const entries = Object.entries(skipped);
  if (entries.length === 0) return "0";
  const total = entries.reduce((acc, [, n]) => acc + n, 0);
  const reasons = entries.sort(([a], [b]) => a.localeCompare(b)).map(([k, n]) => `${k}=${n}`).join(", ");
  return `${total} (${reasons})`;
}

export function runCampaign(opts: CampaignOptions): CampaignSummary {
  mkdirSync(opts.out, { recursive: true });
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-narrowing-fuzz-"));
  const project = createProject();
  const counts = createCounts();
  const cache = new Map<string, Outcome>();

  const run = (text: string): Outcome => {
    let outcome = cache.get(text);
    if (!outcome) {
      counts.modules++;
      outcome = evaluateModule(text, { project, workDir, counts }, opts.hooks);
      cache.set(text, outcome);
    }
    return outcome;
  };

  const resolveForDescribe = opts.hooks?.resolveDafny ?? ((dfy: string, stage: DafnyStage) =>
    dafnyResolveText(dfy, workDir, stage, undefined, opts.hooks?.timeoutMs));

  const arb = moduleArb(opts.positions);
  const started = Date.now();
  const deadline = started + opts.minutes * 60_000;
  const seen = new Set<string>();
  const saved: SavedClass[] = [];
  let rejections = 0;
  let stop = "class limit reached";
  const allPositions = opts.positions.length === POSITIONS.length &&
    opts.positions.every((p, i) => p === POSITIONS[i]);
  const positionsArg = allPositions ? "" : ` --positions ${opts.positions.join(",")}`;

  try {
    for (let round = 0; seen.size < opts.classes; round++) {
      const remaining = deadline - Date.now();
      if (remaining <= 0) { stop = "time limit reached"; break; }
      const roundSeed = opts.seed + round;
      // Lock the failure oracle/stage once the first unseen failure triggers so
      // fast-check shrinking preserves the reported failure stage.
      let lockedOracle: OracleKind | null = null;
      const result = fc.check(fc.property(arb, fns => {
        const outcome = run(renderModule(fns));
        if (outcome.ok || seen.has(outcome.signature)) return true;
        if (lockedOracle === null) {
          lockedOracle = outcome.oracle;
          return false;
        }
        return outcome.oracle !== lockedOracle;
      }), { seed: roundSeed, numRuns: opts.runs, interruptAfterTimeLimit: remaining, markInterruptAsFailure: false });
      if (!result.failed || !result.counterexample) {
        stop = result.interrupted ? "time limit reached" : `round with seed ${roundSeed} found no new class in ${opts.runs} runs`;
        break;
      }
      const text = renderModule(result.counterexample[0]);
      const outcome = run(text);
      if (outcome.ok) continue;
      seen.add(outcome.signature);
      // A rejection may be correct subset behaviour, so it is reported apart from oracle failures.
      const rejection = outcome.oracle === "rejected";
      if (rejection) rejections++;
      const n = seen.size;
      const tsPath = path.join(opts.out, `${n}.ts`);
      const prePath = outcome.preDfy !== undefined ? path.join(opts.out, `${n}.pre.dfy`) : null;
      const optPath = outcome.optDfy !== undefined ? path.join(opts.out, `${n}.opt.dfy`) : null;
      const metaPath = path.join(opts.out, `${n}.meta.json`);
      writeFileSync(tsPath, text);
      if (prePath && outcome.preDfy !== undefined) writeFileSync(prePath, outcome.preDfy);
      if (optPath && outcome.optDfy !== undefined) writeFileSync(optPath, outcome.optDfy);
      const replayCommand = `npm run fuzz:narrowing -- --seed ${roundSeed}${positionsArg} --path ${result.counterexamplePath}`;
      const record: SavedClass = {
        classIndex: n,
        oracle: outcome.oracle,
        stage: outcome.stage ?? null,
        signature: outcome.signature,
        optChanged: outcome.optChanged ?? false,
        seed: roundSeed,
        path: result.counterexamplePath ?? "",
        positions: opts.positions,
        replayCommand,
        files: {
          ts: path.basename(tsPath),
          preDfy: prePath ? path.basename(prePath) : null,
          optDfy: optPath ? path.basename(optPath) : null,
          meta: path.basename(metaPath),
        },
      };
      writeFileSync(metaPath, JSON.stringify(record, null, 2) + "\n");
      saved.push(record);
      console.log(`── class ${n}${rejection ? " (rejection)" : ""}: replay with --seed ${roundSeed}${positionsArg} --path ${result.counterexamplePath} ──\n${text}\n${describeOutcome(outcome, resolveForDescribe)}\n`);
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }

  const elapsedSeconds = Number(((Date.now() - started) / 1000).toFixed(1));
  console.log(`${seen.size - rejections} failure classes, ${rejections} rejection classes; seed ${opts.seed}; stopped: ${stop}`);
  console.log(
    `${counts.modules} distinct modules compiled (${counts.optChanged} changed by peephole), ` +
    `pre: ${counts.pre.attempted} attempted / ${counts.pre.completed} completed / skipped ${formatSkipped(counts.pre.skipped)}, ` +
    `opt: ${counts.opt.attempted} attempted / ${counts.opt.completed} completed / skipped ${formatSkipped(counts.opt.skipped)}, ` +
    `${counts.dafnyCalls} dafny calls, ${elapsedSeconds.toFixed(1)}s`,
  );
  console.log(`counterexamples saved to ${opts.out}`);
  return {
    seed: opts.seed,
    failureClasses: seen.size - rejections,
    rejectionClasses: rejections,
    stop,
    elapsedSeconds,
    counts,
    saved,
    out: opts.out,
  };
}

import {
  replaySavedSemanticCase,
  replaySemanticSeedPath,
  runSemanticCampaign,
} from "./semantic-oracle.js";
import {
  IMPERATIVE_FAMILIES,
  IMPERATIVE_SCHEMA,
  replaySavedImperativeCase,
  runImperativeCampaign,
  type ImperativeFamily,
} from "./imperative-oracle.js";

// ── Driver ──────────────────────────────────────────────────

function main(): number {
  const { values: args } = parseArgs({
    options: {
      seed: { type: "string", default: "1" },
      runs: { type: "string" },
      classes: { type: "string", default: "12" },
      positions: { type: "string", default: POSITIONS.join(",") },
      families: { type: "string", default: IMPERATIVE_FAMILIES.join(",") },
      minutes: { type: "string" },
      out: { type: "string" },
      path: { type: "string" },
      file: { type: "string" },
      semantic: { type: "boolean", default: false },
      imperative: { type: "boolean", default: false },
      "fast-run": { type: "boolean", default: false },
      "inputs-per-fn": { type: "string", default: "3" },
      "verify-timeout": { type: "string", default: "15" },
      case: { type: "string" },
      help: { type: "boolean", default: false },
    },
  });

  if (args.help) {
    console.log(readFileSync(new URL(import.meta.url), "utf8").split("*/")[0].replace(/^\/\*\*\n/, "").replace(/^ \* ?/gm, ""));
    return 0;
  }

  if (args.case) {
    const raw = JSON.parse(readFileSync(args.case, "utf8")) as { schema?: string };
    if (raw.schema === IMPERATIVE_SCHEMA) {
      const outcome = replaySavedImperativeCase(args.case, { timeoutSec: Number(args["verify-timeout"]) });
      if (outcome.ok) {
        console.log(`saved imperative semantic replay passed (${outcome.checks.length} checks verified)`);
        return 0;
      }
      console.log(`${outcome.signature}\n${outcome.detail}`);
      return 1;
    }
    const outcome = replaySavedSemanticCase(args.case);
    if (outcome.ok) {
      console.log(`saved semantic replay passed (${outcome.checks.length} checks verified on both pre and opt)`);
      return 0;
    }
    console.log(`${outcome.signature}\n${outcome.detail}`);
    return 1;
  }

  if (args.imperative) {
    const seed = Number(args.seed);
    const numRuns = Number(args.runs ?? "30");
    const timeoutSec = Number(args["verify-timeout"]);
    const families = args.families.split(",").map(s => s.trim()) as ImperativeFamily[];
    const badFam = families.filter(f => !IMPERATIVE_FAMILIES.includes(f));
    if (badFam.length > 0) {
      console.error(`unknown families: ${badFam.join(", ")}; choose from ${IMPERATIVE_FAMILIES.join(", ")}`);
      return 2;
    }
    const out = args.out ?? path.join(tmpdir(), `lsc-narrowing-imperative-seed${seed}`);
    const summary = runImperativeCampaign({
      seed,
      runs: numRuns,
      families,
      out,
      timeoutSec,
      fastRun: args["fast-run"],
    });
    console.log(JSON.stringify(summary, null, 2));
    const critical = summary.counts.soundnessRefuted + summary.counts.preconditionDropped;
    const otherFailures = summary.counts.semanticMismatch + summary.counts.dafnyResolve + summary.counts.invalidTs + summary.counts.timeout + summary.counts.toolError;
    return critical > 0 || otherFailures > 0 ? 1 : 0;
  }

  if (args.file) {
    const workDir = mkdtempSync(path.join(tmpdir(), "lsc-narrowing-fuzz-file-"));
    try {
      const project = createProject();
      const counts = createCounts();
      const text = readFileSync(args.file, "utf8");
      const outcome = evaluateModule(text, { project, workDir, counts }, { sourceName: path.basename(args.file) });
      const resolveForDescribe = (dfy: string, stage: DafnyStage) => dafnyResolveText(dfy, workDir, stage);
      console.log(describeOutcome(outcome, resolveForDescribe));
      return outcome.ok ? 0 : 1;
    } finally {
      rmSync(workDir, { recursive: true, force: true });
    }
  }

  const seed = Number(args.seed);
  const numRuns = Number(args.runs ?? (args.semantic ? "20" : "150"));
  const minutes = Number(args.minutes ?? (args.semantic ? "8" : "9"));
  const inputsPerFn = Number(args["inputs-per-fn"]);
  const verifyTimeLimitSec = Number(args["verify-timeout"]);
  const positions = args.positions.split(",").map(p => p.trim()) as Position[];
  const unknown = positions.filter(p => !POSITIONS.includes(p));
  if (unknown.length > 0) {
    console.error(`unknown positions: ${unknown.join(", ")}; choose from ${POSITIONS.join(", ")}`);
    return 2;
  }

  if (args.semantic) {
    if (args.path) {
      const replayed = replaySemanticSeedPath({ seed, path: args.path, runs: numRuns, inputsPerFn, positions });
      if (replayed.passed) {
        console.log("semantic replay passed");
        return 0;
      }
      console.log(`${replayed.outcome?.source ?? ""}\n${replayed.outcome?.signature}\n${replayed.outcome?.detail}`);
      return 1;
    }
    const out = args.out ?? path.join(tmpdir(), `lsc-narrowing-semantic-seed${seed}`);
    const summary = runSemanticCampaign({
      seed,
      runs: numRuns,
      classes: Number(args.classes),
      inputsPerFn,
      positions,
      minutes,
      out,
      verifyTimeLimitSec,
    });
    return summary.failureClasses === 0 ? 0 : 1;
  }

  if (args.path) {
    const workDir = mkdtempSync(path.join(tmpdir(), "lsc-narrowing-fuzz-replay-"));
    try {
      const project = createProject();
      const counts = createCounts();
      const arb = moduleArb(positions);
      const run = (text: string) => evaluateModule(text, { project, workDir, counts });
      const resolveForDescribe = (dfy: string, stage: DafnyStage) => dafnyResolveText(dfy, workDir, stage);
      // `endOnFailure` stops at the module the path names. Without it, fast-check
      // would keep shrinking under this weaker property and could reach a class
      // that an earlier round had already reported.
      const result = fc.check(fc.property(arb, fns => run(renderModule(fns)).ok),
        { seed, path: args.path, numRuns, endOnFailure: true });
      if (!result.failed || !result.counterexample) {
        console.log("replay passed");
        return 0;
      }
      const text = renderModule(result.counterexample[0]);
      console.log(`${text}\n${describeOutcome(run(text), resolveForDescribe)}`);
      return 1;
    } finally {
      rmSync(workDir, { recursive: true, force: true });
    }
  }

  const out = args.out ?? path.join(tmpdir(), `lsc-narrowing-fuzz-seed${seed}`);
  const summary = runCampaign({
    seed,
    runs: numRuns,
    classes: Number(args.classes),
    positions,
    minutes,
    out,
  });
  return summary.failureClasses === 0 ? 0 : 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  process.exitCode = main();
}
