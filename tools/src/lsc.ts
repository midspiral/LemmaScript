#!/usr/bin/env node
/**
 * lsc — LemmaScript compiler CLI
 *
 * Pipeline: extract → resolve → narrow → transform → peephole → emit
 */

import { Project, ScriptTarget } from "ts-morph";
import { existsSync, readFileSync } from "fs";
import { execFileSync } from "child_process";
import { createRequire } from "module";
import path from "path";
import { extractModule } from "./extract.js";
import { resolveModule } from "./resolve.js";
import { narrowModule } from "./narrow.js";
import { autoHavocModule } from "./autohavoc.js";
import { transformModuleLean, transformModuleDafny } from "./transform.js";
import { peepholeModule } from "./peephole.js";
import { emitLeanFile } from "./lean-emit.js";
import { emitDafnyFile } from "./dafny-emit.js";
import { dafnyGen, dafnyCheckDiff, dafnyVerify, dafnyRegen } from "./dafny-commands.js";
import { leanGen, leanCheck } from "./lean-commands.js";
import { runInfo } from "./info-command.js";

function main() {
  const args = process.argv.slice(2);

  // `lsc claimcheck <file.ts> …` forwards verbatim to the lemmascript-claimcheck
  // CLI (a dependency; its cli reads the rewritten process.argv). With no
  // leading <file.ts>, batch: one satellite run per LemmaScript-files.txt entry,
  // flags passed through unchanged — the loop is owned here, the satellite
  // stays single-file.
  if (args[0] === "claimcheck") {
    const rest = args.slice(1);
    const missing = () => {
      console.error("`lsc claimcheck` needs lemmascript-claimcheck >= 0.2.0; reinstall with: npm i -g lemmascript");
      process.exit(1);
    };
    if (rest[0] && !rest[0].startsWith("-")) {
      process.argv = [process.argv[0], "lemmascript-claimcheck", ...rest];
      import("lemmascript-claimcheck/cli").catch((err: unknown) => {
        const code = (err as { code?: string })?.code;
        if (code === "ERR_MODULE_NOT_FOUND" || code === "ERR_PACKAGE_PATH_NOT_EXPORTED") missing();
        console.error(err instanceof Error ? err.message : String(err));
        process.exit(1);
      });
      return;
    }
    let cli: string;
    try {
      cli = createRequire(import.meta.url).resolve("lemmascript-claimcheck/cli");
    } catch {
      missing();
      return;
    }
    for (const e of readEntries()) {
      try {
        execFileSync(process.execPath, [cli, e.file, ...rest], { stdio: "inherit" });
      } catch {
        process.exit(1);
      }
    }
    return;
  }

  const backendIdx = args.findIndex(a => a.startsWith("--backend="));
  let backend: "lean" | "dafny" = "dafny";
  if (backendIdx >= 0) {
    const val = args[backendIdx].split("=")[1];
    if (val !== "lean" && val !== "dafny") {
      console.error(`Unknown backend: ${val}. Use --backend=lean or --backend=dafny`);
      process.exit(1);
    }
    backend = val;
    args.splice(backendIdx, 1);
  }

  const timeLimitIdx = args.findIndex(a => a.startsWith("--time-limit="));
  let timeLimit: number | undefined;
  if (timeLimitIdx >= 0) {
    const val = args[timeLimitIdx].split("=")[1];
    if (!/^[1-9]\d*$/.test(val)) {
      console.error(`Invalid --time-limit: ${val} (expected seconds as a positive integer)`);
      process.exit(1);
    }
    timeLimit = parseInt(val);
    args.splice(timeLimitIdx, 1);
  }

  const extraFlagsIdx = args.findIndex(a => a.startsWith("--extra-flags="));
  let extraFlags: string | undefined;
  if (extraFlagsIdx >= 0) {
    extraFlags = args[extraFlagsIdx].split("=").slice(1).join("=");
    args.splice(extraFlagsIdx, 1);
  }

  // --slow (batch mode only): verify every entry with its own timeout instead
  // of degrading slow ones to gen-check.
  let slow = false;
  const slowIdx = args.indexOf("--slow");
  if (slowIdx >= 0) {
    slow = true;
    args.splice(slowIdx, 1);
  }

  // Anything flag-shaped left over is a typo or a space-separated form
  // (`--backend lean`): reject it rather than let it become a positional arg
  // or be silently ignored (which would e.g. verify with the wrong backend).
  const stray = args.find(a => a.startsWith("-"));
  if (stray) {
    console.error(`Unknown flag: ${stray} (flags take the form --flag=value, e.g. --backend=dafny)`);
    process.exit(1);
  }

  const [cmd, filePath] = args;
  if (!cmd) {
    console.error("Usage: lsc <gen|check|regen|extract|info> [--backend=lean|dafny] <file.ts>");
    console.error("       lsc <gen|gen-check|check> [--backend=…] [--slow]   (no file: batch over LemmaScript-files.txt)");
    console.error("       lsc claimcheck [<file.ts>] [flags…]   (forwards to lemmascript-claimcheck)");
    process.exit(1);
  }
  if (!filePath) {
    runBatch(cmd, backend, slow);
    return;
  }
  runFile(cmd, filePath, backend, timeLimit, extraFlags);
}

// LemmaScript-files.txt, parsed: `filepath [timeout_in_seconds] [extra dafny
// flags…]` per line; no timeout = Dafny default. Exits if the file is absent.
function readEntries(): { file: string; timeout?: number; flags?: string }[] {
  if (!existsSync("LemmaScript-files.txt")) {
    console.error("No file given and no LemmaScript-files.txt found.");
    process.exit(1);
  }
  return readFileSync("LemmaScript-files.txt", "utf8")
    .split("\n").map(s => s.trim()).filter(Boolean)
    .map(entry => {
      const [file, second, ...rest] = entry.split(/\s+/);
      const timeout = second && /^[1-9]\d*$/.test(second) ? parseInt(second) : undefined;
      const flags = (timeout === undefined ? [second, ...rest] : rest).filter(Boolean).join(" ") || undefined;
      return { file, timeout, flags };
    });
}

// Batch over LemmaScript-files.txt. `check` entries with a timeout above 60s
// (the CI limit) are gen-check only, unless --slow. Fail-fast: the first
// failing entry exits. tools/check.sh drives this from source;
// installed-package consumers run `lsc check`.
function runBatch(cmd: string, backend: "lean" | "dafny", slow: boolean) {
  if (cmd !== "gen" && cmd !== "gen-check" && cmd !== "check") {
    console.error(`No file given, and batch mode supports gen|gen-check|check (not ${cmd}).`);
    process.exit(1);
  }
  for (const e of readEntries()) {
    if (cmd === "check" && backend === "dafny" && !slow && e.timeout !== undefined && e.timeout > 60) {
      console.log(`=== ${path.basename(e.file)} (timeout ${e.timeout}s > 60s, gen-check only) ===`);
      runFile("gen-check", e.file, backend, undefined, undefined);
    } else {
      runFile(cmd, e.file, backend, e.timeout, e.flags);
    }
  }
}

function runFile(cmd: string, filePath: string, backend: "lean" | "dafny", timeLimit: number | undefined, extraFlags: string | undefined) {
  const absPath = path.resolve(filePath);
  if (!existsSync(absPath)) {
    console.error(`File not found: ${absPath}`);
    process.exit(1);
  }

  // Find nearest tsconfig.json for import resolution; fall back to bare options
  function findTsConfig(from: string): string | undefined {
    let dir = path.dirname(from);
    while (true) {
      const candidate = path.join(dir, "tsconfig.json");
      if (existsSync(candidate)) return candidate;
      const parent = path.dirname(dir);
      if (parent === dir) return undefined;
      dir = parent;
    }
  }
  const tsConfigFilePath = findTsConfig(absPath);
  const project = tsConfigFilePath
    ? new Project({ tsConfigFilePath })
    : new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"] } });
  const sourceFile = project.addSourceFileAtPath(absPath);
  project.resolveSourceFileDependencies();

  const fullText = sourceFile.getFullText();

  // Check //@ backend directive — skip if backend doesn't match.
  // `extract` and `info` are backend-neutral and always run.
  const backendDirective = fullText.match(/\/\/@ backend (\w+)/);
  if (cmd !== "extract" && cmd !== "info" && backendDirective && backendDirective[1] !== backend) {
    console.log(`Skipped: ${path.basename(filePath)} (//@ backend ${backendDirective[1]}, current: ${backend})`);
    return;
  }

  // File-level directives consumed by the Dafny emitter.
  const safeSlice = /\/\/@ safe-slice\b/.test(fullText);

  // `//@ lean-module <name>` overrides the Lean module base (default: file
  // basename). Lean module names are flat/global, so two identically-named
  // `.ts` files (e.g. an in-place fork's duplicated `compaction.ts`) would emit
  // colliding `foo.types`/`foo.def` modules; this gives one a distinct base so
  // both can be separate Lean libraries. Lean-only — Dafny is unaffected.
  const leanModuleDirective = fullText.match(/\/\/@ lean-module ([A-Za-z0-9_.\-]+)/);
  const leanModuleOverride = leanModuleDirective ? leanModuleDirective[1] : undefined;

  // Extract: ts-morph → Raw IR
  const raw = extractModule(sourceFile);

  if (cmd === "extract") {
    console.log(JSON.stringify(raw, null, 2));
    return;
  }

  if (cmd === "info") {
    const outPath = path.join(path.dirname(absPath), `${path.basename(filePath, ".ts")}.ts.json`);
    runInfo(raw, outPath);
    return;
  }

  // Resolve: Raw IR → Typed IR
  const resolved = resolveModule(raw);
  // Narrow: Typed IR → Typed IR (rewrites optional-narrowing patterns to someMatch)
  // auto-havoc (//@ autohavoc): replace unmodellable expressions with arbitrary
  // values so verification rests only on the declared contracts (a sound
  // over-approximation). No-op unless a function opts in.
  const typed = autoHavocModule(narrowModule(resolved));

  const dir = path.dirname(absPath);
  const base = path.basename(filePath, ".ts");

  // ── Dafny backend ─────────────────────────────────────────
  if (backend === "dafny") {
    let { typesFile, defFile } = transformModuleDafny(typed);
    if (typesFile) typesFile = peepholeModule(typesFile, "dafny");
    defFile = peepholeModule(defFile, "dafny");
    const allDecls = [...(typesFile?.decls ?? []), ...defFile.decls];
    const merged = { ...defFile, decls: allDecls };
    const text = emitDafnyFile(merged, path.basename(filePath), { safeSlice });
    const genPath = path.join(dir, `${base}.dfy.gen`);
    const dfyPath = path.join(dir, `${base}.dfy`);
    const basePath = path.join(dir, `${base}.dfy.base`);

    if (cmd === "gen") { dafnyGen(genPath, dfyPath, text); return; }
    if (cmd === "gen-check") {
      dafnyGen(genPath, dfyPath, text);
      if (!dafnyCheckDiff(genPath, dfyPath)) process.exit(1);
      return;
    }
    if (cmd === "check") {
      dafnyGen(genPath, dfyPath, text);
      if (!dafnyCheckDiff(genPath, dfyPath)) process.exit(1);
      if (!dafnyVerify(dfyPath, dir, timeLimit, extraFlags)) process.exit(1);
      return;
    }
    if (cmd === "regen") { dafnyRegen(genPath, dfyPath, basePath, text, dir, timeLimit, extraFlags); return; }
    console.error(`Unknown command: ${cmd}`);
    process.exit(1);
  }

  // ── Lean backend ──────────────────────────────────────────
  const leanBase = leanModuleOverride ?? base;
  const specPath = path.join(dir, `${leanBase}.spec.lean`);
  const specImport = existsSync(specPath) ? `«${leanBase}.spec»` : undefined;
  let { typesFile, defFile } = transformModuleLean(typed, specImport, leanModuleOverride);
  if (typesFile) typesFile = peepholeModule(typesFile, "lean");
  defFile = peepholeModule(defFile, "lean");

  const typesPath = typesFile ? path.join(dir, `${leanBase}.types.lean`) : null;
  const typesText = typesFile ? emitLeanFile(typesFile) : null;
  const defPath = path.join(dir, `${leanBase}.def.lean`);
  const defText = emitLeanFile(defFile);

  if (cmd === "gen") { leanGen(typesPath, defPath, typesText, defText); return; }
  if (cmd === "check") {
    leanGen(typesPath, defPath, typesText, defText);
    if (!leanCheck(dir, leanBase)) process.exit(1);
    return;
  }
  console.error(`Unknown command: ${cmd}`);
  process.exit(1);
}

main();
