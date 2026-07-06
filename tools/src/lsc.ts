#!/usr/bin/env node
/**
 * lsc — LemmaScript compiler CLI
 *
 * Pipeline: extract → resolve → narrow → transform → peephole → emit
 */

import { Project, ScriptTarget } from "ts-morph";
import { existsSync } from "fs";
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

  // `lsc claimcheck …` forwards verbatim to the lemmascript-claimcheck CLI
  // (a dependency; its cli reads the rewritten process.argv).
  if (args[0] === "claimcheck") {
    process.argv = [process.argv[0], "lemmascript-claimcheck", ...args.slice(1)];
    import("lemmascript-claimcheck/cli").catch((err: unknown) => {
      const code = (err as { code?: string })?.code;
      if (code === "ERR_MODULE_NOT_FOUND" || code === "ERR_PACKAGE_PATH_NOT_EXPORTED") {
        console.error("`lsc claimcheck` needs lemmascript-claimcheck >= 0.2.0; reinstall with: npm i -g lemmascript");
      } else {
        console.error(err instanceof Error ? err.message : String(err));
      }
      process.exit(1);
    });
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
    timeLimit = parseInt(args[timeLimitIdx].split("=")[1]);
    args.splice(timeLimitIdx, 1);
  }

  const extraFlagsIdx = args.findIndex(a => a.startsWith("--extra-flags="));
  let extraFlags: string | undefined;
  if (extraFlagsIdx >= 0) {
    extraFlags = args[extraFlagsIdx].split("=").slice(1).join("=");
    args.splice(extraFlagsIdx, 1);
  }

  const [cmd, filePath] = args;
  if (!cmd || !filePath) {
    console.error("Usage: lsc <gen|check|regen|extract|info> [--backend=lean|dafny] <file.ts>");
    console.error("       lsc claimcheck <file.ts> [flags…]   (forwards to lemmascript-claimcheck)");
    process.exit(1);
  }

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
    if (cmd === "regen") { dafnyRegen(genPath, dfyPath, basePath, text, dir); return; }
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
