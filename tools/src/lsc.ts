#!/usr/bin/env node
/**
 * lsc — LemmaScript compiler CLI
 *
 * Pipeline: extract → resolve → transform → emit
 */

import { Project, ScriptTarget } from "ts-morph";
import { existsSync } from "fs";
import path from "path";
import { extractModule } from "./extract.js";
import { resolveModule } from "./resolve.js";
import { peModule } from "./pe.js";
import { transformModuleLean, transformModuleDafny } from "./transform.js";
import { peepholeModule } from "./peephole.js";
import { emitLeanFile } from "./lean-emit.js";
import { emitDafnyFile } from "./dafny-emit.js";
import { dafnyGen, dafnyCheckDiff, dafnyVerify, dafnyRegen } from "./dafny-commands.js";
import { leanGen, leanCheck } from "./lean-commands.js";

function main() {
  const args = process.argv.slice(2);
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
    console.error("Usage: lsc <gen|check|regen|extract> [--backend=lean|dafny] <file.ts>");
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

  // Check //@ backend directive — skip if backend doesn't match
  const backendDirective = sourceFile.getFullText().match(/\/\/@ backend (\w+)/);
  if (backendDirective && backendDirective[1] !== backend) {
    console.log(`Skipped: ${path.basename(filePath)} (//@ backend ${backendDirective[1]}, current: ${backend})`);
    return;
  }

  // Extract: ts-morph → Raw IR
  const raw = extractModule(sourceFile);

  if (cmd === "extract") {
    console.log(JSON.stringify(raw, null, 2));
    return;
  }

  // Resolve: Raw IR → Typed IR
  const resolved = resolveModule(raw);
  // PE: Typed IR → Typed IR (narrowing emulation; currently no-op)
  const typed = peModule(resolved);

  const dir = path.dirname(absPath);
  const base = path.basename(filePath, ".ts");

  // ── Dafny backend ─────────────────────────────────────────
  if (backend === "dafny") {
    let { typesFile, defFile } = transformModuleDafny(typed);
    if (typesFile) typesFile = peepholeModule(typesFile, "dafny");
    defFile = peepholeModule(defFile, "dafny");
    const allDecls = [...(typesFile?.decls ?? []), ...defFile.decls];
    const merged = { ...defFile, decls: allDecls };
    const text = emitDafnyFile(merged, path.basename(filePath));
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
  const specPath = path.join(dir, `${base}.spec.lean`);
  const specImport = existsSync(specPath) ? `«${base}.spec»` : undefined;
  let { typesFile, defFile } = transformModuleLean(typed, specImport);
  if (typesFile) typesFile = peepholeModule(typesFile, "lean");
  defFile = peepholeModule(defFile, "lean");

  const typesPath = typesFile ? path.join(dir, `${base}.types.lean`) : null;
  const typesText = typesFile ? emitLeanFile(typesFile) : null;
  const defPath = path.join(dir, `${base}.def.lean`);
  const defText = emitLeanFile(defFile);

  if (cmd === "gen") { leanGen(typesPath, defPath, typesText, defText); return; }
  if (cmd === "check") {
    leanGen(typesPath, defPath, typesText, defText);
    if (!leanCheck(dir, base)) process.exit(1);
    return;
  }
  console.error(`Unknown command: ${cmd}`);
  process.exit(1);
}

main();
