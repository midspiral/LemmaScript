#!/usr/bin/env -S npx tsx
/**
 * lsc — LemmaScript compiler CLI
 *
 * Pipeline: extract → resolve → transform → emit
 */

import { Project } from "ts-morph";
import { existsSync, readFileSync, writeFileSync, copyFileSync } from "fs";
import { execSync } from "child_process";
import path from "path";
import { extractModule } from "./extract.js";
import { resolveModule } from "./resolve.js";
import { transformModule } from "./transform.js";
import { emitFile } from "./emit.js";
import { transformDafnyModule } from "./dafny-transform.js";
import { emitDafnyFile } from "./dafny-emit.js";

// ── Dafny helpers ───────────────────────────────────────────

function dafnyGen(genPath: string, dfyPath: string, text: string) {
  writeFileSync(genPath, text);
  console.log(`Generated: ${genPath}`);
  if (!existsSync(dfyPath)) {
    writeFileSync(dfyPath, text);
    console.log(`Created: ${dfyPath}`);
  }
}

function dafnyCheckDiff(genPath: string, dfyPath: string): boolean {
  if (!existsSync(dfyPath)) return true;
  try {
    const diff = execSync(`git diff --no-index -- "${genPath}" "${dfyPath}" 2>/dev/null || true`, { encoding: "utf-8" });
    const deletions = diff.split("\n").filter(l => l.startsWith("-") && !l.startsWith("---"));
    if (deletions.length > 0) {
      console.error(`WARNING: ${path.basename(dfyPath)} has modifications to generated lines (not additions-only):`);
      for (const d of deletions.slice(0, 5)) console.error("  " + d);
      return false;
    }
  } catch { /* diff not available */ }
  return true;
}

function dafnyVerify(dfyPath: string, dir: string): boolean {
  console.log("Running dafny verify...");
  try {
    execSync(`dafny verify "${dfyPath}"`, { cwd: dir, stdio: "inherit" });
    return true;
  } catch {
    return false;
  }
}

function dafnySavePatch(genPath: string, dfyPath: string, patchPath: string) {
  try {
    const patch = execSync(`diff -u "${genPath}" "${dfyPath}" || true`, { encoding: "utf-8" });
    writeFileSync(patchPath, patch);
    console.log(`Saved: ${patchPath}`);
  } catch { /* diff not available */ }
}

function dafnyApplyPatch(genPath: string, dfyPath: string, patchPath: string): boolean {
  if (!existsSync(patchPath)) return false;
  const patch = readFileSync(patchPath, "utf-8").trim();
  if (!patch) return false;
  // Copy gen to dfy, then apply patch
  copyFileSync(genPath, dfyPath);
  try {
    execSync(`patch --no-backup-if-mismatch -p0 "${dfyPath}" < "${patchPath}"`, { stdio: "pipe" });
    console.log(`Applied: ${patchPath}`);
    return true;
  } catch {
    // Patch failed to apply cleanly — restore from gen
    copyFileSync(genPath, dfyPath);
    return false;
  }
}

function dafnyRegen(genPath: string, dfyPath: string, patchPath: string, text: string, dir: string) {
  // 1. No .dfy yet — generate both, done
  if (!existsSync(dfyPath)) {
    writeFileSync(genPath, text);
    console.log(`Generated: ${genPath}`);
    writeFileSync(dfyPath, text);
    console.log(`Created: ${dfyPath}`);
    dafnyVerify(dfyPath, dir);
    return;
  }

  // 2. Capture patch from current .dfy.gen → .dfy BEFORE overwriting .dfy.gen
  let hasPatch = false;
  if (existsSync(genPath)) {
    dafnySavePatch(genPath, dfyPath, patchPath);
    const patch = readFileSync(patchPath, "utf-8").trim();
    hasPatch = patch.length > 0;
  }

  // 3. Generate new .dfy.gen
  writeFileSync(genPath, text);
  console.log(`Generated: ${genPath}`);

  // 4. Try verifying existing .dfy as-is
  if (dafnyVerify(dfyPath, dir)) {
    return;
  }

  // 5. Verification failed — try applying patch to new .dfy.gen
  if (hasPatch) {
    console.log("Verification failed. Trying to apply patch...");
    if (dafnyApplyPatch(genPath, dfyPath, patchPath)) {
      if (dafnyVerify(dfyPath, dir)) {
        return;
      }
    }
  }

  // 6. Patch failed or didn't verify — needs LLM re-adaptation
  console.error(`FAILED: ${path.basename(dfyPath)} needs manual re-adaptation.`);
  console.error(`  ${genPath} has the new generated code.`);
  if (hasPatch) console.error(`  ${patchPath} has the captured patch.`);
  process.exit(1);
}

// ── Main ────────────────────────────────────────────────────

function main() {
  const args = process.argv.slice(2);
  const backendIdx = args.indexOf("--backend=dafny");
  const backend = backendIdx >= 0 ? "dafny" : "lean";
  if (backendIdx >= 0) args.splice(backendIdx, 1);

  const [cmd, filePath] = args;
  if (!cmd || !filePath) {
    console.error("Usage: lsc <gen|check|regen|extract> [--backend=dafny] <file.ts>");
    process.exit(1);
  }

  const absPath = path.resolve(filePath);
  if (!existsSync(absPath)) {
    console.error(`File not found: ${absPath}`);
    process.exit(1);
  }

  const project = new Project({ compilerOptions: { strict: true } });
  const sourceFile = project.addSourceFileAtPath(absPath);

  // Extract: ts-morph → Raw IR
  const raw = extractModule(sourceFile);

  if (cmd === "extract") {
    console.log(JSON.stringify(raw, null, 2));
    return;
  }

  // Resolve: Raw IR → Typed IR
  const typed = resolveModule(raw);

  const dir = path.dirname(absPath);
  const base = path.basename(filePath, ".ts");

  // ── Dafny backend ─────────────────────────────────────────
  if (backend === "dafny") {
    const dafnyFile = transformDafnyModule(typed);
    const text = emitDafnyFile(dafnyFile);
    const genPath = path.join(dir, `${base}.dfy.gen`);
    const dfyPath = path.join(dir, `${base}.dfy`);
    const patchPath = path.join(dir, `${base}.dfy.patch`);

    if (cmd === "gen") {
      dafnyGen(genPath, dfyPath, text);
      return;
    }

    if (cmd === "check") {
      dafnyGen(genPath, dfyPath, text);
      dafnyCheckDiff(genPath, dfyPath);
      dafnyVerify(dfyPath, dir);
      return;
    }

    if (cmd === "regen") {
      dafnyRegen(genPath, dfyPath, patchPath, text, dir);
      return;
    }

    console.error(`Unknown command: ${cmd}`);
    process.exit(1);
  }

  // ── Lean backend ──────────────────────────────────────────
  const specPath = path.join(dir, `${base}.spec.lean`);
  const specImport = existsSync(specPath) ? `«${base}.spec»` : undefined;

  // Transform: Typed IR → Lean IR
  const { typesFile, defFile } = transformModule(typed, specImport);

  // Emit: Lean IR → text
  if (typesFile) {
    const typesPath = path.join(dir, `${base}.types.lean`);
    writeFileSync(typesPath, emitFile(typesFile));
    console.log(`Generated: ${typesPath}`);
  }

  const defPath = path.join(dir, `${base}.def.lean`);

  if (cmd === "gen") {
    writeFileSync(defPath, emitFile(defFile));
    console.log(`Generated: ${defPath}`);
    return;
  }

  if (cmd === "check") {
    writeFileSync(defPath, emitFile(defFile));
    console.log(`Generated: ${defPath}`);

    let lakeDir = dir;
    while (lakeDir !== path.dirname(lakeDir)) {
      if (existsSync(path.join(lakeDir, "lakefile.lean"))) break;
      lakeDir = path.dirname(lakeDir);
    }

    const proofPath = path.join(dir, `${base}.proof.lean`);
    if (!existsSync(proofPath)) {
      console.error(`No proof file: ${proofPath}`);
      process.exit(1);
    }

    console.log("Running lake build...");
    try {
      execSync(`lake build`, { cwd: lakeDir, stdio: "inherit" });
    } catch {
      process.exit(1);
    }
    return;
  }

  console.error(`Unknown command: ${cmd}`);
  process.exit(1);
}

main();
