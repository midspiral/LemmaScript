/**
 * Dafny backend commands: gen, check, regen.
 */

import { existsSync, readFileSync, writeFileSync, copyFileSync } from "fs";
import { execSync } from "child_process";
import path from "path";

function writeGen(genPath: string, text: string) {
  writeFileSync(genPath, text);
  console.log(`Generated: ${genPath}`);
}

export function dafnyGen(genPath: string, dfyPath: string, text: string) {
  writeGen(genPath, text);
  if (!existsSync(dfyPath)) {
    writeFileSync(dfyPath, text);
    console.log(`Created: ${dfyPath}`);
  }
}

export function dafnyCheckDiff(genPath: string, dfyPath: string): boolean {
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

export function dafnyVerify(dfyPath: string, dir: string): boolean {
  console.log("Running dafny verify...");
  try {
    execSync(`dafny verify "${dfyPath}"`, { cwd: dir, stdio: "inherit" });
    return true;
  } catch {
    return false;
  }
}

export function dafnySavePatch(genPath: string, dfyPath: string, patchPath: string) {
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
  copyFileSync(genPath, dfyPath);
  try {
    execSync(`patch --no-backup-if-mismatch -p0 "${dfyPath}" < "${patchPath}"`, { stdio: "pipe" });
    console.log(`Applied: ${patchPath}`);
    return true;
  } catch {
    copyFileSync(genPath, dfyPath);
    return false;
  }
}

export function dafnyRegen(genPath: string, dfyPath: string, patchPath: string, text: string, dir: string) {
  // 1. No .dfy yet — create both, verify, done
  if (!existsSync(dfyPath)) {
    dafnyGen(genPath, dfyPath, text);
    dafnyVerify(dfyPath, dir);
    return;
  }

  // 2. Capture patch from current gen → dfy BEFORE overwriting gen
  let hasPatch = false;
  if (existsSync(genPath)) {
    dafnySavePatch(genPath, dfyPath, patchPath);
    hasPatch = readFileSync(patchPath, "utf-8").trim().length > 0;
  }

  // 3. Write new gen
  writeGen(genPath, text);

  // 4. Try verifying existing dfy as-is
  if (dafnyVerify(dfyPath, dir)) return;

  // 5. Failed — try applying captured patch to new gen
  if (hasPatch) {
    console.log("Verification failed. Trying to apply patch...");
    if (dafnyApplyPatch(genPath, dfyPath, patchPath) && dafnyVerify(dfyPath, dir)) return;
  }

  // 6. Needs LLM re-adaptation
  console.error(`FAILED: ${path.basename(dfyPath)} needs manual re-adaptation.`);
  console.error(`  ${genPath} has the new generated code.`);
  if (hasPatch) console.error(`  ${patchPath} has the captured patch.`);
  process.exit(1);
}
