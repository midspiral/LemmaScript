/**
 * Dafny backend commands: gen, check, regen.
 */

import { existsSync, readFileSync, writeFileSync, copyFileSync, unlinkSync } from "fs";
import { execFileSync } from "child_process";
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
  let diff = "";
  try {
    diff = execFileSync("git", ["diff", "--no-index", "--", genPath, dfyPath], { encoding: "utf-8", stdio: ["ignore", "pipe", "ignore"] });
  } catch (e: any) {
    // git diff exits 1 when files differ; stdout still holds the diff
    if (e && e.stdout != null) {
      diff = typeof e.stdout === "string" ? e.stdout : e.stdout.toString("utf-8");
    } else {
      return true;
    }
  }
  const deletions = diff.split("\n").filter(l => l.startsWith("-") && !l.startsWith("---"));
  if (deletions.length > 0) {
    console.error(`WARNING: ${path.basename(dfyPath)} has modifications to generated lines (not additions-only):`);
    for (const d of deletions.slice(0, 5)) console.error("  " + d);
    return false;
  }
  return true;
}

export function dafnyVerify(dfyPath: string, dir: string, timeLimit?: number, extraFlags?: string): boolean {
  console.log("Running dafny verify...");
  try {
    const content = readFileSync(dfyPath, "utf-8");
    const args: string[] = ["verify"];
    if (content.includes("Std.")) args.push("--standard-libraries");
    if (timeLimit) args.push("--verification-time-limit", String(timeLimit));
    if (extraFlags) {
      for (const tok of extraFlags.split(/\s+/)) if (tok) args.push(tok);
    }
    args.push(dfyPath);
    execFileSync("dafny", args, { cwd: dir, stdio: "inherit" });
    return true;
  } catch {
    return false;
  }
}

export function dafnyRegen(genPath: string, dfyPath: string, basePath: string, text: string, dir: string) {
  // 1. Read old gen before overwriting (needed for base seeding)
  const oldGen = existsSync(genPath) ? readFileSync(genPath, "utf-8") : "";

  // 2. Always write new gen so user can inspect latest output
  writeGen(genPath, text);

  // 3. No .dfy yet — create dfy, verify, done
  if (!existsSync(dfyPath)) {
    writeFileSync(dfyPath, text);
    console.log(`Created: ${path.basename(dfyPath)}`);
    if (!dafnyVerify(dfyPath, dir)) {
      console.error(`FAILED: ${path.basename(dfyPath)} verification failed on first run.`);
      process.exit(1);
    }
    return;
  }

  // 4. Determine anchor: base file if it exists (dirty state), otherwise old gen
  const anchor = existsSync(basePath) ? readFileSync(basePath, "utf-8") : oldGen;

  // 5. If gen changed, three-way merge
  if (text !== anchor) {
    const savedDfy = readFileSync(dfyPath, "utf-8");
    if (!existsSync(basePath)) writeFileSync(basePath, anchor);
    const mergedPath = dfyPath + ".merged";
    console.log("Gen changed. Three-way merging...");
    try {
      execFileSync("git", ["merge-file", dfyPath, basePath, genPath], { stdio: "pipe" });
      console.log(`Merged: ${path.basename(dfyPath)}`);
    } catch (e: any) {
      if (e.status > 0) {
        copyFileSync(dfyPath, mergedPath);
        writeFileSync(dfyPath, savedDfy);
        console.error(`CONFLICT: ${path.basename(dfyPath)} — merge had conflicts, dfy restored. See ${path.basename(mergedPath)}`);
        process.exit(1);
      }
      throw e;
    }
  }

  // 6. Check gen invariant (unconditional)
  if (!dafnyCheckDiff(genPath, dfyPath)) {
    console.error(`FAILED: ${path.basename(dfyPath)} has modifications to generated lines.`);
    process.exit(1);
  }

  // 7. Verify
  if (!dafnyVerify(dfyPath, dir)) {
    console.error(`FAILED: ${path.basename(dfyPath)} verification failed.`);
    process.exit(1);
  }

  // 8. Success — delete base (gen is now the anchor)
  if (existsSync(basePath)) unlinkSync(basePath);
}
