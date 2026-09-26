/** Generated baselines, additions-only proof files, and three-way recovery. */

import { existsSync, readFileSync, writeFileSync, copyFileSync, unlinkSync } from "fs";
import { execFileSync } from "child_process";
import path from "path";

function writeGen(genPath: string, text: string) {
  writeFileSync(genPath, text);
  console.log(`Generated: ${genPath}`);
}

export function proofGen(genPath: string, proofPath: string, text: string) {
  writeGen(genPath, text);
  if (!existsSync(proofPath)) {
    writeFileSync(proofPath, text);
    console.log(`Created: ${proofPath}`);
  }
}

export function proofCheckDiff(genPath: string, proofPath: string): boolean {
  for (const filePath of [genPath, proofPath]) {
    if (!existsSync(filePath)) {
      console.error(`ERROR: cannot verify additions-only diff; file does not exist: ${filePath}`);
      return false;
    }
  }

  let diff = "";
  try {
    diff = execFileSync(
      "git",
      ["diff", "--no-index", "--minimal", "--no-color", "--no-ext-diff", "--no-textconv", "--text", "--", genPath, proofPath],
      { encoding: "utf-8", stdio: ["ignore", "pipe", "pipe"] },
    );
  } catch (e: any) {
    // `git diff --no-index` exits 1 for a valid, non-empty comparison. Every
    // other exit shape means the comparison did not complete, even when git
    // happened to return partial stdout.
    const status = e?.status;
    const stdout = typeof e?.stdout === "string" ? e.stdout : "";
    if (status !== 1 || e?.signal != null || e?.code != null || !stdout.startsWith("diff --git ")) {
      const detail = typeof e?.stderr === "string" ? e.stderr.trim() : "";
      console.error(
        `ERROR: could not run \`git diff\` to verify ${path.basename(proofPath)} is additions-only` +
        `${status === undefined ? " (is git installed?)" : ` (git exited ${status})`}` +
        `${detail ? `: ${detail}` : ""}`,
      );
      return false;
    }
    diff = stdout;
  }
  // Only file headers are metadata. Inside a hunk, even a line beginning
  // with "---" is a deletion (for example, text inside a multiline string).
  const deletions: string[] = [];
  let inHunk = false;
  for (const line of diff.split("\n")) {
    if (line.startsWith("diff --git ")) inHunk = false;
    else if (line.startsWith("@@ ")) inHunk = true;
    else if (inHunk && line.startsWith("-")) deletions.push(line);
  }
  if (deletions.length > 0) {
    console.error(`WARNING: ${path.basename(proofPath)} has modifications to generated lines (not additions-only):`);
    for (const d of deletions.slice(0, 5)) console.error("  " + d);
    return false;
  }
  return true;
}

export function proofRegen(genPath: string, proofPath: string, basePath: string, text: string, verify: () => boolean, noVerify = false) {
  // 1. Read old gen before overwriting (needed for base seeding)
  const oldGen = existsSync(genPath) ? readFileSync(genPath, "utf-8") : "";

  // 2. Always write new gen so user can inspect latest output
  writeGen(genPath, text);

  // 3. No working proof yet — seed it and verify.
  if (!existsSync(proofPath)) {
    writeFileSync(proofPath, text);
    console.log(`Created: ${path.basename(proofPath)}`);
    if (!noVerify && !verify()) {
      console.error(`FAILED: ${path.basename(proofPath)} verification failed on first run.`);
      process.exit(1);
    }
    return;
  }

  // 4. Determine anchor: base file if it exists (dirty state), otherwise old gen
  const anchor = existsSync(basePath) ? readFileSync(basePath, "utf-8") : oldGen;

  // 5. If gen changed, three-way merge
  if (text !== anchor) {
    const savedProof = readFileSync(proofPath, "utf-8");
    if (!existsSync(basePath)) writeFileSync(basePath, anchor);
    const mergedPath = proofPath + ".merged";
    console.log("Gen changed. Three-way merging...");
    try {
      execFileSync("git", ["merge-file", proofPath, basePath, genPath], { stdio: "pipe" });
      console.log(`Merged: ${path.basename(proofPath)}`);
    } catch (e: any) {
      if (e.status > 0) {
        copyFileSync(proofPath, mergedPath);
        writeFileSync(proofPath, savedProof);
        console.error(`CONFLICT: ${path.basename(proofPath)} — merge had conflicts, proof restored. See ${path.basename(mergedPath)}`);
        process.exit(1);
      }
      throw e;
    }
  }

  // 6. Check gen invariant (unconditional)
  if (!proofCheckDiff(genPath, proofPath)) {
    console.error(`FAILED: ${path.basename(proofPath)} has modifications to generated lines.`);
    process.exit(1);
  }

  // 7. Verify (skipped under --no-verify: caller verifies separately)
  if (!noVerify && !verify()) {
    // The clean merge already incorporated this generation into the proof
    // file. Keep that generation as the next merge anchor even though the
    // verifier rejected the current proof state; otherwise the next regen
    // compares against the pre-merge generation and can duplicate declarations.
    writeFileSync(basePath, text);
    console.error(`FAILED: ${path.basename(proofPath)} verification failed.`);
    process.exit(1);
  }

  // 8. Success — delete base (gen is now the anchor)
  if (existsSync(basePath)) unlinkSync(basePath);
}
