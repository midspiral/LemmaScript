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
  for (const filePath of [genPath, dfyPath]) {
    if (!existsSync(filePath)) {
      console.error(`ERROR: cannot verify additions-only diff; file does not exist: ${filePath}`);
      return false;
    }
  }

  let diff = "";
  try {
    diff = execFileSync(
      "git",
      ["diff", "--no-index", "--minimal", "--no-color", "--no-ext-diff", "--no-textconv", "--text", "--", genPath, dfyPath],
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
        `ERROR: could not run \`git diff\` to verify ${path.basename(dfyPath)} is additions-only` +
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
    console.error(`WARNING: ${path.basename(dfyPath)} has modifications to generated lines (not additions-only):`);
    for (const d of deletions.slice(0, 5)) console.error("  " + d);
    return false;
  }
  return true;
}

const OPTIONS_HEADER = /^\/\/ lsc options:(.*)$/m;
const STRING_SEMANTICS = ["unicode-scalar", "javascript-utf16"];

/**
 * Verifier arguments implied by a generated file's `// lsc options:` header
 * (DESIGN_STRINGS.md §5–6). Read from the artifact rather than the config, so a
 * standalone `.dfy` verifies under the model it was generated for. The char
 * mode is always pinned — a default is not a pin. Only `--unicode-char:false`
 * is deprecated in Dafny 4.11, and `--allow-deprecation` waives exactly that
 * warning; the blanket warning waiver would also un-fatal vacuity and
 * missing-{:axiom} warnings, which a verifier must keep fatal.
 */
export function dafnyVerifyArgs(content: string, timeLimit?: number, extraFlags?: string): { args: string[]; error?: string } {
  let stringSemantics = "unicode-scalar";
  const header = content.match(OPTIONS_HEADER);
  for (const token of (header?.[1] ?? "").trim().split(/\s+/).filter(Boolean)) {
    const eq = token.indexOf("=");
    const key = eq < 0 ? token : token.slice(0, eq);
    const value = eq < 0 ? "" : token.slice(eq + 1);
    if (key !== "string-semantics") continue;
    if (!STRING_SEMANTICS.includes(value)) {
      return { args: [], error: `ERROR: unknown string-semantics '${value}' in the generated header; this lsc knows ${STRING_SEMANTICS.join(", ")} (DESIGN_STRINGS.md).` };
    }
    stringSemantics = value;
  }
  const utf16 = stringSemantics === "javascript-utf16";
  const usesStandardLibrary = content.includes("Std.");
  if (utf16 && usesStandardLibrary) {
    return { args: [], error:
      "ERROR: this proof combines \"string-semantics\": \"javascript-utf16\" with Dafny's standard library. " +
      "Dafny 4.11 cannot load its Unicode-scalar standard library under --unicode-char:false. " +
      "Remove the Std.* import from the proof additions, or set \"unicode-scalar\" in lemmascript.json." };
  }
  const args: string[] = ["verify"];
  if (usesStandardLibrary) args.push("--standard-libraries");
  if (timeLimit) args.push("--verification-time-limit", String(timeLimit));
  if (extraFlags) {
    for (const tok of extraFlags.split(/\s+/)) if (tok) args.push(tok);
  }
  args.push(utf16 ? "--unicode-char:false" : "--unicode-char:true");
  if (utf16) args.push("--allow-deprecation");
  return { args };
}

export function dafnyVerify(dfyPath: string, dir: string, timeLimit?: number, extraFlags?: string): boolean {
  console.log("Running dafny verify...");
  try {
    const { args, error } = dafnyVerifyArgs(readFileSync(dfyPath, "utf-8"), timeLimit, extraFlags);
    if (error) { console.error(error); return false; }
    args.push(dfyPath);
    execFileSync("dafny", args, { cwd: dir, stdio: "inherit" });
    return true;
  } catch (e: any) {
    if (e?.code === "ENOENT") {
      console.error("ERROR: `dafny` not found on PATH — verification never ran. Install Dafny 4.x: https://dafny.org/");
    }
    return false;
  }
}

export function dafnyRegen(genPath: string, dfyPath: string, basePath: string, text: string, dir: string, timeLimit?: number, extraFlags?: string, noVerify = false) {
  // 1. Read old gen before overwriting (needed for base seeding)
  const oldGen = existsSync(genPath) ? readFileSync(genPath, "utf-8") : "";

  // 2. Always write new gen so user can inspect latest output
  writeGen(genPath, text);

  // 3. No .dfy yet — create dfy, verify, done
  if (!existsSync(dfyPath)) {
    writeFileSync(dfyPath, text);
    console.log(`Created: ${path.basename(dfyPath)}`);
    if (!noVerify && !dafnyVerify(dfyPath, dir, timeLimit, extraFlags)) {
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

  // 7. Verify (skipped under --no-verify: caller verifies separately)
  if (!noVerify && !dafnyVerify(dfyPath, dir, timeLimit, extraFlags)) {
    // The clean merge already incorporated this generation into the proof
    // file. Keep that generation as the next merge anchor even though the
    // verifier rejected the current proof state; otherwise the next regen
    // compares against the pre-merge generation and can duplicate declarations.
    writeFileSync(basePath, text);
    console.error(`FAILED: ${path.basename(dfyPath)} verification failed.`);
    process.exit(1);
  }

  // 8. Success — delete base (gen is now the anchor)
  if (existsSync(basePath)) unlinkSync(basePath);
}
