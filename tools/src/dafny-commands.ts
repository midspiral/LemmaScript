/**
 * Dafny backend commands: gen, check, regen.
 */

import { existsSync, readFileSync, writeFileSync, copyFileSync, unlinkSync, mkdtempSync, rmSync } from "fs";
import os from "os";
import { execFileSync } from "child_process";
import path from "path";
import { DEFAULT_OPTIONS, parseOptionValue, type LscOptions } from "./config.js";
import type { RunLog } from "./run-log.js";

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

export function dafnyCheckDiff(genPath: string, dfyPath: string, log?: RunLog): boolean {
  const ok = additionsOnly(genPath, dfyPath);
  if (!ok) log?.finish({ stage: "diff", exit: 1, dfyPath });
  return ok;
}

/**
 * The proof must be the generated file plus additions. Two passes:
 *
 * 1. Source lines: `git diff --minimal` of `.dfy.gen` against `.dfy` shows no
 *    deletions. Fast, and its messages point at the author's own lines.
 * 2. Canonical print: the same diff on `dafny resolve --print` output of both
 *    files. Dafny re-prints the parsed program with comments dropped and one
 *    clause per line, so a generated clause hidden inside an added block
 *    comment or verbatim string, or extended by an added `|| true` line,
 *    becomes a deleted or modified printed line. See DESIGN_DIFF.md.
 */
function additionsOnly(genPath: string, dfyPath: string): boolean {
  for (const filePath of [genPath, dfyPath]) {
    if (!existsSync(filePath)) {
      console.error(`ERROR: cannot verify additions-only diff; file does not exist: ${filePath}`);
      return false;
    }
  }

  // Proof additions must retain the model chosen by the generated companion.
  let utf16: boolean;
  try {
    const generated = readStringSemantics(readFileSync(genPath, "utf-8"));
    const proof = readStringSemantics(readFileSync(dfyPath, "utf-8"));
    if (proof !== generated) {
      throw new Error(`proof string-semantics=${proof} differs from generated string-semantics=${generated}`);
    }
    utf16 = proof === "javascript-utf16";
  } catch (error) {
    console.error(`ERROR: ${path.basename(dfyPath)}: ${error instanceof Error ? error.message : String(error)}`);
    return false;
  }

  const source = gitDiff(genPath, dfyPath, dfyPath);
  if (source === null) return false;
  const deletions = hunkLines(source).filter(l => l.startsWith("-"));
  if (deletions.length > 0) {
    console.error(`WARNING: ${path.basename(dfyPath)} has modifications to generated lines (not additions-only):`);
    for (const d of deletions.slice(0, 5)) console.error("  " + d);
    return false;
  }
  return additionsOnlyCanonical(genPath, dfyPath, utf16);
}

/** `git diff --no-index --minimal a b`, or null (after reporting) when the
 *  comparison did not complete. */
function gitDiff(a: string, b: string, reportAs: string, context?: number): string | null {
  const args = ["diff", "--no-index", "--minimal", "--no-color", "--no-ext-diff", "--no-textconv", "--text"];
  if (context !== undefined) args.push(`--unified=${context}`);
  try {
    return execFileSync("git", [...args, "--", a, b], { encoding: "utf-8", stdio: ["ignore", "pipe", "pipe"] });
  } catch (e: any) {
    // `git diff --no-index` exits 1 for a valid, non-empty comparison. Every
    // other exit shape means the comparison did not complete, even when git
    // happened to return partial stdout.
    const status = e?.status;
    const stdout = typeof e?.stdout === "string" ? e.stdout : "";
    if (status === 1 && e?.signal == null && e?.code == null && stdout.startsWith("diff --git ")) return stdout;
    const detail = typeof e?.stderr === "string" ? e.stderr.trim() : "";
    console.error(
      `ERROR: could not run \`git diff\` to verify ${path.basename(reportAs)} is additions-only` +
      `${status == null ? " (is git installed?)" : ` (git exited ${status})`}` +
      `${detail ? `: ${detail}` : ""}`,
    );
    return null;
  }
}

/** The body lines of every hunk, with their leading ` `, `+`, or `-`. Only
 *  file headers are metadata: inside a hunk, even a line beginning with "---"
 *  is a deletion (for example, text inside a multiline string). */
function hunkLines(diff: string): string[] {
  const out: string[] = [];
  let inHunk = false;
  for (const line of diff.split("\n")) {
    if (line.startsWith("diff --git ")) inHunk = false;
    else if (line.startsWith("@@ ")) inHunk = true;
    else if (inHunk && line.length > 0 && !line.startsWith("\\")) out.push(line);
  }
  return out;
}

/** A `function … by method` is emitted with an empty functional body for the
 *  proof to supply, so the generated file alone does not parse. Given the
 *  full-context source diff (already known to have no deletions), rebuild the
 *  generated text with the proof's lines spliced into each such body. Those
 *  lines are proof-authored, so comparing against them hides nothing. */
function fillByMethodBodies(fullDiff: string): string {
  const lines = hunkLines(fullDiff), out: string[] = [];
  for (let k = 0; k < lines.length; k++) {
    if (lines[k].startsWith(" ")) { out.push(lines[k].slice(1)); continue; }
    let n = k;
    while (n < lines.length && lines[n].startsWith("+")) n++;
    if (out[out.length - 1] === "{" && lines[n]?.slice(1) === "}" && lines[n + 1]?.slice(1).startsWith("by method")) {
      for (; k < n; k++) out.push(lines[k].slice(1));
    }
    k = n - 1;
  }
  return out.join("\n");
}

/** `dafny resolve --print` of `src` into `out`, with the filename header line
 *  removed. Dafny prints after parsing and before resolution, so unresolved
 *  names (a predicate defined only in the proof) do not matter and the exit
 *  status is ignored; only a parse error leaves no output. The standard
 *  library is deliberately not loaded: parsing does not need it, and with it
 *  Dafny would print the whole library too. */
function printDafny(src: string, out: string, utf16: boolean): "ok" | "no-dafny" | "no-parse" {
  const args = ["resolve", `--print:${out}`, utf16 ? "--unicode-char:false" : "--unicode-char:true"];
  if (utf16) args.push("--allow-deprecation");
  try {
    execFileSync("dafny", [...args, src], { stdio: "ignore" });
  } catch (e: any) {
    if (e?.code === "ENOENT") return "no-dafny";
  }
  if (!existsSync(out)) return "no-parse";
  const lines = normalizePrint(readFileSync(out, "utf-8")).split("\n");
  if (lines[0]?.startsWith("//")) lines.shift();
  writeFileSync(out, lines.join("\n"));
  return "ok";
}

/** Make Dafny's print line-stable under proof additions. Besides joining
 *  verbatim strings, split a loop header's trailing `{` onto its own line:
 *  the printer writes `while c {` when a loop has no clauses and `while c`
 *  / `invariant …` / `{` once the proof adds invariants, which would make the
 *  generated header look modified. */
export function normalizePrint(text: string): string {
  return joinVerbatimStrings(text).replace(/^(\s*)((?:while|for)\b.*\S)\s*\{$/gm, "$1$2\n$1{");
}

/** Dafny prints a multi-line verbatim string `@"…"` as written, so generated
 *  lines wrapped in one would still appear in the print as if present. Join
 *  each such literal onto one line; it is the only Dafny token that can span
 *  lines once comments are gone, and an ordinary string cannot contain a raw
 *  newline. Scans string and char literals so a `@"` inside one is not a start. */
export function joinVerbatimStrings(text: string): string {
  const out: string[] = [];
  let buf = "";
  let inVerbatim = false;
  for (const line of text.split("\n")) {
    buf = inVerbatim ? `${buf}\\n${line}` : line;
    let inString = false, inChar = false;
    for (let i = 0; i < line.length; i++) {
      const c = line[i];
      if (inVerbatim) { if (c === '"') { if (line[i + 1] === '"') i++; else inVerbatim = false; } continue; }
      if (inString) { if (c === "\\") i++; else if (c === '"') inString = false; continue; }
      if (inChar) { if (c === "\\") i++; else if (c === "'") inChar = false; continue; }
      if (c === "@" && line[i + 1] === '"') { inVerbatim = true; i++; }
      else if (c === '"') inString = true;
      // `'` also appears inside identifiers (x'); a char literal never follows one.
      else if (c === "'" && (i === 0 || !/[\w?']/.test(line[i - 1]))) inChar = true;
    }
    if (!inVerbatim) out.push(buf);
  }
  if (inVerbatim) out.push(buf);
  return out.join("\n");
}

function additionsOnlyCanonical(genPath: string, dfyPath: string, utf16: boolean): boolean {
  const tmp = mkdtempSync(path.join(os.tmpdir(), "lsc-print-"));
  try {
    // Dafny accepts only the .dfy extension; the generated file is .dfy.gen.
    const genCopy = path.join(tmp, "generated.dfy");
    copyFileSync(genPath, genCopy);
    const genPrint = path.join(tmp, "generated.print.dfy");
    const dfyPrint = path.join(tmp, "proof.print.dfy");
    let g = printDafny(genCopy, genPrint, utf16);
    if (g === "no-parse") {
      const full = gitDiff(genPath, dfyPath, dfyPath, readFileSync(dfyPath, "utf-8").split("\n").length + 1);
      if (full !== null) { writeFileSync(genCopy, fillByMethodBodies(full)); g = printDafny(genCopy, genPrint, utf16); }
    }
    if (g === "no-dafny") {
      console.warn(`WARNING: \`dafny\` not found on PATH; ${path.basename(dfyPath)} was checked additions-only on source lines only ` +
        "(comments and strings were not normalized).");
      return true;
    }
    if (g === "no-parse") {
      console.warn(`WARNING: ${path.basename(genPath)} does not parse as Dafny on its own; ` +
        `${path.basename(dfyPath)} was checked additions-only on source lines only.`);
      return true;
    }
    if (printDafny(dfyPath, dfyPrint, utf16) !== "ok") {
      console.error(`ERROR: ${path.basename(dfyPath)} does not parse as Dafny; cannot check additions-only canonically.`);
      return false;
    }
    const diff = gitDiff(genPrint, dfyPrint, dfyPath);
    if (diff === null) return false;
    const hidden = hunkLines(diff).filter(l => l.startsWith("-"));
    if (hidden.length > 0) {
      console.error(`ERROR: ${path.basename(dfyPath)}: generated text is hidden or altered (not additions-only):`);
      for (const d of hidden.slice(0, 5)) console.error("  " + d);
      console.error("  Look for a block comment, verbatim string, or expression continuation around it.");
      return false;
    }
    return true;
  } finally {
    rmSync(tmp, { recursive: true, force: true });
  }
}

/** Read the saved model, rejecting ambiguous headers before verification. */
function readStringSemantics(content: string): LscOptions["string-semantics"] {
  const headers = [...content.matchAll(/^\/\/ lsc options:(.*)$/gm)];
  if (headers.length > 1) throw new Error("generated header: duplicate lsc options header (string-semantics must be unambiguous)");
  let model = DEFAULT_OPTIONS["string-semantics"];
  let seen = false;
  for (const token of (headers[0]?.[1] ?? "").trim().split(/\s+/).filter(Boolean)) {
    const eq = token.indexOf("=");
    const key = eq < 0 ? token : token.slice(0, eq);
    if (key !== "string-semantics") continue;
    if (seen) throw new Error("generated header: duplicate string-semantics option");
    seen = true;
    model = parseOptionValue(key, eq < 0 ? "" : token.slice(eq + 1), "generated header");
  }
  return model;
}

/**
 * Build verifier arguments from the generated file's `// lsc options:` header.
 * Reading the saved string model instead of the current project config keeps
 * verification consistent with generation, even if the config later changes.
 * Always pass `--unicode-char` explicitly. UTF-16 mode also needs
 * `--allow-deprecation` because Dafny 4.11 deprecates `--unicode-char:false`.
 * Other warning categories remain fatal.
 */
export function dafnyVerifyArgs(content: string, timeLimit?: number, extraFlags?: string): { args: string[]; error?: string } {
  let stringSemantics: LscOptions["string-semantics"];
  try {
    stringSemantics = readStringSemantics(content);
  } catch (error) {
    return { args: [], error: `ERROR: ${error instanceof Error ? error.message : String(error)}` };
  }
  const utf16 = stringSemantics === "javascript-utf16";
  const usesStandardLibrary = content.includes("Std.");
  if (utf16 && usesStandardLibrary) {
    return { args: [], error:
      "ERROR: this proof combines \"string-semantics\": \"javascript-utf16\" with Dafny's standard library. " +
      "Dafny 4.11 cannot load its Unicode-scalar standard library under --unicode-char:false. " +
      "Set \"dafny-library\": \"local\" in lemmascript.json or add //@ option dafny-library local, " +
      "then run lsc regen to regenerate collection helpers. " +
      "This does not rewrite handwritten Std.* imports or calls; replace those with local proofs or helpers separately." };
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

export function dafnyVerify(dfyPath: string, dir: string, timeLimit?: number, extraFlags?: string, log?: RunLog): boolean {
  console.log("Running dafny verify...");
  try {
    const { args, error } = dafnyVerifyArgs(readFileSync(dfyPath, "utf-8"), timeLimit, extraFlags);
    if (error) {
      console.error(error);
      log?.finish({ stage: "resolve", exit: 1, dfyPath });
      return false;
    }
    if (log) args.push(...log.dafnyArgs());
    args.push(dfyPath);
    execFileSync("dafny", args, { cwd: dir, stdio: "inherit" });
    log?.finish({ stage: "ok", exit: 0, dfyPath, results: log.readResults() });
    return true;
  } catch (e: any) {
    if (e?.code === "ENOENT") {
      console.error("ERROR: `dafny` not found on PATH — verification never ran. Install Dafny 4.x: https://dafny.org/");
      log?.discard();
      return false;
    }
    // Dafny writes no results when it stops at parsing or resolution.
    const results = log?.readResults() ?? null;
    log?.finish({ stage: results ? "verify" : "resolve", exit: 1, dfyPath, results });
    return false;
  }
}

export function dafnyRegen(genPath: string, dfyPath: string, basePath: string, text: string, dir: string, timeLimit?: number, extraFlags?: string, noVerify = false, log?: RunLog) {
  // 1. Read old gen before overwriting (needed for base seeding)
  const oldGen = existsSync(genPath) ? readFileSync(genPath, "utf-8") : "";

  // 2. Always write new gen so user can inspect latest output
  writeGen(genPath, text);

  // 3. No .dfy yet — create dfy, verify, done
  if (!existsSync(dfyPath)) {
    writeFileSync(dfyPath, text);
    console.log(`Created: ${path.basename(dfyPath)}`);
    if (!noVerify && !dafnyVerify(dfyPath, dir, timeLimit, extraFlags, log)) {
      console.error(`FAILED: ${path.basename(dfyPath)} verification failed on first run.`);
      process.exit(1);
    }
    log?.finish({ stage: "ok", exit: 0, dfyPath });
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
    const merge = (flags: string[]) => execFileSync(
      "git", ["merge-file", ...flags, "--", dfyPath, basePath, genPath],
      // A stable locale lets us recognize an unsupported option without
      // mistaking other usage errors for an older Git version.
      { encoding: "utf-8", stdio: ["ignore", "pipe", "pipe"], env: { ...process.env, LC_ALL: "C" } },
    );
    try {
      try {
        // Match the additions-only check: the default diff can misalign
        // unchanged generated lines after a large inserted proof block.
        merge(["--diff-algorithm=minimal"]);
      } catch (e: any) {
        if (e?.status !== 129 || e?.signal != null || e?.code != null
          || typeof e?.stderr !== "string"
          || !/^error: unknown option [`']diff-algorithm(?:=minimal)?'/m.test(e.stderr)) throw e;
        writeFileSync(dfyPath, savedDfy);
        console.warn("WARNING: this Git does not support git merge-file --diff-algorithm; retrying with the default algorithm. " +
          "Upgrade to Git 2.44 or later to avoid false conflicts after large proof additions.");
        merge([]);
      }
      console.log(`Merged: ${path.basename(dfyPath)}`);
    } catch (e: any) {
      // Git returns a conflict count capped at 127. Usage errors, fatal
      // errors and interrupted/failed processes are not merge conflicts.
      const conflict = Number.isInteger(e?.status) && e.status >= 1 && e.status <= 127
        && e?.signal == null && e?.code == null;
      try {
        if (conflict) copyFileSync(dfyPath, mergedPath);
      } finally {
        writeFileSync(dfyPath, savedDfy);
      }
      if (conflict) {
        console.error(`CONFLICT: ${path.basename(dfyPath)} — merge had conflicts, dfy restored. See ${path.basename(mergedPath)}`);
        log?.finish({ stage: "conflict", exit: 1, dfyPath });
      } else {
        const reason = e?.code === "ENOENT" ? " (git not found on PATH)"
          : e?.code != null ? ` (${e.code})`
          : e?.signal != null ? ` (signal ${e.signal})`
          : typeof e?.status === "number" ? ` (git exited ${e.status})` : "";
        const detail = typeof e?.stderr === "string" ? e.stderr.trim() : "";
        console.error(`ERROR: could not run \`git merge-file\` for ${path.basename(dfyPath)}${reason}; dfy restored` +
          `${detail ? `: ${detail}` : "."}`);
        log?.discard();
      }
      process.exit(1);
    }
  }

  // 6. Check gen invariant (unconditional)
  if (!dafnyCheckDiff(genPath, dfyPath, log)) {
    console.error(`FAILED: ${path.basename(dfyPath)} has modifications to generated lines.`);
    process.exit(1);
  }

  // 7. Verify (skipped under --no-verify: caller verifies separately)
  if (!noVerify && !dafnyVerify(dfyPath, dir, timeLimit, extraFlags, log)) {
    // The clean merge already incorporated this generation into the proof
    // file. Keep that generation as the next merge anchor even though the
    // verifier rejected the current proof state; otherwise the next regen
    // compares against the pre-merge generation and can duplicate declarations.
    writeFileSync(basePath, text);
    console.error(`FAILED: ${path.basename(dfyPath)} verification failed.`);
    process.exit(1);
  }

  // 8. Success — delete base (gen is now the anchor). After a verified run
  // dafnyVerify has already recorded the outcome; this records --no-verify.
  if (existsSync(basePath)) unlinkSync(basePath);
  log?.finish({ stage: "ok", exit: 0, dfyPath });
}
