/** Dafny backend commands: gen, check, regen. */

import { readFileSync } from "fs";
import { execFileSync } from "child_process";
import { proofCheckDiff, proofRegen } from "./proof-files.js";
export { proofGen as dafnyGen } from "./proof-files.js";
import path from "path";
import { DEFAULT_OPTIONS, parseOptionValue, type LscOptions } from "./config.js";

export function dafnyCheckDiff(genPath: string, dfyPath: string): boolean {
  if (!proofCheckDiff(genPath, dfyPath)) return false;

  // Proof additions must retain the model chosen by the generated companion.
  try {
    const generated = readStringSemantics(readFileSync(genPath, "utf-8"));
    const proof = readStringSemantics(readFileSync(dfyPath, "utf-8"));
    if (proof !== generated) {
      throw new Error(`proof string-semantics=${proof} differs from generated string-semantics=${generated}`);
    }
  } catch (error) {
    console.error(`ERROR: ${path.basename(dfyPath)}: ${error instanceof Error ? error.message : String(error)}`);
    return false;
  }

  return true;
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
  proofRegen(genPath, dfyPath, basePath, text, () => dafnyVerify(dfyPath, dir, timeLimit, extraFlags), noVerify, dafnyCheckDiff);
}
