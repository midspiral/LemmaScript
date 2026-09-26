/** Dafny backend commands: gen, check, regen. */

import { readFileSync } from "fs";
import { execFileSync } from "child_process";
import { proofRegen } from "./proof-files.js";
export { proofGen as dafnyGen, proofCheckDiff as dafnyCheckDiff } from "./proof-files.js";

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
  } catch (e: any) {
    if (e?.code === "ENOENT") {
      console.error("ERROR: `dafny` not found on PATH — verification never ran. Install Dafny 4.x: https://dafny.org/");
    }
    return false;
  }
}

export function dafnyRegen(genPath: string, dfyPath: string, basePath: string, text: string, dir: string, timeLimit?: number, extraFlags?: string, noVerify = false) {
  proofRegen(genPath, dfyPath, basePath, text, () => dafnyVerify(dfyPath, dir, timeLimit, extraFlags), noVerify);
}
