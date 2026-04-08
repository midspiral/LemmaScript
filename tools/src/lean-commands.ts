/**
 * Lean backend commands: gen, check.
 */

import { existsSync, writeFileSync } from "fs";
import { execSync } from "child_process";
import path from "path";

export function leanGen(typesPath: string | null, defPath: string, typesText: string | null, defText: string) {
  if (typesPath && typesText) {
    writeFileSync(typesPath, typesText);
    console.log(`Generated: ${typesPath}`);
  }
  writeFileSync(defPath, defText);
  console.log(`Generated: ${defPath}`);
}

export function leanCheck(dir: string, base: string): boolean {
  let lakeDir = dir;
  while (lakeDir !== path.dirname(lakeDir)) {
    if (existsSync(path.join(lakeDir, "lakefile.lean"))) break;
    lakeDir = path.dirname(lakeDir);
  }

  const proofPath = path.join(dir, `${base}.proof.lean`);
  if (!existsSync(proofPath)) {
    console.error(`No proof file: ${proofPath}`);
    return false;
  }

  console.log("Running lake build...");
  try {
    execSync(`lake build`, { cwd: lakeDir, stdio: "inherit" });
    return true;
  } catch {
    return false;
  }
}
