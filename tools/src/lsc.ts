/**
 * lsc — LemmaScript compiler CLI
 *
 * Pipeline: extract → resolve → transform → emit
 */

import { Project } from "ts-morph";
import { existsSync, writeFileSync } from "fs";
import { execSync } from "child_process";
import path from "path";
import { extractModule } from "./extract.js";
import { resolveModule } from "./resolve.js";
import { transformModule } from "./transform.js";
import { emitFile } from "./emit.js";

function main() {
  const [cmd, filePath] = process.argv.slice(2);
  if (!cmd || !filePath) {
    console.error("Usage: lsc <gen|check|extract> <file.ts>");
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
