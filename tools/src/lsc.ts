/**
 * lsc — LemmaScript compiler CLI
 *
 * Usage:
 *   lsc gen <file.ts>       — generate .def.lean
 *   lsc check <file.ts>    — gen + lake build
 *   lsc extract <file.ts>  — print IR JSON
 */

import { Project } from "ts-morph";
import { existsSync, writeFileSync } from "fs";
import { execSync } from "child_process";
import path from "path";
import { extractModule } from "./extract.js";
import { generateDef } from "./codegen.js";

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
  const mod = extractModule(sourceFile);

  if (cmd === "extract") {
    console.log(JSON.stringify(mod, null, 2));
    return;
  }

  // Determine spec import
  const dir = path.dirname(absPath);
  const base = path.basename(filePath, ".ts");
  const specPath = path.join(dir, `${base}.spec.lean`);
  const specImport = existsSync(specPath) ? `«${base}.spec»` : undefined;

  const lean = generateDef(mod, specImport);

  if (cmd === "gen") {
    const defPath = path.join(dir, `${base}.def.lean`);
    writeFileSync(defPath, lean);
    console.log(`Generated: ${defPath}`);
    return;
  }

  if (cmd === "check") {
    const defPath = path.join(dir, `${base}.def.lean`);
    writeFileSync(defPath, lean);
    console.log(`Generated: ${defPath}`);

    // Find lakefile
    let lakeDir = dir;
    while (lakeDir !== path.dirname(lakeDir)) {
      if (existsSync(path.join(lakeDir, "lakefile.lean"))) break;
      lakeDir = path.dirname(lakeDir);
    }

    // Build the proof file
    const proofPath = path.join(dir, `${base}.proof.lean`);
    if (!existsSync(proofPath)) {
      console.error(`No proof file: ${proofPath}`);
      console.error(`Create it with: prove_correct ${mod.functions[0]?.name ?? "fn"} by loom_solve`);
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
