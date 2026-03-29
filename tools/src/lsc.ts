/**
 * lsc — LemmaScript compiler CLI
 *
 * Usage:
 *   npx tsx src/lsc.ts check <file.ts>     — extract, generate, print Lean
 *   npx tsx src/lsc.ts extract <file.ts>   — extract only (print IR JSON)
 */

import { Project } from "ts-morph";
import { existsSync } from "fs";
import path from "path";
import { extractModule } from "./extract.js";
import { generateLean } from "./codegen.js";

function main() {
  const [cmd, filePath] = process.argv.slice(2);

  if (!cmd || !filePath) {
    console.error("Usage: lsc <check|extract> <file.ts>");
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

  if (cmd === "check" || cmd === "gen") {
    const baseName = path.basename(filePath, ".ts");
    const specPath = path.join(path.dirname(absPath), `${baseName}.spec.lean`);
    const specImport = existsSync(specPath) ? `«${baseName}.spec»` : undefined;
    const lean = generateLean(mod, specImport);
    console.log(lean);
    return;
  }

  console.error(`Unknown command: ${cmd}`);
  process.exit(1);
}

main();
