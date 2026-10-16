import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

const example = readFileSync(new URL("../../examples/resultPipeline.ts", import.meta.url), "utf8");
const loader = createRequire(import.meta.url).resolve("tsx");
const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const cases = [
  ["verifies the order-validation pipeline", example, false],
  ["rejects reversed error priority", example.replace("flatMap(checkQuantity(order), checkPrice)", "flatMap(checkPrice(order), checkQuantity)"), true],
  ["rejects an incorrect total", example.replace("valid.quantity * valid.unitPrice", "valid.quantity + valid.unitPrice"), true],
] as const;
for (const backend of ["dafny", "fstar"] as const) {
  const exe = backend === "dafny" ? process.env.DAFNY_EXE || "dafny" : process.env.FSTAR_EXE || "fstar.exe";
  const version = spawnSync(exe, ["--version"], { encoding: "utf8", timeout: 10_000 });
  const installed = !version.error && version.status === 0;
  if (process.env[`LSC_REQUIRE_${backend.toUpperCase()}`] && !installed) throw new Error(`${backend} is required`);
  for (const [label, text, broken] of cases) {
    if (broken) assert.notEqual(text, example, label);
    test(`${backend} ${label}`, { skip: !installed, timeout: 40_000 }, () => {
      const dir = mkdtempSync(join(tmpdir(), "lsc-result-pipeline-"));
      try {
        const source = join(dir, "resultPipeline.ts");
        writeFileSync(source, text);
        const result = spawnSync(process.execPath, ["--import", loader, cli, "check", `--backend=${backend}`, source], { cwd: dir, encoding: "utf8", timeout: 35_000 });
        assert.ifError(result.error);
        const output = result.stdout + result.stderr;
        assert.equal(result.status, broken ? 1 : 0, output);
        assert.match(output, broken ? /postcondition|Failed to prove|Could not prove/i : /0 errors|All verification conditions discharged/);
      } finally { rmSync(dir, { recursive: true, force: true }); }
    });
  }
}
