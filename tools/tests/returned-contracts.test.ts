import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

const dafny = spawnSync(process.env.DAFNY_EXE || "dafny", ["--version"], { encoding: "utf8", timeout: 10_000 });
const installed = !dafny.error && dafny.status === 0;
if (process.env.LSC_REQUIRE_DAFNY && !installed) throw new Error("Returned-function contract tests require Dafny");
const loader = createRequire(import.meta.url).resolve("tsx");
const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const example = readFileSync(new URL("../../examples/accessPolicy.ts", import.meta.url), "utf8");
const brokenPolicy = example.replace("return value => eligible(value) && !denied(value)", "return value => eligible(value)");
assert.notEqual(brokenPolicy, example, "The mutation must remove the deny override");
for (const broken of [false, true]) {
  test(`Dafny access-policy example ${broken ? "rejects removal of the deny override" : "verifies returned predicates and their clients"}`, { skip: !installed, timeout: 30_000 }, () => {
    const dir = mkdtempSync(join(tmpdir(), "lsc-returned-contract-"));
    try {
      const source = join(dir, "accessPolicy.ts");
      writeFileSync(source, broken ? brokenPolicy : example);
      const result = spawnSync(process.execPath, ["--import", loader, cli, "check", "--backend=dafny", source], { cwd: dir, encoding: "utf8", timeout: 25_000 });
      assert.ifError(result.error);
      const output = result.stdout + result.stderr;
      assert.equal(result.status, broken ? 1 : 0, output);
      assert.match(output, broken ? /a postcondition could not be proved/ : /0 errors/);
    } finally { rmSync(dir, { recursive: true, force: true }); }
  });
}
