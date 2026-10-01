import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

const loader = createRequire(import.meta.url).resolve("tsx");
const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const example = readFileSync(new URL("../../examples/dual.ts", import.meta.url), "utf8");
const asInterface = example.replace(
  "export type Predicate<A> = (value: A) => boolean;",
  "export interface Predicate<A> { (value: A): boolean }",
);
const broken = example.replace("return value => self(value) && !denied(value)", "return value => self(value)");
assert.notEqual(asInterface, example, "The variant must use a callable interface");
assert.notEqual(broken, example, "The mutation must remove the deny override");

for (const backend of ["dafny", "fstar"] as const) {
  const exe = backend === "dafny" ? process.env.DAFNY_EXE || "dafny" : process.env.FSTAR_EXE || "fstar.exe";
  const version = spawnSync(exe, ["--version"], { encoding: "utf8", timeout: 10_000 });
  const installed = !version.error && version.status === 0;
  if (process.env["LSC_REQUIRE_" + backend.toUpperCase()] && !installed) throw new Error(backend + " is required");
  for (const [label, source, fails] of [
    ["verifies generic callable aliases", example, false],
    ["verifies equivalent callable interfaces", asInterface, false],
    ["rejects removing the deny override", broken, true],
  ] as const) {
    test(`${backend} dual ${label}`, { skip: !installed, timeout: 60_000 }, () => {
      const dir = mkdtempSync(join(tmpdir(), "lsc-dual-"));
      try {
        writeFileSync(join(dir, "dual.ts"), source);
        const result = spawnSync(process.execPath,
          ["--import", loader, cli, "check", "--backend=" + backend, "--time-limit=20", "dual.ts"],
          { cwd: dir, encoding: "utf8", timeout: 55_000 });
        assert.ifError(result.error);
        const output = result.stdout + result.stderr;
        assert.equal(result.status, fails ? 1 : 0, output);
        assert.match(output, fails ? /postcondition|Failed to prove|Could not prove/i : /0 errors|All verification conditions discharged/);
      } finally { rmSync(dir, { recursive: true, force: true }); }
    });
  }
}
