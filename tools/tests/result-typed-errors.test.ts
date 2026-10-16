import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { copyFileSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

const source = new URL("../../examples/resultTypedErrors.ts", import.meta.url);
const example = readFileSync(source, "utf8");
const loader = createRequire(import.meta.url).resolve("tsx");
const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const cases = [
  ["verifies distinct error types in the order pipeline", example, false],
  ["preserves explicit type argument order with an erased primitive constraint", example
    .replace("flatMap<A, B, E>", "flatMap<Index extends number, A, B, E>")
    .replace("flatMap<Order, Order, OrderError>", "flatMap<number, Order, Order, OrderError>"), false],
  ["rejects reversed error priority", example.replace("(checkQuantity(order), checkPrice)", "(checkPrice(order), checkQuantity)"), true],
  ["rejects a changed quantity payload", example.replace("quantity: order.quantity }", "quantity: order.quantity + 1 }"), true],
  ["rejects a changed price payload", example.replace("unitPrice: order.unitPrice }", "unitPrice: order.unitPrice - 1 }"), true],
  ["rejects an incorrect total", example.replace("valid.quantity * valid.unitPrice", "valid.quantity + valid.unitPrice"), true],
  ["rejects a missing price check", example.replace("(checkQuantity(order), checkPrice)", "(checkQuantity(order), checkQuantity)"), true],
] as const;

for (const backend of ["dafny", "fstar"] as const) {
  const exe = backend === "dafny" ? process.env.DAFNY_EXE || "dafny" : process.env.FSTAR_EXE || "fstar.exe";
  const version = spawnSync(exe, ["--version"], { encoding: "utf8", timeout: 10_000 });
  const installed = !version.error && version.status === 0;
  if (process.env[`LSC_REQUIRE_${backend.toUpperCase()}`] && !installed) throw new Error(`${backend} is required`);
  for (const [label, text, broken] of cases) {
    if (broken) assert.notEqual(text, example, label);
    test(`${backend} ${label}`, { skip: !installed, timeout: 50_000 }, () => {
      const dir = mkdtempSync(join(tmpdir(), "lsc-result-typed-errors-"));
      try {
        const file = join(dir, "resultTypedErrors.ts");
        writeFileSync(file, text);
        const extension = backend === "dafny" ? "dfy" : "fst";
        for (const suffix of [extension, `${extension}.gen`]) {
          copyFileSync(fileURLToPath(new URL(`resultTypedErrors.${suffix}`, source)), file.replace(/\.ts$/, `.${suffix}`));
        }
        const result = spawnSync(process.execPath, ["--import", loader, cli, "regen", `--backend=${backend}`, file], { cwd: dir, encoding: "utf8", timeout: 45_000 });
        assert.ifError(result.error);
        const output = result.stdout + result.stderr;
        assert.equal(result.status, broken ? 1 : 0, output);
        assert.match(output, broken ? /postcondition|Failed to prove|Could not prove/i : /0 errors|All verification conditions discharged/);
      } finally { rmSync(dir, { recursive: true, force: true }); }
    });
  }
}
