/** CLI verification, negative contracts, regeneration, and executable lowering.
 * Invoked by test-fixtures.sh against the source compiler.
 */
import assert from "node:assert/strict";
import { copyFileSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { resolve, join } from "node:path";
import { spawnSync } from "node:child_process";
import { createRequire } from "node:module";

const dir = mkdtempSync(join(tmpdir(), "lsc-async-"));
const cli = resolve("tools/src/lsc.ts");
const loader = createRequire(import.meta.url).resolve("tsx");
const source = readFileSync("tools/fixtures/async-functions.ts", "utf8");
writeFileSync(join(dir, "lemmascript.json"), "{}\n");
function run(command: string, args: string[], success: boolean) {
  const result = spawnSync(command, args, { cwd: dir, encoding: "utf8", timeout: 180_000,
    env: { ...process.env, LSC_RUN_LOG: "true" } });
  const output = result.stdout + result.stderr;
  assert.ifError(result.error);
  if (success) assert.equal(result.status, 0, output);
  else {
    assert.notEqual(result.status, 0, "false contract unexpectedly verified");
    assert.match(output, /assertion might not hold|precondition.*could not be proved|postcondition.*could not be proved/);
    assert.doesNotMatch(output, /parse errors|resolution\/type errors|timed out|internal compilation exception/i);
  }
  return output;
}
function check(name: string, text: string, success: boolean) {
  const path = join(dir, name + ".ts");
  writeFileSync(path, text);
  return run(process.execPath, ["--import", loader, cli, "check", "--backend=dafny", "--time-limit=15", path], success);
}
try {
  check("async-functions", source, true);
  const info = JSON.parse(run(process.execPath, ["--import", loader, cli, "info", "--typed", join(dir, "async-functions.ts")], true));
  const boundary = info.functions.find((f: { name: string }) => f.name === "absolute");
  assert.equal(boundary.isAsync, true);
  assert.deepEqual(boundary.nativeParams, ["p"]);
  assert.equal(boundary.returnTy.kind, "promise");
  assert.equal(info.dafny.error, undefined);
  check("wrong-result", source.replace("return x + 1n;", "return x + 2n;"), false);
  check("wrong-callee-precondition", source.replace("await positiveOnly(n)", "await positiveOnly(-n)"), false);
  check("wrong-handler", source.replace("? 7n : 9n", "? 8n : 9n"), false);

  writeFileSync(join(dir, "wrong-result.ts"), source);
  run(process.execPath, ["--import", loader, cli, "regen", "--backend=dafny", join(dir, "wrong-result.ts")], true);
  const report = JSON.parse(run(process.execPath, ["--import", loader, cli, "runs", "--json"], true));
  assert.deepEqual(report.catches.map((c: { function: string; kind: string; evidence: { hint: string } }) =>
    [c.function, c.kind, c.evidence.hint]), [["increment", "source-fix", "code"]]);
  assert.deepEqual(report.open.map((c: { function: string }) => c.function).sort(), ["guarded", "recover"]);
  assert.deepEqual(report.dropped, []);

  const proof = join(dir, "async-functions.dfy");
  writeFileSync(proof, readFileSync(proof, "utf8") + "\nlemma UserAddition() ensures 1 == 1 {}\n");
  const updated = source.replace("\\result === n + 1n", "\\result === 1n + n");
  writeFileSync(join(dir, "async-functions.ts"), updated);
  run(process.execPath, ["--import", loader, cli, "regen", "--backend=dafny", join(dir, "async-functions.ts")], true);
  assert.match(readFileSync(proof, "utf8"), /lemma UserAddition\(\)/);

  copyFileSync("tools/fixtures/async-runtime-check.dfy", join(dir, "async-runtime-check.dfy"));
  const output = run("dafny", ["run", "--target:py", "--no-verify", "async-runtime-check.dfy"], true);
  assert.match(output, /async runtime checks passed/);
  console.log(`Async verification and runtime checks passed (${dir}).`);
} catch (error) {
  console.error(`Async artifacts and run logs retained at ${dir}`);
  throw error;
}
