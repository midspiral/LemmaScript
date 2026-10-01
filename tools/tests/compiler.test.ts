import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { copyFileSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { compile as compileExpression, evaluate, shadowingDemo, type Expression, type Environment, type Continuation } from "../../examples/compiler.ts";

const source = new URL("../../examples/compiler.ts", import.meta.url);
const example = readFileSync(source, "utf8");
const core = example.slice(0, example.indexOf("export function run("));
const loader = createRequire(import.meta.url).resolve("tsx");
const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const cases = [
  ["verifies opaque compiler clients and lexical shadowing", example, false, true],
  ["proves the universal compiler theorem without proof additions", core, false, false],
  ["supports generic aliases for returned code", core.replace(
    "export type Code = (environment: Environment, continuation: Continuation) => bigint;",
    "type Binary<A, B, R> = (a: A, b: B) => R;\nexport type Code = Binary<Environment, Continuation, bigint>;"
  ), false, false],
  ["rejects dropping the continuation in the zero optimization", core.replace("continuation(0n)", "0n"), true, false],
  ["rejects forgetting lexical binding", core.replace(
    "body(bind(environment, expression.name, x), continuation)", "body(environment, continuation)"
  ), true, false],
  ["rejects removing the compiler contract from opaque client proofs", example.replace(
    /\/\/@ ensures forall\(environment: Environment[^\n]+/, "//@ ensures true"
  ), true, true],
] as const;

for (const backend of ["dafny", "fstar"] as const) {
  const exe = backend === "dafny" ? process.env.DAFNY_EXE || "dafny" : process.env.FSTAR_EXE || "fstar.exe";
  const version = spawnSync(exe, ["--version"], { encoding: "utf8", timeout: 10_000 });
  const installed = !version.error && version.status === 0;
  if (process.env["LSC_REQUIRE_" + backend.toUpperCase()] && !installed) throw new Error(backend + " is required");
  for (const [label, text, broken, proofs] of cases) {
    if (broken) assert.notEqual(text, proofs ? example : core, label);
    test(backend + " CPS compiler " + label, { skip: !installed, timeout: 60_000 }, () => {
      const dir = mkdtempSync(join(tmpdir(), "lsc-compiler-"));
      try {
        const file = join(dir, "compiler.ts");
        writeFileSync(file, text);
        if (proofs) {
          const extension = backend === "dafny" ? "dfy" : "fst";
          for (const suffix of [extension, extension + ".gen"]) {
            copyFileSync(fileURLToPath(new URL("compiler." + suffix, source)), file.replace(/\.ts$/, "." + suffix));
          }
        }
        const result = spawnSync(process.execPath,
          ["--import", loader, cli, proofs ? "regen" : "check", "--backend=" + backend, "--time-limit=20", file],
          { cwd: dir, encoding: "utf8", timeout: 55_000 });
        assert.ifError(result.error);
        const output = result.stdout + result.stderr;
        assert.equal(result.status, broken ? 1 : 0, output);
        assert.match(output, broken ? /postcondition|Failed to prove|Could not prove|assertion might not hold/i : /0 errors|All verification conditions discharged/);
      } finally { rmSync(dir, { recursive: true, force: true }); }
    });
  }
}

test("compiled closures agree with the interpreter across trees, environments and continuations", () => {
  const literal = (value: bigint): Expression => ({ kind: "literal", value });
  const variable = (name: number): Expression => ({ kind: "variable", name });
  const programs: Expression[] = [
    { kind: "add", left: literal(17n), right: literal(25n) },
    { kind: "multiply", left: literal(6n), right: literal(7n) },
    { kind: "multiply", left: variable(0), right: literal(0n) },
    { kind: "let", name: 0, value: variable(1), body: variable(0) },
  ];
  let seed = 19;
  const choose = (n: number): number => {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed % n;
  };
  function tree(depth: number): Expression {
    if (depth === 0) return choose(2) === 0 ? literal(BigInt(choose(7) - 3)) : variable(choose(2));
    switch (choose(3)) {
      case 0: return { kind: "add", left: tree(depth - 1), right: tree(depth - 1) };
      case 1: return { kind: "multiply", left: tree(depth - 1), right: tree(depth - 1) };
      default: return { kind: "let", name: choose(2), value: tree(depth - 1), body: tree(depth - 1) };
    }
  }
  for (let i = 0; i < 128; i++) programs.push(tree(3));
  const continuations: Continuation[] = [x => x, x => 10n * x + 1n, x => x * x, () => 7n];
  for (const expression of programs) {
    const code = compileExpression(expression);
    for (const input of [-3n, -1n, 0n, 2n, 5n, 9007199254740993n]) {
      const environment: Environment = name => input + BigInt(name);
      const expected = evaluate(expression, environment);
      for (const continuation of continuations) {
        assert.equal(code(environment, continuation), continuation(expected));
      }
    }
  }
  for (const input of [-7n, -1n, 0n, 1n, 13n, 9007199254740993n]) {
    assert.equal(shadowingDemo(input), 30n * (input + 1n) + 1n);
  }
  // A zero-valued expression must still call its continuation.
  assert.equal(compileExpression(programs[2])(() => 99n, () => 7n), 7n);
});
