import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { peepholeModule } from "../src/peephole.ts";

function extract(source: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("helper-signatures.ts", source);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return extractModule(file);
}

function generate(source: string, backend: "dafny" | "lean" = "dafny") {
  const typed = narrowModule(resolveModule(extract(source)));
  const { typesFile, defFile } = backend === "dafny"
    ? transformModuleDafny(typed) : transformModuleLean(typed);
  const mod = peepholeModule({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, backend);
  if (backend === "dafny") return emitDafnyFile(mod);
  resetLeanModule();
  return emitLeanFile(mod);
}

function verify(source: string, helpers: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-helper-signatures-"));
  try {
    const file = join(dir, "test.dfy");
    writeFileSync(file, helpers + generate(source));
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=10", file], {
      encoding: "utf8", timeout: 60_000,
    });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

for (const helper of [
  // try/finally is outside the fragment, so extracting these bodies would fail.
  "function positive(n: number): boolean { try { return n > 0; } finally {} }",
  "const positive = (n: number) => { try { return n > 0; } finally {} };",
]) {
  test(`Boolean helper types survive opt-in selection: ${helper.startsWith("const") ? "arrow" : "declaration"}`, () => {
    const source = helper + String.raw`
//@ verify
export function either(flag: boolean, n: number): boolean {
  //@ ensures \result === (flag || positive(n))
  return flag || positive(n);
}
//@ verify
export function both(flag: boolean, n: number): boolean {
  //@ ensures \result === (flag && positive(n))
  return flag && positive(n);
}
`;
    const raw = extract(source);
    assert.deepEqual(raw.functions.map(f => f.name), ["either", "both"]);
    assert.deepEqual(raw.externs, []);
    for (const backend of ["dafny", "lean"] as const) {
      const output = generate(source, backend);
      assert.doesNotMatch(output, /_logic|axiom|function positive|def positive/);
      assert.match(output, backend === "dafny" ? /flag \|\| positive\(n\)/ : /flag ∨ positive n/);
      assert.match(output, backend === "dafny" ? /flag && positive\(n\)/ : /flag ∧ positive n/);
    }
    const result = verify(source, "function positive(n: int): bool { n > 0 }\n");
    assert.equal(result.status, 0, result.output);
  });
}

const guarded = String.raw`
interface Message { ok: boolean }
function headOk(m: Message): boolean { try { return m.ok; } finally {} }
function unused(date: Date): RegExp { return new RegExp(date.toISOString()); }
//@ verify
export function safe(messages: Message[], index: number): boolean {
  //@ requires 0 <= index && index <= messages.length
  //@ ensures \result === (index === messages.length || headOk(messages[index]))
  return index === messages.length || headOk(messages[index]);
}
`;

test("typed helper calls preserve bounds guards and still require a backend definition", () => {
  const output = generate(guarded);
  assert.doesNotMatch(output, /_logic|unused|Date|RegExp|axiom/);
  const result = verify(guarded, "function headOk(m: Message): bool { m.ok }\n");
  assert.equal(result.status, 0, result.output);
  const missing = verify(guarded, "");
  assert.notEqual(missing.status, 0);
  assert.match(missing.output, /unresolved identifier: headOk/);
});

const operandValues = String.raw`
function value(n: number): number { try { return n; } finally {} }
//@ verify
export function fallback(n: number): number {
  //@ ensures \result === (value(n) || 5)
  return value(n) || 5;
}
//@ verify
export function selected(n: number): number {
  //@ ensures \result === (value(n) && 5)
  return value(n) && 5;
}
`;

test("operand-valued helpers keep JavaScript && and || semantics in bodies and contracts", () => {
  const helpers = "function value(n: int): int { n }\n";
  const result = verify(operandValues, helpers);
  assert.equal(result.status, 0, result.output);
  const falseContract = operandValues.replace(
    "//@ ensures \\result === (value(n) || 5)",
    "//@ requires n === 0\n  //@ ensures \\result === value(n)",
  );
  const rejected = verify(falseContract, helpers);
  assert.notEqual(rejected.status, 0);
  assert.match(rejected.output, /postcondition could not be proved/);
});

test("a local callback keeps its own signature when it shadows an excluded helper", () => {
  const source = String.raw`
function value(n: number): boolean { return n > 0; }
//@ verify
export function fallback(value: (n: number) => number, n: number): number {
  //@ ensures \result === (value(n) || 5)
  return value(n) || 5;
}
`;
  const result = verify(source, "");
  assert.equal(result.status, 0, result.output);
});
