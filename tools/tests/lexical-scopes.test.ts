import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
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
import { renameSpecVariables } from "../src/specparser.ts";
import { isUserName } from "../src/names.ts";
import * as runtime from "../fixtures/lexical-scopes.ts";
import * as narrowingRuntime from "../fixtures/narrowing-shadowing.ts";

const fixture = readFileSync(new URL("../fixtures/lexical-scopes.ts", import.meta.url), "utf8");
const narrowingFixture = readFileSync(new URL("../fixtures/narrowing-shadowing.ts", import.meta.url), "utf8");

function source(text: string) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("/scopes.ts", text);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return file;
}

function generate(text: string, backend: "dafny" | "lean" = "dafny") {
  const mod = narrowModule(resolveModule(extractModule(source(text))));
  const { typesFile, defFile } = (backend === "dafny" ? transformModuleDafny : transformModuleLean)(mod);
  const output = peepholeModule({ ...defFile, decls: [...typesFile?.decls ?? [], ...defFile.decls] }, backend);
  resetLeanModule();
  return backend === "dafny" ? emitDafnyFile(output) : emitLeanFile(output);
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-scopes-"));
  try {
    const path = join(dir, "scopes.dfy");
    writeFileSync(path, text);
    // As `lsc check` does: load the standard library only for text that uses it.
    const stdlib = text.includes("Std.") ? ["--standard-libraries"] : [];
    const result = spawnSync("dafny", ["verify", ...stdlib, "--verification-time-limit=15", path],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

test("block, branch, lambda, ghost, and loop scopes agree with JavaScript", () => {
  assert.equal(runtime.bareBlock(3), 3);
  assert.equal(runtime.branchLocal(3, true), 3);
  assert.equal(runtime.branchLocal(3, false), 3);
  assert.equal(runtime.lambdaBranch(3, true), 3);
  assert.equal(runtime.narrowedBlock(7), 7);
  assert.equal(runtime.narrowedBranch(7, true), 7);
  assert.equal(runtime.lambdaSwitch(3, "a"), 3);
  assert.equal(runtime.siblingBlocks(3), 10);
  assert.equal(runtime.globalShadow(), 13);
  assert.equal(runtime.destructuredShadow(3), 3);
  assert.equal(runtime.ghostScopes(3), 3);
  assert.equal(runtime.initializedClosure(3), 11);
  assert.equal(runtime.counterScope(3), 5);
  const result = verify(generate(fixture));
  assert.equal(result.status, 0, result.output);
});

test("false contracts for #361 and #362 fail as postconditions, including narrowed and lambda bodies", () => {
  const selected = fixture.slice(0, fixture.indexOf("//@ ensures \\result === p + 7"));
  const falseSpecs = selected.replaceAll("\\result === p", "\\result === 5");
  const result = verify(generate(falseSpecs));
  assert.notEqual(result.status, 0, result.output);
  assert.equal((result.output.match(/Error: a postcondition could not be proved/g) ?? []).length, 6, result.output);
  assert.doesNotMatch(result.output, /resolution\/type errors|unresolved identifier|timed out/);
});

test("method bodies reject the false bare-block contract too", () => {
  const text = `export function f(p: number): number {
    //@ ensures \\result === 5
    let total = 0;
    { let p = 5; total += p; }
    return p;
  }`;
  const result = verify(generate(text));
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /a postcondition could not be proved/);
});

test("forward local captures (#360) are rejected using declaration identity", () => {
  for (const declarations of [
    "const read = (): number => p; const p = 5;",
    "const read = (): number => p; let p = 5;",
    "const read = (): number => p; const { p } = { p: 5 };",
    "const read = (): number => p; const [p] = [5];",
    "const read = (): number => p, p = 5;",
    "const read = (): number => [0].map(x => p)[0]; const p = 5;",
    "const read = (): number => ({ p }).p; const p = 5;",
  ]) {
    const text = `export function f(p: number, flag: boolean): number {
      if (flag) { ${declarations} return read(); } return p;
    }`;
    assert.throws(() => extractModule(source(text)), /Unsupported forward capture 'p'.*local declared later/);
  }
  const narrowed = `export function f(p: number | undefined): number {
    if (p !== undefined) { const read = (): number => p; const p = 5; return read(); }
    return 0;
  }`;
  assert.throws(() => extractModule(source(narrowed)), /Unsupported forward capture 'p'/);
});

test("closure diagnostics distinguish fields, inner locals, and initialized captures", () => {
  const text = `type Pair = { p: number };
    export function f(p: number, pair: Pair): number {
      //@ ensures \\result === p + pair.p + 5
      const readField = (): number => pair.p;
      const readInner = (): number => { const p = 5; return p; };
      const readOuter = (): number => p;
      return readOuter() + readField() + readInner();
    }`;
  const result = verify(generate(text));
  assert.equal(result.status, 0, result.output);
});

test("annotation renaming preserves strings, fields, record keys, and bound variables", () => {
  const text = `p === s . p && "p" === 'p' && { p: p }.p === p
    && forall(p: int, p === s.p) && exists(q: int, q === p) && p === 5`;
  const renamed = renameSpecVariables(text, name => name === "p" ? "p_2" : name);
  assert.equal(renamed, `p_2 === s . p && "p" === 'p' && { p: p_2 }.p === p_2
    && forall(p: int, p === s.p) && exists(q: int, q === p_2) && p_2 === 5`);
});

test("renamed bindings avoid source and spec binders and remain reserved for later passes", () => {
  const file = source(`export function f(p: number, p_2: number): number {
    let total = 0;
    { const p = 5;
      const xs = [p];
      //@ assert forall(p_3: int, 0 <= p_3 && p_3 < xs.length ==> xs[p_3] === p)
      total += p;
    }
    return p;
  }`);
  const before = file.getFullText();
  const first = extractModule(file);
  const local = first.functions[0].body[1];
  assert.equal(local.kind, "let");
  assert.ok(local.kind === "let" && local.name === "p_4");
  assert.ok(isUserName("p_4"));
  assert.equal(file.getFullText(), before);
  assert.deepEqual(extractModule(file), first, "repeated extraction must be deterministic");
  const result = verify(generate(before));
  assert.equal(result.status, 0, result.output);
});

test("both backends retain distinct inner and outer bindings", () => {
  const text = `export function f(p: number, flag: boolean): number {
    if (flag) { const p = 5; } return p;
  }`;
  assert.match(generate(text), /var p_2 := 5;\s+p\b/);
  assert.match(generate(text, "lean"), /let p_2 := 5\s+p\b/);
});

test("narrowing respects loop locals, field roots, lambda parameters, and quantified variables", () => {
  assert.equal(narrowingRuntime.whileShadow(3), 5);
  assert.equal(narrowingRuntime.forOfShadow(3), 5);
  assert.equal(narrowingRuntime.fieldShadow({ value: 3 }), 8);
  assert.equal(narrowingRuntime.lambdaScopes(3), 13);
  assert.equal(narrowingRuntime.lambdaTernary(3), 8);
  assert.equal(narrowingRuntime.quantifierScope(3), 3);
  assert.equal(narrowingRuntime.variantShadow({ kind: "a", n: 3 }), 8);
  assert.equal(narrowingRuntime.switchShadow({ kind: "a", n: 3 }), 8);
  const result = verify(generate(narrowingFixture));
  assert.equal(result.status, 0, result.output);
  const lean = generate(narrowingFixture, "lean");
  // Each shadowing binding has its own name, so no later pass can confuse them.
  assert.match(lean, /total := total \+ p_2\b/);
  assert.match(lean, /total := total \+ box_2\.value\b/);
  assert.match(lean, /fun p_2 => p_2\b/);
  assert.match(lean, /∃ p' : Int, 0 ≤ p' ∧ p' < xs\.size/);
});

test("narrowing cannot prove the outer value was read through a shadowing loop local", () => {
  const correct = source(narrowingFixture).getFunctionOrThrow("whileShadow").getFullText();
  const falseContract = correct.replace("\\result === 5", "\\result === 3");
  // Before the fix, replacing the invariant too made this false proof succeed.
  const reported = falseContract.replace("total === i * 5", "total === i * 3")
    .replace("function whileShadow", "function reportedFalseProof");
  const reportedResult = verify(generate(reported));
  assert.notEqual(reportedResult.status, 0, reportedResult.output);
  assert.match(reportedResult.output, /invariant.*could not be proved/);
  assert.doesNotMatch(reportedResult.output, /resolution\/type errors|unresolved identifier|timed out/);
  const result = verify(generate(falseContract));
  assert.notEqual(result.status, 0, result.output);
  assert.match(result.output, /a postcondition could not be proved/);
  assert.doesNotMatch(result.output, /resolution\/type errors|unresolved identifier|timed out/);
});

for (const name of ["variantShadow", "switchShadow"]) {
  test(`variant narrowing cannot read a shadowing local as the scrutinee: ${name}`, () => {
    const file = source(narrowingFixture);
    const helpers = ["Shape", "Plain"].map(t => file.getTypeAliasOrThrow(t).getFullText()).join("") +
      file.getFunctionOrThrow("plain").getFullText();
    const falseContract = helpers + file.getFunctionOrThrow(name).getFullText()
      .replace("\\result === 8", "\\result === 6").replace("total === i * 5", "total === i * 3");
    const result = verify(generate(falseContract));
    assert.notEqual(result.status, 0, result.output);
    assert.match(result.output, /invariant.*could not be proved/);
    assert.doesNotMatch(result.output, /resolution\/type errors|unresolved identifier|timed out/);
  });
}

const loopAnnotations = `export function narrowedLoopAnnotations(p: number[] | undefined): number {
  //@ type i nat
  //@ ensures p !== undefined ==> \\result === p.length
  if (p !== undefined) {
    let i = 0;
    while (i < p.length) {
      //@ invariant i <= p.length
      //@ decreases p.length - i
      //@ done_with i === p.length
      i++;
    }
    return i;
  }
  return 0;
}`;

test("narrowing reaches a loop's termination measure", () => {
  const result = verify(generate(loopAnnotations));
  assert.equal(result.status, 0, result.output);
});

test("Lean loop annotations use the narrowed value", () => {
  const lean = generate(loopAnnotations, "lean");
  assert.match(lean, /decreasing _p_val\.size - i/);
  assert.match(lean, /done_with \(i = _p_val\.size : Prop\)/);
});
