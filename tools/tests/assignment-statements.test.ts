import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";
import { peepholeModule } from "../src/peephole.ts";

function extract(text: string) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("/assignments.ts", text);
  const diagnostics = project.getPreEmitDiagnostics();
  assert.equal(diagnostics.length, 0, project.formatDiagnosticsWithColorAndContext(diagnostics));
  return extractModule(source);
}

function generate(text: string, backend: "dafny" | "lean" = "dafny") {
  const mod = narrowModule(resolveModule(extract(text)));
  const { typesFile, defFile } = (backend === "dafny" ? transformModuleDafny : transformModuleLean)(mod);
  const output = peepholeModule({ ...defFile, decls: [...typesFile?.decls ?? [], ...defFile.decls] }, backend);
  resetLeanModule();
  return backend === "dafny" ? emitDafnyFile(output) : emitLeanFile(output);
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-assignments-"));
  try {
    const path = join(dir, "assignments.dfy");
    writeFileSync(path, generate(text));
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=15", path],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

const parenthesized = `export function parenWholeAssign(p: number): number {
  //@ ensures \\result === 7
  let x = p;
  (x = 7);
  return x;
}
export function parenTarget(p: number): number {
  //@ ensures \\result === 7
  let x = p;
  (x) = 7;
  return x;
}`;

test("parenthesized assignment statements and targets preserve writes in both backends (#355, #356)", () => {
  const result = verify(parenthesized);
  assert.equal(result.status, 0, result.output);
  const lean = generate(parenthesized, "lean");
  assert.equal((lean.match(/x := 7/g) ?? []).length, 2, lean);
});

test("the previously provable false postcondition now fails verification (#356)", () => {
  const result = verify(parenthesized.replaceAll("\\result === 7", "p === 0 ==> \\result === 0"));
  assert.notEqual(result.status, 0, result.output);
  assert.equal((result.output.match(/Error: a postcondition could not be proved/g) ?? []).length, 2, result.output);
  assert.doesNotMatch(result.output, /resolution\/type errors|unresolved identifier|timed out/);
});

test("parentheses preserve scoped targets, array updates, loop updates, and havoc", () => {
  const result = verify(`export function scoped(p: number): number {
    //@ ensures \\result === p + 9
    let total = 0;
    { let p = 0; (((p) = 7)); ((p) += 2); ((p)++); (++(p)); ((p)--); (--(p)); total = p; }
    return p + total;
  }
  export function arrayShadow(a: number[]): number {
    //@ ensures \\result === a.length + 7
    let total = 0;
    { const a = [0]; (((a)[0]) = 7); total = a[0]; }
    return a.length + total;
  }
  export function loop(): number {
    //@ ensures \\result === 3
    let total = 0;
    for (let i = 0; i < 3; ((i)++)) {
      //@ invariant 0 <= i && i <= 3
      //@ invariant total === i
      //@ decreases 3 - i
      total++;
      continue;
    }
    return total;
  }
  export function abstracted(p: number): number {
    //@ ensures \\result === p
    { let p = 0;
      //@ havoc
      (((p) = Math.random()));
    }
    return p;
  }`);
  assert.equal(result.status, 0, result.output);
});

test("assignments and updates in value positions fail with a source location", () => {
  const bodies = [
    "const y = (x = 7);", "return x = 7;", "if ((x = 7) > 0) return x;",
    "while ((x = 7) > 0) return x;", "Math.abs(x = 7);", "const a = [x = 7];",
    "const a = { value: x = 7 };", "const y = x > 0 ? (x = 7) : 0;",
    "const y = x > 0 && (x = 7);", "x = (x = 7);", "const f = () => x = 7;",
    ...["=", "+=", "-=", "*=", "/=", "%=", "**=", "<<=", ">>=", ">>>=", "&=", "|=", "^=", "&&=", "||=", "??="]
      .map(op => `const y = (x ${op} 7);`),
    ...["++x", "x++", "--x", "x--"].map(expr => `const y = ${expr};`),
    ...["&&=", "||=", "??="].map(op => `x ${op} 7;`),
  ];
  for (const body of bodies) {
    assert.throws(() => extract(`export function f(x: number): number { ${body} return x; }`),
      /Unsupported (assignment|update) expression at \/assignments\.ts:1:\d+:.*Use a separate assignment statement/, body);
  }
  assert.throws(() => extract(`export function f(x: number): number {
  const y = (x = 7);
  return x;
}`), /Unsupported assignment expression at \/assignments\.ts:2:14: x = 7/);
});

test("both CLIs reject value assignments before writing verification artifacts", () => {
  const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
  const loader = createRequire(import.meta.url).resolve("tsx");
  for (const backend of ["dafny", "lean"]) {
    const dir = mkdtempSync(join(tmpdir(), "lsc-assignment-cli-"));
    try {
      writeFileSync(join(dir, "assignments.ts"), `export function f(p: number): number {
  //@ ensures p === 0 ==> \\result === 0
  let x = p;
  const y = (x = 7);
  return x;
}`);
      const result = spawnSync(process.execPath, ["--import", loader, cli, "gen", `--backend=${backend}`, "assignments.ts"],
        { cwd: dir, encoding: "utf8", timeout: 30_000 });
      assert.ifError(result.error);
      assert.notEqual(result.status, 0, result.stdout + result.stderr);
      assert.match(result.stdout + result.stderr, /Unsupported assignment expression at .*assignments\.ts:4:14: x = 7/);
      assert.deepEqual(readdirSync(dir), ["assignments.ts"]);
    } finally { rmSync(dir, { recursive: true, force: true }); }
  }
});
