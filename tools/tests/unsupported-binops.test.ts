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
  const source = project.createSourceFile("/ops.ts", text);
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

test("unsupported binary and compound operators fail extraction with operator name and source location (#30)", () => {
  const cases: { name: string; op: string; code: string; line: number }[] = [
    {
      name: "exponentiation **",
      op: "**",
      code: `export function square(x: number): number {\n  return x ** 2;\n}\n`,
      line: 2,
    },
    {
      name: "unsigned right shift >>>",
      op: ">>>",
      code: `export function ushr(x: number): number {\n  return x >>> 1;\n}\n`,
      line: 2,
    },
    {
      name: "compound exponentiation **=",
      op: "**=",
      code: `export function powAssign(x: number): number {\n  let y = x;\n  y **= 2;\n  return y;\n}\n`,
      line: 3,
    },
    {
      name: "compound unsigned right shift >>>=",
      op: ">>>=",
      code: `export function ushrAssign(x: number): number {\n  let y = x;\n  y >>>= 1;\n  return y;\n}\n`,
      line: 3,
    },
    {
      name: "bitwise xor ^",
      op: "^",
      code: `export function xor(x: number, y: number): number {\n  return x ^ y;\n}\n`,
      line: 2,
    },
    {
      name: "compound bitwise xor ^=",
      op: "^=",
      code: `export function xorAssign(x: number): number {\n  let y = x;\n  y ^= 1;\n  return y;\n}\n`,
      line: 3,
    },
  ];
  for (const c of cases) {
    assert.throws(
      () => extract(c.code),
      (err: unknown) => {
        assert.ok(err instanceof Error);
        assert.ok(err.message.includes(`Unsupported binary operator '${c.op}'`), err.message);
        assert.ok(err.message.includes(`/ops.ts:${c.line}:`), err.message);
        return true;
      },
      c.name,
    );
  }
});

test("lsc gen rejects **, **=, and >>> on both Dafny and Lean backends without writing artifacts (#30)", () => {
  const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
  const loader = createRequire(import.meta.url).resolve("tsx");
  const samples = [
    { op: "**", code: `export function square(x: number): number {\n  return x ** 2;\n}\n`, line: 2 },
    { op: ">>>", code: `export function ushr(x: number): number {\n  return x >>> 1;\n}\n`, line: 2 },
    { op: "**=", code: `export function powAssign(x: number): number {\n  let y = x;\n  y **= 2;\n  return y;\n}\n`, line: 3 },
  ];
  for (const backend of ["dafny", "lean"] as const) {
    for (const sample of samples) {
      const dir = mkdtempSync(join(tmpdir(), "lsc-binops-cli-"));
      try {
        writeFileSync(join(dir, "ops.ts"), sample.code);
        const result = spawnSync(
          process.execPath,
          ["--import", loader, cli, "gen", `--backend=${backend}`, "ops.ts"],
          { cwd: dir, encoding: "utf8", timeout: 30_000 },
        );
        assert.ifError(result.error);
        const out = result.stdout + result.stderr;
        assert.notEqual(result.status, 0, `${backend} unexpectedly succeeded on ${sample.op}: ${out}`);
        assert.ok(out.includes(`Unsupported binary operator '${sample.op}'`), out);
        assert.ok(out.includes(`ops.ts:${sample.line}:`), out);
        assert.deepEqual(readdirSync(dir), ["ops.ts"], `${backend} wrote artifacts on failed ${sample.op}`);
      } finally {
        rmSync(dir, { recursive: true, force: true });
      }
    }
  }
});

test("supported binary operators still generate and verify; Lean rejects Dafny-only bitwise ops cleanly", () => {
  const arithmetic = `export function ops(a: number, b: number): number {
  //@ requires b > 0
  //@ ensures \\result === a + b - a + a * 2 + (a % b)
  return a + b - a + a * 2 + (a % b);
}`;
  const dfy = generate(arithmetic, "dafny");
  assert.match(dfy, /function ops/);
  const dir = mkdtempSync(join(tmpdir(), "lsc-binops-ok-"));
  try {
    const dfyPath = join(dir, "ops.dfy");
    writeFileSync(dfyPath, dfy);
    const res = spawnSync("dafny", ["verify", "--verification-time-limit=15", dfyPath], {
      encoding: "utf8",
      timeout: 120_000,
    });
    assert.ifError(res.error);
    assert.equal(res.status, 0, res.stdout + res.stderr);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
  const lean = generate(arithmetic, "lean");
  assert.match(lean, /def ops/);

  // Bitwise shifts/masks lower in Dafny, and fail cleanly in Lean instead of emitting raw tokens.
  const bitwise = `export function shift(x: bigint): bigint {\n  return x << 2n;\n}\n`;
  assert.match(generate(bitwise, "dafny"), /\(x \* 4\)/);
  assert.throws(() => generate(bitwise, "lean"), /Unsupported Lean binary operator: <</);
});
