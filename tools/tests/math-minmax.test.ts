import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import * as example from "../../examples/mathMinMax.ts";
import * as integerExample from "../../examples/mathMinMaxInt.ts";

function sourceModule(text: string) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.createSourceFile("minmax.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return narrowModule(resolveModule(extractModule(source)));
}

function emitSource(text: string, name = "minmax.ts") {
  const { typesFile, defFile } = transformModuleDafny(sourceModule(text));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, name);
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-minmax-"));
  try {
    const path = join(dir, "minmax.dfy");
    writeFileSync(path, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "10", path],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("positional min/max preserve bounds, membership, and the join of every operand type", () => {
  const functions: string[] = [];
  const expected = new Map<string, string>();
  for (const op of ["min", "max"]) for (const arity of [1, 2, 3, 4]) {
    const names = ["a", "b", "c", "d"].slice(0, arity);
    const variants = [names.map(() => "int"), names.map(() => "nat"), names.map(() => "real")];
    if (arity > 1) variants.push(
      names.map((_, i) => i === 0 ? "nat" : "int"),
      names.map((_, i) => i === 0 ? "int" : "nat"),
      names.map((_, i) => i === 0 ? "real" : "int"),
      names.map((_, i) => i === arity - 1 ? "real" : "int"),
    );
    for (const [variant, types] of variants.entries()) {
      const name = `${op}${arity}_${variant}`;
      const result = types.includes("real") ? "real" : types.every(t => t === "nat") ? "nat" : "int";
      expected.set(name, result);
      functions.push(`export function ${name}(${names.map(n => `${n}: number`).join(", ")}): number {
  ${names.map((n, i) => `//@ type ${n} ${types[i]}`).join("\n  ")}
  //@ type \\result ${result}
  //@ ensures ${names.map(n => `\\result ${op === "max" ? ">=" : "<="} ${n}`).join(" && ")}
  //@ ensures ${names.map(n => `\\result === ${n}`).join(" || ")}
  const value = Math.${op}(${names.join(", ")});
  return value;
}`);
    }
  }
  const source = functions.join("\n");
  const mod = sourceModule(source);
  for (const fn of mod.functions) {
    const value = fn.body[0];
    assert.ok(value.kind === "let", fn.name);
    assert.equal(value.init.ty.kind, expected.get(fn.name), fn.name);
  }
  const result = verify(emitSource(source));
  assert.equal(result.status, 0, result.output);

  // Dropping the last operand must invalidate the maximum's bound contract.
  const wrong = verify(emitSource(`export function missing(a: number, b: number, c: number, d: number): number {
    //@ ensures \\result >= a && \\result >= b && \\result >= c && \\result >= d
    return Math.max(a, b, c);
  }`));
  assert.notEqual(wrong.status, 0, wrong.output);
  assert.match(wrong.output, /could not be proved/);
});

test("real spreads promote scalar and array segments, including empty segments", () => {
  const functions: string[] = [];
  for (const op of ["min", "max"]) {
    for (const [index, args] of [
      "...reals", "0, ...reals", "...reals, 0", "...ints, ...reals", "...reals, ...ints",
      "n, r, ...ints, ...reals", "...[], ...reals, ...[]", "...[], ...ints, ...[], r",
      "...[n, r], ...ints", "...[n, -1], ...reals",
    ].entries()) {
      functions.push(`export function ${op}Spread${index}(ints: number[], reals: number[], n: number, r: number): number {
        //@ type n nat
        //@ type r real
        //@ type reals real[]
        //@ type \\result real
        //@ requires reals.length > 0
        const value = Math.${op}(${args});
        return Math.${op}(value, 0.5);
      }`);
    }
  }
  const source = functions.join("\n");
  for (const fn of sourceModule(source).functions) {
    const value = fn.body[0];
    assert.ok(value.kind === "let");
    assert.equal(value.init.ty.kind, "real", fn.name);
  }
  const output = emitSource(source);
  assert.match(output, /SeqIntToReal\(ints\)/);
  assert.match(output, /\[\(n as real\), r\]/);
  for (const helper of ["MaxOfSeqReal", "MinOfSeqReal", "SeqIntToReal"])
    assert.equal(output.match(new RegExp(`function ${helper}\\(`, "g"))?.length, 1, helper);
  const result = verify(output);
  assert.equal(result.status, 0, result.output);
});

test("only the combined spread sequence must be nonempty", () => {
  const good = verify(emitSource(`
    export function anchored(xs: number[]): number {
      //@ type xs real[]
      //@ type \\result real
      return Math.max(...[], ...xs, 0);
    }
    export function combined(xs: number[], ys: number[]): number {
      //@ type ys real[]
      //@ type \\result real
      //@ requires xs.length + ys.length > 0
      return Math.min(...xs, ...[], ...ys);
    }
  `));
  assert.equal(good.status, 0, good.output);
  for (const args of ["...xs", "...[]"]) {
    const bad = verify(emitSource(`export function empty(xs: number[]): number {
      //@ type xs real[]
      //@ type \\result ${args === "...[]" ? "int" : "real"}
      return Math.max(${args});
    }`));
    assert.notEqual(bad.status, 0, bad.output);
    assert.match(bad.output, /precondition.*could not be proved|precondition.*might not hold/);
  }
});

test("min/max diagnose zero arguments, bigint, and nonnumeric operands before lowering", () => {
  for (const op of ["min", "max"]) {
    assert.throws(() => sourceModule(`export function bad(): number { return Math.${op}(); }`),
      new RegExp(`Math\\.${op}.*zero arguments.*Infinity`));
    for (const args of ["n", "0, n", "0, 1, n", "...xs", "0, ...xs", "...[0, n]", "...[], ...xs"]) {
      assert.throws(() => sourceModule(`export function bad(n: bigint, xs: bigint[]): number {
        // @ts-expect-error JavaScript Math does not accept bigint.
        return Math.${op}(${args});
      }`), new RegExp(`Math\\.${op}.*bigint.*TypeError`), args);
    }
    assert.throws(() => sourceModule(`export function bad(s: string): number {
      // @ts-expect-error The numeric model does not coerce strings.
      return Math.${op}(s);
    }`), /requires numeric operands/);
  }
});

test("min/max evaluate positional and spread arguments once in source order", () => {
  for (const transform of [transformModuleDafny, transformModuleLean]) {
    const { defFile } = transform(sourceModule(`
      function mark(id: number): number { let value = id; value += 1; return value; }
      function list(id: number): number[] { let value = id; value += 1; return [value]; }
      export function positional(): number { return Math.max(mark(1), mark(2), mark(3)); }
      export function single(): number { return Math.min(mark(4)); }
      export function spread(): number { return Math.max(mark(5), ...list(6), mark(7), ...list(8)); }
    `));
    for (const [name, expected] of [["positional", [1, 2, 3]], ["single", [4]], ["spread", [5, 6, 7, 8]]] as const) {
      const decl = defFile.decls.find(d => d.kind === "method" && d.name === name);
      assert.ok(decl?.kind === "method", name);
      const args = decl.body.flatMap(s => {
        if (s.kind !== "let-bind" || s.value.kind !== "app" || !["mark", "list"].includes(s.value.fn)) return [];
        const arg = s.value.args[0];
        assert.ok(arg.kind === "num");
        return [arg.value];
      });
      assert.deepEqual(args, expected, name);
    }
  }
});

test("existing integer-spread output stays byte-identical", () => {
  const source = readFileSync(new URL("../../examples/maxSpread.ts", import.meta.url), "utf8");
  const generated = readFileSync(new URL("../../examples/maxSpread.dfy.gen", import.meta.url), "utf8");
  assert.equal(emitSource(source, "maxSpread.ts"), generated);
});

test("integer spreads preserve temporary bindings in generated methods", () => {
  const output = emitSource(`export function clippedRange(scores: number[]): number {
    let range = 0;
    const high = Math.max(...scores, 0);
    const low = Math.min(...scores, 0);
    range = high - low;
    return range;
  }`);
  // These generated lines are part of existing proofs' additions-only base,
  // even though the sequence helpers themselves are pure Dafny functions.
  assert.ok(output.includes(`  var i_t0 := MaxOfSeq((scores + [0]));
  var high := i_t0;
  var i_t1 := MinOfSeq((scores + [0]));
  var low := i_t1;`), output);
});

test("the examples execute as TypeScript and verify through the compiled CLI", () => {
  assert.equal(example.singleScore(-0.75), -0.75);
  assert.equal(example.highestOfThree(-3, -2, -1), -1);
  assert.equal(example.lowestOfFour(0.75, -0.25, 0.5, -1.5), -1.5);
  assert.equal(example.highestScore([0.25, -1.5, 2.75]), 2.75);
  assert.equal(example.lowestScore([0.25, -1.5, 2.75]), -1.5);
  assert.equal(example.highestScoreOrZero([]), 0);
  assert.equal(example.lowestScoreOrZero([]), 0);
  for (const [whole, fractional] of [[[], [-0.5]], [[-2], []], [[-2, 3], [3.5, -0.25]]])
    assert.equal(example.highestMixedScore(whole, fractional), Math.max(...whole, ...fractional));

  assert.equal(integerExample.singleValue(-7), -7);
  assert.equal(integerExample.highestInteger(-9, -3, -5), -3);
  assert.equal(integerExample.lowestNatural(5, 0, 2), 0);
  assert.equal(integerExample.lowestMixed(3, -4), -4);
  for (const xs of [[-9], [-3, -7, -2], [5, 0, -5]]) {
    assert.equal(integerExample.highestInArray(xs), Math.max(...xs));
    assert.equal(integerExample.lowestInArray(xs), Math.min(...xs));
    assert.equal(integerExample.arrayRange(xs), Math.max(...xs) - Math.min(...xs));
    assert.equal(integerExample.guardedHighest(xs), Math.max(...xs));
  }
  assert.equal(integerExample.lowestOrZero([]), 0);
  assert.equal(integerExample.lowestOrZero([-3, 2]), -3);
  assert.equal(integerExample.highestWithNatural([], 2), 2);
  assert.equal(integerExample.highestWithNatural([-3, 5], 2), 5);
  assert.equal(integerExample.guardedHighest([]), 0);
  for (const [ns, xs] of [[[], [-4]], [[2], []], [[0, 3], [-2, 5]]])
    assert.equal(integerExample.highestMixedArrays(ns, xs), Math.max(...ns, ...xs));

  const dir = mkdtempSync(join(tmpdir(), "lsc-minmax-example-"));
  try {
    for (const name of ["mathMinMax", "mathMinMaxInt"]) {
      for (const ext of ["ts", "dfy"])
        writeFileSync(join(dir, `${name}.${ext}`), readFileSync(new URL(`../../examples/${name}.${ext}`, import.meta.url)));
      const cli = fileURLToPath(new URL("../dist/lsc.js", import.meta.url));
      const result = spawnSync(process.execPath, [cli, "check", "--backend=dafny", "--time-limit=10", join(dir, `${name}.ts`)],
        { encoding: "utf8", timeout: 60_000, env: { ...process.env, LSC_RUN_LOG: "false" } });
      assert.ifError(result.error);
      assert.equal(result.status, 0, result.stdout + result.stderr);
      assert.match(result.stdout, /0 errors/);
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
