import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget, ts } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const cases = [
  ["parenWholeAssign", "let x = p; (x = 7); return x;", 7],
  ["parenthesizedTarget", "let x = p; (((x) = 7)); return x;", 7],
  ["assignInInit", "let x = p; const y = (x = 7); return x;", 7],
  ["assignedValue", "let x = p; const y = (x = 7); return x + y;", 14],
  ["chain", "let x = p, y = p; const z = (x = y = 7); return x + y + z;", 21],
  ["earlierRead", "let x = 1; return x + (x = 7);", 8],
  ["earlierResult", "let x = p; return (x = 7) + (x = 8) + x;", 23],
  ["callArguments", "let x = 1; const y = pair(x, (x = 7)); return y + 100 * x;", 717],
  ["methodArgument", "let x = p, y = p; x = checked(y = 7); return x + y;", 14],
  ["callBeforeAssignment", "let x = 1; return checked(x) + (x = 0);", 1],
  ["condition", "let x = p; if ((x = 7) > 0) return x; return 0;", 7],
  ["conditional", "let x = p; const y = p === 0 ? (x = 7) : (x = 8); return x + y;", 14],
  ["skipAnd", "let x = 1; const y = p !== 0 && (x = 7) > 0; return x;", 1],
  ["skipOr", "let x = 1; const y = p === 0 || (x = 7) > 0; return x;", 1],
  ["numberOr", "let x = 1; const y = x || (x = 7); return x + y;", 2],
  ["numberAnd", "let x = 1; const y = x && (x = 7); return x + y;", 14],
  ["arrayElements", "let x = 1; const a = [x, (x = 7), x]; return a[0] + a[1] + a[2];", 15],
  ["recordFields", "let x = 1; let r: Pair = { a: x, b: (x = 7) }; return r.a + r.b + x;", 15],
  ["fieldTarget", "let r: Pair = { a: 1, b: 2 }; const y = (r.a = 7); return y + r.a + r.b;", 16],
  ["fieldStatement", "let r: Pair = { a: 1, b: 2 }; let x = p; (r.a = (x = 7)); return r.a + r.b + x;", 16],
  ["indexTarget", "const a = [1, 2]; const y = (a[p] = (a[1] = 7)); return y + a[0] + a[1];", 21],
  ["computedTarget", "const a = [1, 2]; let i = p; const y = (a[i++] = 7); return 100 * i + 10 * a[0] + a[1] + y;", 179],
  ["indexMutation", "const a = [1]; return a[(a[0] = 7) - 7];", 7],
  ["assignedReceiver", "let a = [1]; return (a = [2])[(a[0] = 7) - 7];", 7],
  ["replacedReceiver", "let a = [1]; const x = a[(a = [7])[0] - 7]; return x + a[0];", 8],
  ["spreadSnapshot", "let r: Pair = { a: 1, b: 2 }; let s: Pair = { ...r, a: (r.b = 7) }; return s.a + s.b + r.b;", 16],
  ["arraySpreadSnapshot", "const a = [1]; const b = [...a, (a[0] = 7)]; return b[0] + b[1] + a[0];", 15],
  ["freshNames", "const _assigned0 = 1, _eval0 = 2, _branch0 = 3; let x = p; return (x = 7) + _assigned0 + _eval0 + _branch0;", 13],
  ["compound", "let x = 1; const y = (x += (x = 7)); return x + y;", 16],
  ["postfixUpdate", "let x = 1; const y = x++; return x + y;", 3],
  ["prefixUpdate", "let x = 1; const y = ++x; return x + y;", 4],
  ["logicalAssign", "let x = p; const y = (x ||= 7); return x + y;", 14],
  ["skipLogicalAssign", "let x = 1; const y = (x ||= (x = 7)); return x + y;", 2],
  ["nullishAssign", "let x: number | undefined = p === 0 ? undefined : p; const y = (x ??= 7); return y;", 7],
  ["skipNullish", "let x = p; const y = p === 0 ? 1 : undefined; const z = y ?? (x = 7); return x + z;", 1],
  ["takeNullish", "let x = p; const y = p === 0 ? undefined : 1; const z = y ?? (x = 7); return x + z;", 14],
  ["optionalTarget", "let x: number | undefined = undefined; const y = p === 0 ? (x = 7) : (x = 8); return y;", 7],
  ["skipOptionalCall", "let x = p; const a = p === 0 ? undefined : [7]; const y = a?.includes(x = 7); return x;", 0],
  ["takeOptionalCall", "let x = p; const a = p === 0 ? [7] : undefined; const y = a?.includes(x = 7); return x;", 7],
  ["parameter", "return (p = 7);", 7],
  ["objectCondition", "let a: number[] = []; if (a = [7]) return a[0]; return 0;", 7],
  ["loopCondition", `let x = p;
    while ((x = x + 1) < 3) {
      //@ invariant 0 <= x && x < 3
      //@ decreases 3 - x
      //@ done_with x === 3
      x = x;
    }
    return x;`, 3],
  ["loopContinue", `let x = p, sum = 0;
    while ((x += 1) < 3) {
      //@ invariant 0 <= x && x < 3
      //@ invariant sum === 0
      //@ decreases 3 - x
      //@ done_with x === 3 && sum === 0
      continue;
    }
    return 10 * x + sum;`, 30],
  ["loopFor", `let x = p;
    for (let i = 0; (x = i) < 3; (i = i + 1)) {
      //@ invariant 0 <= i && i <= 3
      //@ decreases 3 - i
      //@ done_with x === 3
      if (i === 1) continue;
    }
    return x;`, 3],
] as const;

const source = `type Pair = { a: number; b: number };
function pair(a: number, b: number): number {
  //@ ensures \\result === 10 * a + b
  return 10 * a + b;
}
function checked(n: number): number {
  //@ requires n > 0
  //@ ensures \\result === n
  let value = n; value += 0; return value;
}
export function tagged(c: string | number[]): number {
  //@ ensures Array.isArray(c) ==> \\result === 14
  //@ ensures !Array.isArray(c) ==> \\result === 16
  let x = 0;
  const y = Array.isArray(c) ? (x = 7) : (x = 8);
  return x + y;
}
` + cases.map(([name, body, expected]) => `export function ${name}(p: number): number {
  ${name.startsWith("loop") ? "//@ type p nat\n  //@ type x nat\n  //@ type i nat" : ""}
  //@ requires p === 0
  //@ ensures \\result === ${expected}
  ${body}
}`).join("\n");

function typed(text = source) {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("assignments.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

function dafny(text = source) {
  const { typesFile, defFile } = transformModuleDafny(typed(text));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-assignments-"));
  try {
    const proof = join(dir, "assignments.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit=10", proof],
      { encoding: "utf8", timeout: 60_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("assignment-expression results and side effects agree with JavaScript", () => {
  const exports: Record<string, (p: unknown) => number> = {};
  new Function("exports", ts.transpileModule(source, {
    compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ESNext },
  }).outputText)(exports);
  for (const [name, , expected] of cases) assert.equal(exports[name](0), expected, name);
  assert.equal(exports.tagged([1]), 14);
  assert.equal(exports.tagged("s"), 16);
  const output = dafny();
  const result = verify(output);
  assert.equal(result.status, 0, result.output + "\n" + output);
});

for (const name of ["parenWholeAssign", "assignInInit"]) {
  test(`Dafny rejects the original false postcondition for ${name}`, () => {
    const body = cases.find(c => c[0] === name)![1];
    const result = verify(dafny(`export function ${name}(p: number): number {
      //@ ensures p === 0 ==> \\result === 0
      ${body}
    }`));
    assert.notEqual(result.status, 0, result.output);
    assert.match(result.output, /postcondition could not be proved/);
  });
}

test("explicitly pure functions retain assignments in their by-method implementation", () => {
  const output = dafny(`//@ pure
    function assignValue(p: number): number {
      let x = p;
      return x = 7;
    }`);
  // Complete the generated functional-spec stub with a proof addition.
  const proof = output.replace("function assignValue_fun_spec(p: int): int\n",
    "function assignValue_fun_spec(p: int): int\n{ 7 }\n");
  assert.notEqual(proof, output);
  const result = verify(proof);
  assert.equal(result.status, 0, result.output + "\n" + proof);
});

test("Lean emits the same executable assignment effects", () => {
  resetLeanModule();
  const { defFile } = transformModuleLean(typed());
  const output = emitLeanFile(defFile);
  assert.match(output, /x := _assigned\d+/);
  assert.doesNotMatch(output, /_ := x = 7/);
});

test("Lean proves the assignment-expression contracts", {
  skip: !existsSync(new URL("../../.lake/build/lib/lean/LemmaScript.olean", import.meta.url)),
}, () => {
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(typed());
  const output = emitLeanFile({ ...defFile, imports: ["LemmaScript"],
    decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  const proofs = "prove_correct pair by\n  velvet_vcgen [pair] with (tactic => simp [Pure.pair])\n\n" +
    "prove_correct checked by\n  velvet_vcgen [checked] with finish\n\n" +
    "prove_correct tagged by\n  velvet_vcgen [tagged] with finish\n\n" +
    cases.map(([name]) =>
      `prove_correct ${name} by\n  velvet_vcgen [${name}] with ${name === "replacedReceiver" ? "(tactic => simp_all)" : "finish"}\n`).join("\n");
  const dir = mkdtempSync(join(tmpdir(), "lsc-assignments-lean-"));
  try {
    const file = join(dir, "Assignments.lean");
    writeFileSync(file, output + "\n" + proofs);
    const result = spawnSync("lake", ["env", "lean", file], {
      cwd: fileURLToPath(new URL("../../", import.meta.url)), encoding: "utf8", timeout: 60_000,
    });
    assert.ifError(result.error);
    assert.equal(result.status, 0, result.stdout + result.stderr + "\n" + output);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
