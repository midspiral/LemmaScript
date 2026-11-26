import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract";
import { resolveModule } from "../src/resolve";
import { narrowModule } from "../src/narrow";
import { transformModule, transformModuleDafny } from "../src/transform";
import { emitDafnyFile } from "../src/dafny-emit";
import { emitLeanFile } from "../src/lean-emit";
import type { TExpr, TStmt } from "../src/typedir";

const source = `
export function countTwice(xs: number[]): number {
  //@ ensures \\result === 2 * xs.length
  let n = 0;
  for (const x of xs) {
    //@ invariant n === _x_idx
    n = n + 1;
  }
  let m = 0;
  for (const x of xs) {
    //@ invariant n === xs.length && m === _x_idx2
    m = m + 1;
  }
  return n + m;
}

export function halfTwice(xs: number[]): number {
  //@ ensures \\result === xs.length
  let n = 0;
  for (const x of xs) {
    //@ invariant n * 1.5 === _x_idx * 1.5
    n = n + 1;
  }
  let m = 0;
  for (const x of xs) {
    //@ invariant m * 1.5 === _x_idx2 * 1.5
    m = m + 1;
  }
  return m;
}

export function branchLoops(xs: number[], ys: number[], flag: boolean): number {
  //@ ensures \\result === (flag ? xs.length : ys.length)
  let total = 0;
  if (flag) {
    for (const x of xs) {
      //@ invariant total === _x_idx
      total = total + 1;
    }
  } else {
    for (const x of ys) {
      //@ invariant total === _x_idx2
      total = total + 1;
    }
  }
  return total;
}

export function mapEntriesTwice(m: Map<string, number>): number {
  let n = 0;
  for (const [k, v] of m) {
    //@ invariant n === _k_idx
    n = n + 1;
  }
  let p = 0;
  for (const [k, v] of m) {
    //@ invariant p === _k_idx2
    p = p + 1;
  }
  return n + p;
}
`;

function resolveSource(code: string) {
  const project = new Project({
    compilerOptions: {
      strict: true,
      target: ScriptTarget.ESNext,
      lib: ["lib.esnext.d.ts"],
      types: [],
      skipLibCheck: true,
    },
  });
  const file = project.createSourceFile("loops.ts", code);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "test input must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

function collectVars(expr: TExpr, out: Map<string, TExpr["ty"]> = new Map()): Map<string, TExpr["ty"]> {
  switch (expr.kind) {
    case "var":
      out.set(expr.name, expr.ty);
      break;
    case "binop":
      collectVars(expr.left, out);
      collectVars(expr.right, out);
      break;
    case "unop":
      collectVars(expr.expr, out);
      break;
    case "call":
      collectVars(expr.fn, out);
      for (const a of expr.args) collectVars(a, out);
      break;
    case "index":
      collectVars(expr.obj, out);
      collectVars(expr.idx, out);
      break;
    case "field":
      collectVars(expr.obj, out);
      break;
    case "conditional":
      collectVars(expr.cond, out);
      collectVars(expr.then, out);
      collectVars(expr.else, out);
      break;
    case "forall":
    case "exists":
      collectVars(expr.body, out);
      break;
  }
  return out;
}

function emitDafny(code: string) {
  const { typesFile, defFile } = transformModuleDafny(resolveSource(code));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "loops.ts");
}

function emitLean(code: string) {
  const { defFile } = transformModule(resolveSource(code));
  return emitLeanFile(defFile, "loops.ts");
}

function verifyDafny(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-loop-counters-"));
  try {
    const proof = join(dir, "loops.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "30", proof], {
      encoding: "utf8",
      timeout: 180_000,
    });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("resolve records disambiguated counter names per function and types them as nat", () => {
  const mod = resolveSource(source);

  const countTwice = mod.functions.find(f => f.name === "countTwice")!;
  const countLoops = countTwice.body.filter((s): s is TStmt & { kind: "forof" } => s.kind === "forof");
  assert.deepEqual(countLoops.map(l => l.idx), ["_x_idx", "_x_idx2"]);
  assert.equal(collectVars(countLoops[0].invariants[0]).get("_x_idx")?.kind, "nat");
  const countSecondVars = new Map<string, TExpr["ty"]>();
  for (const inv of countLoops[1].invariants) collectVars(inv, countSecondVars);
  assert.equal(countSecondVars.get("_x_idx2")?.kind, "nat");

  // Counter numbering resets in each function.
  const halfTwice = mod.functions.find(f => f.name === "halfTwice")!;
  const halfLoops = halfTwice.body.filter((s): s is TStmt & { kind: "forof" } => s.kind === "forof");
  assert.deepEqual(halfLoops.map(l => l.idx), ["_x_idx", "_x_idx2"]);
  assert.equal(collectVars(halfLoops[1].invariants[0]).get("_x_idx2")?.kind, "nat");

  // Sibling branches in one function number their loops in source order.
  const branchFn = mod.functions.find(f => f.name === "branchLoops")!;
  const ifStmt = branchFn.body.find((s): s is TStmt & { kind: "if" } => s.kind === "if")!;
  const thenLoop = ifStmt.then.find((s): s is TStmt & { kind: "forof" } => s.kind === "forof")!;
  const elseLoop = ifStmt.else.find((s): s is TStmt & { kind: "forof" } => s.kind === "forof")!;
  assert.equal(thenLoop.idx, "_x_idx");
  assert.equal(elseLoop.idx, "_x_idx2");
  assert.equal(collectVars(thenLoop.invariants[0]).get("_x_idx")?.kind, "nat");
  assert.equal(collectVars(elseLoop.invariants[0]).get("_x_idx2")?.kind, "nat");

  // Destructured map loops number by head name.
  const mapFn = mod.functions.find(f => f.name === "mapEntriesTwice")!;
  const mapLoops = mapFn.body.filter((s): s is TStmt & { kind: "forof" } => s.kind === "forof");
  assert.deepEqual(mapLoops.map(l => l.idx), ["_k_idx", "_k_idx2"]);
  assert.equal(collectVars(mapLoops[1].invariants[0]).get("_k_idx2")?.kind, "nat");
});

test("Dafny verifies real arithmetic and integer specs referencing _x_idx2", () => {
  const dafny = emitDafny(source);
  assert.match(dafny, /\(\s*i_x_idx2\s+as\s+real\s*\)/, `expected _x_idx2 coerced to real:\n${dafny}`);
  const result = verifyDafny(dafny);
  assert.equal(result.status, 0, `Dafny verification failed:\n${result.output}\n---\n${dafny}`);
});

test("Lean emitter reuses the resolved counter names for repeated for-of loops", () => {
  const lean = emitLean(`
export function countTwice(xs: number[]): number {
  let n = 0;
  for (const x of xs) {
    //@ invariant n === _x_idx
    n = n + 1;
  }
  let m = 0;
  for (const x of xs) {
    //@ invariant n === xs.length && m === _x_idx2
    m = m + 1;
  }
  return n + m;
}
`);
  assert.match(lean, /for _x_idx in/);
  assert.match(lean, /for _x_idx2 in/);
});
