import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { autoHavocModule } from "../src/autohavoc.ts";
import { narrowModule } from "../src/narrow.ts";
import { emitFstarFile } from "../src/fstar-emit.ts";
import { checkFstarSource } from "../src/fstar-source.ts";
import { checkFstarProof, fstarFlags, fstarPaths, fstarVerify, fstarRegen, fstarCheckDiff } from "../src/fstar-commands.ts";

const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const loader = createRequire(import.meta.url).resolve("tsx");
const examples = fileURLToPath(new URL("../../examples/", import.meta.url));
const fstar = spawnSync(process.env.FSTAR_EXE || "fstar.exe", ["--version"], { encoding: "utf8", timeout: 10_000 });
const installed = !fstar.error && fstar.status === 0;
if (process.env.LSC_REQUIRE_FSTAR && !installed) throw new Error("F* integration tests require fstar.exe (or FSTAR_EXE)");
const realFstar = { skip: !installed, timeout: 60_000 };

function compile(source: string, module = "Test"): string {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: { strict: true, target: ScriptTarget.ESNext } });
  const file = project.createSourceFile("input.ts", source);
  const raw = extractModule(file);
  checkFstarSource(file, raw);
  return emitFstarFile(autoHavocModule(narrowModule(resolveModule(raw))), module);
}
function temporary(run: (dir: string) => void): void {
  const dir = mkdtempSync(join(tmpdir(), "lsc-fstar-test-"));
  try { run(dir); } finally { rmSync(dir, { recursive: true, force: true }); }
}
function verify(source: string): boolean {
  let ok = false;
  temporary(dir => {
    const file = join(dir, "Test.fst");
    writeFileSync(file, compile(source));
    writeFileSync(file + ".gen", readFileSync(file));
    ok = fstarVerify(file, 20);
  });
  return ok;
}
function runCli(dir: string, args: string[], env = process.env) {
  const result = spawnSync(process.execPath, ["--import", loader, cli, ...args], { cwd: dir, env, encoding: "utf8", timeout: 30_000 });
  assert.ifError(result.error);
  return result;
}

test("module names survive checkout relocation and distinguish duplicate stems", () => {
  assert.equal(fstarPaths("/one/src/a-b.ts", "/one").moduleName, fstarPaths("/two/src/a-b.ts", "/two").moduleName);
  assert.notEqual(fstarPaths("/one/src/a-b.ts", "/one").moduleName, fstarPaths("/one/src/a_b.ts", "/one").moduleName);
  assert.notEqual(fstarPaths("/one/x/foo.ts", "/one").moduleName, fstarPaths("/one/y/foo.ts", "/one").moduleName);
});

for (const file of ["fstarClosures.ts", "fstarComposition.ts", "fstarArrays.ts", "fstarIteration.ts"]) {
  test(`generated example verifies: ${file}`, realFstar, () => {
    assert.equal(verify(readFileSync(join(examples, file), "utf8")), true);
  });
}

test("local generic closures, shadowed names, zero arguments, booleans and indexing", realFstar, () => {
  assert.equal(verify(String.raw`
    export function identity<A>(x:A): A { return x; }
    export function closure<A>(x:A): () => A { return ():A => x; }
    export function test(ls_result:number, xs:number[]):number {
      //@ requires xs.length > 0
      //@ ensures \result === ls_result + xs[0]
      const id = (ls_result:number):number => identity(ls_result);
      const get = closure(id(ls_result));
      const positive = (x:number):boolean => x > 0;
      if (positive(get()) || !positive(get())) return get() + xs[0];
      return 0;
    }
  `), true);
});

test("generic map, filter, every, some and initialized fold accept pure callbacks", realFstar, () => {
  assert.equal(verify(`
    export function predicates(xs:number[]):boolean {
      const kept = xs.filter((x:number):boolean => x > 0);
      return kept.every((x:number):boolean => x > 0) || kept.some((x:number):boolean => x < 0);
    }
    export function fold(xs:number[]):number {
      return xs.map((x:number):number => x + 1).reduce((a:number, x:number):number => a + x, 0);
    }
  `), true);
});

for (const [label, code] of [
  ["false postcondition", String.raw`export function bad(x:number):number {
    //@ ensures \result > x
    return x;
  }`],
  ["false closure contract", String.raw`export function bad(n:number):(x:number)=>number {
    //@ ensures forall(x:int, \result(x) === x + n)
    return (x:number):number => x - n;
  }`],
  ["callback violates caller precondition", String.raw`
    export function twice(f:(x:number)=>number,x:number):number {
      //@ requires forall(y:int, f(y) >= y)
      //@ ensures \result >= x
      return f(f(x));
    }
    export function bad(x:number):number { return twice((y:number):number => y-1,x); }
  `],
  ["array bounds are obligations", `export function bad(xs:number[]):number { return xs[0]; }`],
  ["nontermination", `export function bad(x:number):number { return bad(x); }`],
] as const) {
  test(`verifier rejects ${label}`, realFstar, () => assert.equal(verify(code), false));
}

for (const [label, code, error] of [
  ["mutable closure", `export function bad():()=>number { let x=0; return ():number => ++x; }`, /mutation of captured variable/],
  ["module mutation", `const xs=[1]; xs[0]=2; export function bad():number { return xs[0]; }`, /module-level statement/],
  ["escaped array constant", `export const xs=[1]; export function bad():number { return xs[0]; }`, /scalar module constants/],
  ["callback mutation", `export function bad(xs:number[]):number[] { return xs.map((x:number):number => { xs[0]=x; return x; }); }`, /mutation of captured variable/],
  ["reference equality", `export function bad(xs:number[],ys:number[]):boolean { return xs===ys; }`, /reference equality/],
  ["function identity", `export function bad(f:()=>number,g:()=>number):boolean { return f===g; }`, /reference equality/],
  ["index callback", `export function bad(xs:number[]):number[] { return xs.map((x:number,i:number):number => x+i); }`, /1-parameter callback/],
  ["thisArg", `export function bad(xs:number[]):number[] { return xs.map((x:number):number => x, 0); }`, /thisArg/],
  ["reduce without initial", `export function bad(xs:number[]):number { return xs.reduce((x:number,y:number):number=>x+y); }`, /initial values/],
  ["destructured parameters", `export function bad([x,y]:[number,number]):number { return x+y; }`, /destructured parameters/],
  ["default parameter", `export function bad(x:number=1):number { return x; }`, /defaulted and rest/],
  ["rest parameter", `export function bad(...xs:number[]):number { return xs.length; }`, /defaulted and rest/],
  ["async", `export async function bad():Promise<number> { return await Promise.resolve(1); }`, /async functions|await/i],
  ["constraint", `export function bad<A extends number>(x:A):number { return x; }`, /constrained/],
  ["type alias shadowing", `type A=number; export function bad<A>(x:A):A { return x; }`, /shadowing type aliases/],
  ["nested contract", `export function bad():(x:number)=>number { return (x:number):number => {\n //@ ensures false\n return x; }; }`, /nested lambda contracts/],
  ["unsafe literal", `export function bad():number { return 9007199254740993; }`, /safe integers/],
  ["skip", `export function bad(xs:number[]):number {\n //@ skip\n xs.push(1);\n return xs.length; }`, /statement-level skip/],
  ["contract", `export function bad(x:number):number {\n //@ contract x > 0\n return x; }`, /contract annotations/],
] as const) {
  test(`generation rejects ${label}`, () => assert.throws(() => compile(code), error));
}


for (const [label, code] of [
  ["loop mutation and early returns", String.raw`export function size(xs:number[]):number {
    //@ ensures \result === xs.length
    let n=0;
    while (n<xs.length) {
      //@ invariant 0 <= n && n <= xs.length
      n++;
    }
    return n;
  }`],
  ["local arrays and lexical scope", String.raw`export function size(b:boolean):number {
    //@ ensures \result === 2
    let xs:number[]=[];
    { const x=1; xs.push(x); }
    if(b) { const x=2; xs.push(x); } else { xs.push(3); }
    return xs.length;
  }`],
  ["optional arguments", String.raw`export function f(x?:number):number { return x ?? 0; }
    export function test():number { //@ ensures \result === 0
      return f();
    }`],

  ["deterministic extern", String.raw`//@ extern
    export function external(x:number):number { return x; }
    export function test(x:number):boolean {
      //@ ensures \result
      return external(x)===external(x);
    }`],
  ["explicit source havoc and assume", String.raw`export function sample():number {
    //@ ensures \result >= 0
    //@ havoc
    const x:number=0;
    //@ assume x >= 0
    return x;
  }`],
] as const) {
  test(`expanded model verifies ${label}`, realFstar, () => assert.equal(verify(code), true));
}
for (const [label, code] of [
  ["incorrect loop invariant", String.raw`export function bad(n:number):number {
    //@ requires n > 0
    let i=0;
    while(i<n) {
      //@ invariant i === 0
      i++;
    }
    return i;
  }`],
  ["independent impure calls", String.raw`//@ extern
    //@ impure
    export function roll():number { return 0; }
    export function bad():boolean {
      //@ ensures \result
      return roll()===roll();
    }`],
  ["independent havoc loop iterations", String.raw`export function bad():number {
    //@ ensures \result === 0
    let total=0;
    for(let i=0;i<2;i++) {
      //@ invariant 0 <= i && i <= 2
      //@ havoc
      const x:number=0;
      total += i===0 ? x : -x;
    }
    return total;
  }`],
] as const) {
  test(`expanded model rejects ${label}`, realFstar, () => assert.equal(verify(code), false));
}

test("generated trust cannot be enlarged by proof additions", () => {
  const generated = "module Test\nassume val external : int -> GTot int\n";
  checkFstarProof(generated + "let fact () : Lemma (1==1) = ()\n", generated);
  assert.throws(() => checkFstarProof(generated + "let bad () = assume False\n", generated));
});

test("resource flags are accepted while verification bypass flags are rejected", () => {
  assert.deepEqual(fstarFlags("--fuel 3 --z3rlimit=30"), ["--fuel", "3", "--z3rlimit", "30"]);
  for (const flags of ["--lax", "--admit_smt_queries true", "--verify_module Other", "--fuel", "--fuel -1", "--include .", "--codegen OCaml"]) {
    assert.throws(() => fstarFlags(flags));
  }
});
test("proof admission/options are rejected but mentions in comments and strings are fine", () => {
  checkFstarProof('module Test\n// admit\n(* assume (* nested *) false *)\nlet label = "#push-options admit"\n');
  for (const addition of ['#push-options "--lax"', "assume val impossible : False", "let nope = admit ()", "let nope = FStar.Tactics.Builtins.tadmit ()", "[@@admit] let x=1", "let nope = FStar.Tactics.Builtins.set_options \"--lax\""]) {
    assert.throws(() => checkFstarProof("module Test\n" + addition));
  }
});
test("opaque SMT definitions still require a valid proof", realFstar, () => temporary(dir => {
  const file = join(dir, "Test.fst");
  const source = 'module Test\n[@@"opaque_to_smt"]\nlet bad () : Lemma False = ()\n';
  checkFstarProof(source);
  writeFileSync(file, source);
  assert.equal(fstarVerify(file, 20), false);
}));
test(".fsti companions and missing verifiers fail", () => temporary(dir => {
  const file = join(dir, "Test.fst");
  writeFileSync(file, "module Test\nlet x=1\n");
  writeFileSync(file + "i", "module Test\nval x:int\n");
  assert.equal(fstarVerify(file, 5), false);
  rmSync(file + "i");
  const before = process.env.FSTAR_EXE;
  try { process.env.FSTAR_EXE = join(dir, "missing-fstar"); assert.equal(fstarVerify(file, 5), false); }
  finally { if (before === undefined) delete process.env.FSTAR_EXE; else process.env.FSTAR_EXE = before; }
}));
test("nonzero exit and a process deadline cannot report success", { skip: process.platform === "win32" }, () => temporary(dir => {
  const file = join(dir, "Test.fst"), exe = join(dir, "fake-fstar");
  writeFileSync(file, "module Test\nlet x=1\n");
  const before = process.env.FSTAR_EXE;
  try {
    process.env.FSTAR_EXE = exe;
    writeFileSync(exe, '#!/bin/sh\nprintf "Verified module: Test\\n"\nexit 1\n', { mode: 0o755 });
    assert.equal(fstarVerify(file, 1), false);
    writeFileSync(exe, '#!/bin/sh\nexec sleep 30\n', { mode: 0o755 });
    assert.equal(fstarVerify(file, 1), false);
  } finally { if (before === undefined) delete process.env.FSTAR_EXE; else process.env.FSTAR_EXE = before; }
}));
test("regen preserves checked proof additions and rejects generated edits", realFstar, () => temporary(dir => {
  const f = fstarPaths(join(dir, "a.ts"), dir);
  const source = (n:number) => `export function add(x:number):number { return x+${n}; }
    export function unchanged(x:number):number { const y=x+1; return y+1; }`;
  fstarRegen(f.gen, f.proof, f.base, compile(source(1), f.moduleName), 20);
  const addition = "\nlet retained_proof () : Lemma (1 + 1 == 2) = ()\n";
  writeFileSync(f.proof, readFileSync(f.proof, "utf8") + addition);
  fstarRegen(f.gen, f.proof, f.base, compile(source(2), f.moduleName), 20);
  assert.equal(readFileSync(f.proof, "utf8"), readFileSync(f.gen, "utf8") + addition);
  assert.equal(existsSync(f.base), false);
  writeFileSync(f.proof, readFileSync(f.proof, "utf8").replace("v_x + (2)", "v_x - (2)"));
  assert.equal(fstarCheckDiff(f.gen, f.proof), false);
}));
test("CLI honors backend selection and fails before writing on unsupported input", () => temporary(dir => {
  const file = join(dir, "a.ts");
  writeFileSync(file, "//@ backend fstar\nexport function f(x:number):number { return x; }\n");
  for (const backend of ["dafny", "lean"]) {
    const result = runCli(dir, ["check", `--backend=${backend}`, file]);
    assert.equal(result.status, 0, result.stderr);
    assert.match(result.stdout, /Skipped/);
  }
  assert.deepEqual(readdirSync(dir), ["a.ts"]);
  writeFileSync(file, "export function f(x:number=1):number { return x; }\n");
  assert.notEqual(runCli(dir, ["gen", "--backend=fstar", file]).status, 0);
  assert.deepEqual(readdirSync(dir), ["a.ts"]);
  writeFileSync(file, "export function f(x:number):number { return x; }\n");
  const result = runCli(dir, ["gen-check", "--backend=fstar", file]);
  assert.equal(result.status, 0, result.stderr);
  const files = fstarPaths(file, dir);
  assert.ok(existsSync(files.proof));
  assert.ok(existsSync(files.gen));
}));

test("comma-separated backend selectors permit each named backend", () => temporary(dir => {
  const file = join(dir, "a.ts");
  writeFileSync(file, "//@ backend dafny,fstar\nexport function f(x:number):number { return x; }\n");
  const lean = runCli(dir, ["gen", "--backend=lean", file]);
  assert.equal(lean.status, 0, lean.stderr);
  assert.match(lean.stdout, /Skipped/);
  for (const backend of ["dafny", "fstar"]) {
    const result = runCli(dir, ["gen", `--backend=${backend}`, file]);
    assert.equal(result.status, 0, result.stderr);
    assert.doesNotMatch(result.stdout, /Skipped/);
  }
}));
