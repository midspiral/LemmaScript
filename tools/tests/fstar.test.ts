import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { runInNewContext } from "node:vm";
import { Project, ScriptTarget, ts } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { autoHavocModule } from "../src/autohavoc.ts";
import { narrowModule } from "../src/narrow.ts";
import { DEFAULT_OPTIONS } from "../src/config.ts";
import { emitFstarFile } from "../src/fstar-emit.ts";
import { checkFstarSource } from "../src/fstar-source.ts";
import { checkFstarProof, fstarFlags, fstarPaths, migrateFstarArtifacts, fstarVerify, fstarRegen, fstarCheckDiff } from "../src/fstar-commands.ts";

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
  const raw = extractModule(file, { ...DEFAULT_OPTIONS, "string-semantics": "javascript-utf16" });
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
  assert.equal(fstarPaths("/one/src/a-b.ts", "/one").proof, "/one/src/a-b.fst");
  assert.equal(fstarPaths("/one/src/a_b.ts", "/one").proof, "/one/src/a_b.fst");
});

for (const layout of ["module", "directory"] as const) {
  test(`artifact migration from ${layout} layout preserves proofs and recovery state`, () => temporary(dir => {
    const source = join(dir, "a-b.ts");
    const files = fstarPaths(source, dir);
    const legacy = layout === "module" ? join(dir, `${files.moduleName}.fst`) : join(dir, "fstar", "a-b.fst");
    mkdirSync(join(dir, "fstar"));
    const artifacts = new Map([
      ["", "working proof"], [".gen", "generated baseline"], [".base", "merge anchor"],
      [".merged", "unresolved conflict"], ["i", "interface that must still be rejected"],
    ]);
    for (const [suffix, text] of artifacts) writeFileSync(legacy + suffix, text);
    migrateFstarArtifacts(source, files);
    for (const [suffix, text] of artifacts) {
      assert.equal(existsSync(legacy + suffix), false);
      assert.equal(readFileSync(files.proof + suffix, "utf8"), text);
    }
    migrateFstarArtifacts(source, files); // already migrated
    for (const [suffix, text] of artifacts) assert.equal(readFileSync(files.proof + suffix, "utf8"), text);
  }));

  test(`artifact migration from ${layout} layout refuses to mix proof state`, () => {
    for (const suffix of ["", ".gen", ".base", ".merged", "i"]) temporary(dir => {
      const source = join(dir, "a.ts");
      const files = fstarPaths(source, dir);
      const legacy = layout === "module" ? join(dir, `${files.moduleName}.fst`) : join(dir, "fstar", "a.fst");
      mkdirSync(join(dir, "fstar"));
      writeFileSync(legacy, "old proof");
      writeFileSync(legacy + ".gen", "old baseline");
      writeFileSync(files.proof + suffix, "new proof state");
      assert.throws(() => migrateFstarArtifacts(source, files), /conflicting proof artifact sets exist/);
      assert.equal(readFileSync(legacy, "utf8"), "old proof");
      assert.equal(readFileSync(legacy + ".gen", "utf8"), "old baseline");
      assert.equal(readFileSync(files.proof + suffix, "utf8"), "new proof state");
      assert.deepEqual(readdirSync(dir).filter(name => name.startsWith("a.fst")), ["a.fst" + suffix]);
    });
  });
}

test("artifact migration refuses to choose between two previous layouts", () => temporary(dir => {
  const source = join(dir, "a.ts");
  const files = fstarPaths(source, dir);
  const moduleFile = join(dir, `${files.moduleName}.fst`);
  const directoryFile = join(dir, "fstar", "a.fst");
  mkdirSync(join(dir, "fstar"));
  writeFileSync(moduleFile, "module proof");
  writeFileSync(directoryFile, "directory proof");
  assert.throws(() => migrateFstarArtifacts(source, files), /conflicting proof artifact sets exist/);
  assert.equal(readFileSync(moduleFile, "utf8"), "module proof");
  assert.equal(readFileSync(directoryFile, "utf8"), "directory proof");
  assert.equal(existsSync(files.proof), false);
}));

for (const file of ["fstarClosures.ts", "fstarComposition.ts", "fstarArrays.ts", "fstarIteration.ts"]) {
  test(`generated example verifies: ${file}`, realFstar, () => {
    assert.equal(verify(readFileSync(join(examples, file), "utf8")), true);
  });
}

const callablePredicates = String.raw`
  interface Predicate<in A> { (value: A): boolean }
  interface StringPredicate extends Predicate<string> {}
  export function negate<A>(self: Predicate<A>): Predicate<A> {
    //@ ensures forall(value: A, \result(value) === !self(value))
    return value => !self(value);
  }
  export function positive(value: number): boolean {
    //@ ensures \result === (value > 0)
    const predicate = negate((n: number): boolean => n <= 0);
    return predicate(value);
  }
  export function inherited(self: StringPredicate, value: string): boolean {
    //@ ensures \result === !self(value)
    const predicate = negate(self);
    return predicate(value);
  }
`;
test("callable interfaces retain instantiated and inherited signatures in opaque closure proofs", realFstar, () => temporary(dir => {
  const file = join(dir, "Test.fst");
  const generated = compile(callablePredicates).replace(/^let v_negate /m, '[@@"opaque_to_smt"]\nlet v_negate ');
  writeFileSync(file, generated);
  writeFileSync(file + ".gen", generated);
  assert.equal(fstarVerify(file, 20), true);
}));
test("callable interface proofs reject a wrong returned predicate", realFstar, () => {
  assert.equal(verify(callablePredicates.replace("return value => !self(value)", "return value => self(value)")), false);
});

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

test("function namespaces preserve generic callbacks and qualified calls", realFstar, () => {
  const source = String.raw`
    export namespace Functions {
      export function compose<A,B,C>(f:(x:B)=>C,g:(x:A)=>B):(x:A)=>C {
        //@ ensures forall(x:A, \result(x) === f(g(x)))
        return (x:A):C => f(g(x));
      }
      export namespace Inner {
        export function positive(x:number):number {
          //@ requires x > 0
          //@ ensures \result === x
          return x;
        }
      }
    }
    export function caller(x:number):number {
      //@ ensures \result === 2 * (x + 1)
      return Functions.compose((n:number):number => 2*n, (n:number):number => n+1)(x);
    }
    export function checked():number { return Functions.Inner.positive(1); }
  `;
  assert.match(compile(source), /let v_compose/);
  assert.equal(verify(source), true);
  assert.equal(verify(source.replace("positive(1)", "positive(0)")), false);
});

test("namespace verification selection checks the selected function body", realFstar, () => {
  const source = String.raw`
    export namespace Selected {
      export function identity(x:number):number {
        //@ verify
        //@ ensures \result === x
        return x;
      }
      export async function ignored():Promise<number> { return await Promise.resolve(1); }
    }
  `;
  assert.match(compile(source), /let v_identity/);
  assert.doesNotMatch(compile(source), /v_ignored/);
  assert.equal(verify(source), true);
  assert.equal(verify(source.replace("return x;", "return x+1;")), false);
});

test("string ordering uses UTF-16 lexicographic comparisons and proper prefixes", realFstar, () => {
  const source = String.raw`
    export function ordering():boolean {
      //@ ensures \result
      return "" < "a" && "a" < "aa" && "ab" < "b" && "ab" <= "ab" &&
        "b" > "aa" && "b" >= "b" && !("aa" <= "a") && !("a" >= "b") &&
        "\uD83D\uDE00" < "\uE000" && "\uD800" < "\uD801";
    }
    export function asymmetry(a:string,b:string):boolean {
      //@ ensures \result
      return !(a < b && b < a);
    }
  `;
  assert.equal(verify(source), true);
  assert.equal(verify(source.replace('"\\uD83D\\uDE00" <', '"\\uD83D\\uDE00" >')), false);
});

test("F* CLI keeps native UTF-16 literals across different Dafny source profiles", () => temporary(dir => {
  writeFileSync(join(dir, "library.ts"), String.raw`//@ option string-semantics javascript-utf16
//@ option dafny-library local
export function identity(value:string):string {
  //@ ensures \result === value
  return value;
}
`);
  writeFileSync(join(dir, "source.ts"), String.raw`import { identity } from "./library";
export function codeUnit():number {
  //@ ensures \result === 0xD800
  return identity("\uD800").charCodeAt(0);
}
`);
  const result = runCli(dir, ["gen", "--backend=fstar", "source.ts"]);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.match(readFileSync(join(dir, "source.fst.gen"), "utf8"), /S\.build \(S\.empty\) \(55296\)/);
}));

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
  ["namespace mutable closure", `export namespace N { export function bad():()=>number { let x=0; return ():number => ++x; } }`, /mutation of captured variable/],
  ["namespace reference equality", `export namespace N { export function bad(xs:number[],ys:number[]):boolean { return xs===ys; } }`, /reference equality/],
  ["namespace state", `export namespace N { const x=1; export function bad():number { return x; } }`, /Only function declarations/],
  ["namespace initialization", `export namespace N { console.log(1); export function bad():number { return 1; } }`, /Only function declarations/],
  ["namespace name collision", `export namespace A { export function value():number { return 1; } } export namespace B { export function value():number { return 2; } }`, /Namespace function name collision/],
  ["namespace arrow name collision", `const value=():number=>1; export namespace A { export function value():number { return 2; } }`, /Namespace function name collision/],
  ["namespace lookalike object", `export namespace N { export function one():number { return 1; } } export function bad(ns:typeof N):number { return ns.one(); }`, /unsupported field/],
  ["ambient namespace", `declare namespace N { function value():number; }`, /non-ambient function-only namespaces/],
  ["mutable closure", `export function bad():()=>number { let x=0; return ():number => ++x; }`, /mutation of captured variable/],
  ["reassigned captured parameter", `export function bad(x:number):number { const get=():number=>x; x++; return get(); }`, /mutation of captured variable/],
  ["shorthand capture", `type Box={x:number}; export function bad():Box { let x=0; const get=():Box=>({x}); x=1; return get(); }`, /mutation of captured variable/],
  ["wrapped captured update", `export function bad():number { const xs=[1]; const get=():number=>xs[0]; (xs as number[])[0]=2; return get(); }`, /mutation of captured variable/],
  ["wrapped captured mutator", `export function bad():number { const xs=[1]; const get=():number=>xs.length; (xs.push)(2); return get(); }`, /mutation of captured variable/],
  ["outer update of captured this", `export class Box { value:number=0; bad():number { const get=():number=>this.value; this.value++; return get(); } }`, /mutation of captured variable/],
  ["callback update of this", `export class Box { value:number=0; bad():()=>number { return ():number=>++this.value; } }`, /mutation of captured variable/],
  ["module mutation", `const xs=[1]; xs[0]=2; export function bad():number { return xs[0]; }`, /module-level statement/],
  ["escaped array constant", `export const xs=[1]; export function bad():number { return xs[0]; }`, /scalar module constants/],
  ["callback mutation", `export function bad(xs:number[]):number[] { return xs.map((x:number):number => { xs[0]=x; return x; }); }`, /mutation of captured variable/],
  ["reference equality", `export function bad(xs:number[],ys:number[]):boolean { return xs===ys; }`, /reference equality/],
  ["tuple identity", `export function bad(x:[number],y:[number]):boolean { return x===y; }`, /reference equality/],
  ["optional object identity", `type Box={x:number}; export function bad(x:Box|undefined,y:Box|undefined):boolean { return x===y; }`, /reference equality/],
  ["generic identity", `export function bad<A>(x:A,y:A):boolean { return x===y; }`, /reference equality/],
  ["function identity", `export function bad(f:()=>number,g:()=>number):boolean { return f===g; }`, /reference equality/],
  ["index callback", `export function bad(xs:number[]):number[] { return xs.map((x:number,i:number):number => x+i); }`, /1-parameter callback/],
  ["thisArg", `export function bad(xs:number[]):number[] { return xs.map((x:number):number => x, 0); }`, /thisArg/],
  ["reduce without initial", `export function bad(xs:number[]):number { return xs.reduce((x:number,y:number):number=>x+y); }`, /initial values/],
  ["destructured parameters", `export function bad([x,y]:[number,number]):number { return x+y; }`, /destructured parameters/],
  ["default parameter", `export function bad(x:number=1):number { return x; }`, /defaulted and rest/],
  ["rest parameter", `export function bad(...xs:number[]):number { return xs.length; }`, /defaulted and rest/],
  ["async", `export async function bad():Promise<number> { return await Promise.resolve(1); }`, /async functions|await/i],
  ["non-primitive constraint", `export function bad<A extends {value:number}>(x:A):number { return x.value; }`, /constrained/],
  ["default type parameter", `export function bad<A=number>(x:A):A { return x; }`, /defaulted/],
  ["type alias shadowing", `type A=number; export function bad<A>(x:A):A { return x; }`, /shadowing type aliases/],
  ["nested contract", `export function bad():(x:number)=>number { return (x:number):number => {\n //@ ensures false\n return x; }; }`, /nested lambda contracts/],
  ["unsafe literal", `export function bad():number { return 9007199254740993; }`, /safe integers/],
  ["skip", `export function bad(xs:number[]):number {\n //@ skip\n xs.push(1);\n return xs.length; }`, /statement-level skip/],
  ["contract", `export function bad(x:number):number {\n //@ contract x > 0\n return x; }`, /contract annotations/],
] as const) {
  test(`generation rejects ${label}`, () => assert.throws(() => compile(code), error));
}

// Each false contract below used to verify. Execute the same source to retain
// the counterexample, then require rejection before an F* model can be emitted.
for (const [label, code, actual, error] of [
  ["reassignment after closure creation", String.raw`export function bad():number {
    //@ ensures \result === 0
    let x=0;
    const get=():number=>x;
    x=1;
    return get();
  }`, 1, /mutation of captured variable/],
  ["array update after closure creation", String.raw`export function bad():number {
    //@ ensures \result === 1
    const xs=[1];
    const get=():number=>xs.length;
    xs.push(2);
    return get();
  }`, 2, /mutation of captured variable/],
  ["structural equality replacing object identity", String.raw`type Box={value:number};
  export function bad():boolean {
    //@ ensures \result
    const a:Box={value:1};
    const b:Box={value:1};
    return a===b;
  }`, false, /reference equality/],
] as const) {
  test(`source guard rejects falsely provable ${label}`, () => {
    const javascript = ts.transpileModule(code, {
      compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 },
    }).outputText;
    const exports: { bad?: () => unknown } = {};
    runInNewContext(javascript, { exports });
    assert.equal(exports.bad!(), actual);
    assert.throws(() => compile(code), error);
  });
}

test("capture checks preserve immutable snapshots, shadowing and nullable value tests", realFstar, () => {
  assert.equal(verify(String.raw`
    type Box={value:number};
    export function test(box:Box|undefined):number {
      //@ ensures \result === 3
      let x=0;
      const snapshot=x;
      const get=():number=>snapshot;
      x=1;
      const scoped=():number=>{ const x=2; return x; };
      if (box === undefined) return get()+x+scoped();
      return get()+x+scoped();
    }
  `), true);
});

test("generic equality accepts a primitive input constraint", realFstar, () => {
  assert.equal(verify(String.raw`
    export function same<T extends number | string>(x:T,y:T):boolean {
      return x===y;
    }
    export function test(n:number,s:string):boolean {
      //@ ensures \result
      return same(n,n) && same(s,s) && !same(n,n+1);
    }
  `), true);
});


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
for (const layout of ["module", "directory"] as const) {
  test(`CLI regen migrates ${layout} companions before merging source changes`, () => temporary(dir => {
    const source = join(dir, "a-b.ts");
    const files = fstarPaths(source, dir);
    const legacy = layout === "module" ? join(dir, `${files.moduleName}.fst`) : join(dir, "fstar", "a-b.fst");
    mkdirSync(join(dir, "fstar"));
    const program = (n: number) => `export function add(x:number):number { return x+${n}; }
      export function unchanged(x:number):number { const y=x+1; return y+1; }`;
    const baseline = compile(program(1), files.moduleName).replace("Program source: input.ts", "Program source: a-b.ts");
    const addition = "\nlet retained_proof () : Lemma (1 + 1 == 2) = ()\n";
    writeFileSync(source, program(2));
    writeFileSync(legacy + ".gen", baseline);
    writeFileSync(legacy, baseline + addition);
    const result = runCli(dir, ["regen", "--backend=fstar", "--no-verify", source]);
    assert.equal(result.status, 0, result.stderr);
    assert.equal(existsSync(legacy), false);
    assert.equal(existsSync(legacy + ".gen"), false);
    assert.equal(existsSync(files.base), false);
    const generated = readFileSync(files.gen, "utf8");
    assert.match(generated, /v_x \+ \(2\)/);
    assert.equal(readFileSync(files.proof, "utf8"), generated + addition);
  }));
}
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
