import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
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

function source(text: string) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const file = project.createSourceFile("/closures.ts", text);
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

function verifyDafny(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-closures-"));
  try {
    const path = join(dir, "closures.dfy");
    writeFileSync(path, text);
    const stdlib = text.includes("Std.") ? ["--standard-libraries"] : [];
    const result = spawnSync("dafny", ["verify", ...stdlib, "--verification-time-limit=15", path],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally { rmSync(dir, { recursive: true, force: true }); }
}

test("rejects closure capturing a reassigned let variable (#267 repro 1)", () => {
  const text = `
    //@ ensures \\result === 2
    export function late(): number {
      let n = 1;
      const f = (x: number): number => x + n;
      n = 5;
      return f(1);
    }`;
  for (const backend of ["dafny", "lean"] as const) {
    assert.throws(() => generate(text, backend),
      /Unsupported closure over mutable variable 'n' at line 5/, backend);
  }
});

test("rejects closure capturing an array, object, Map, or Set mutated in place (#267 repro 2)", () => {
  const cases: [string, string, string][] = [
    ["array push", "a", `
      export function stale(): number {
        const a: number[] = [1];
        const len = (k: number): number => a.length + k;
        a.push(2);
        return len(0);
      }`],
    ["array index assign", "a", `
      export function staleIdx(): number {
        const a: number[] = [1];
        const first = (k: number): number => a[0] + k;
        a[0] = 9;
        return first(0);
      }`],
    ["array pop", "a", `
      export function stalePop(): number {
        const a: number[] = [1, 2];
        const len = (k: number): number => a.length + k;
        a.pop();
        return len(0);
      }`],
    ["object property mutation", "box", `
      export function staleObj(): number {
        const box = { v: 1 };
        const read = (k: number): number => box.v + k;
        box.v = 9;
        return read(0);
      }`],
    ["nested array field mutation", "box", `
      export function staleNested(): number {
        const box = { xs: [1] };
        const len = (k: number): number => box.xs.length + k;
        box.xs.push(2);
        return len(0);
      }`],
    ["Map set", "m", `
      export function staleMap(): number {
        const m = new Map<string, number>();
        const sz = (k: number): number => m.size + k;
        m.set("a", 1);
        return sz(0);
      }`],
    ["Set add", "s", `
      export function staleSet(): number {
        const s = new Set<number>();
        const sz = (k: number): number => s.size + k;
        s.add(1);
        return sz(0);
      }`],
  ];
  for (const [label, name, text] of cases) {
    assert.throws(() => extractModule(source(text)),
      new RegExp(`Unsupported closure over mutable variable '${name}' at line \\d+`), label);
  }
});

test("rejects closure capturing a collection mutated through a call or an alias (#267 repro 3)", () => {
  const cases: [string, string, string][] = [
    ["direct mutating helper call", "arr", `
      function push1(a: number[]): void { a.push(1); }
      export function viaCall(): number {
        const arr: number[] = [];
        const f = (k: number): number => arr.length + k;
        push1(arr);
        return f(0);
      }`],
    ["transitive mutating helper call", "arr", `
      function push1(a: number[]): void { a.push(1); }
      function wrap(b: number[]): void { push1(b); }
      export function viaTransitiveCall(): number {
        const arr: number[] = [];
        const f = (k: number): number => arr.length + k;
        wrap(arr);
        return f(0);
      }`],
    ["alias mutated after closure", "arr", `
      export function viaAlias(): number {
        const arr: number[] = [];
        const f = (k: number): number => arr.length + k;
        const b = arr;
        b.push(1);
        return f(0);
      }`],
    ["reverse alias mutated after closure", "b", `
      export function viaReverseAlias(): number {
        const arr: number[] = [];
        const b = arr;
        const f = (k: number): number => b.length + k;
        arr.push(1);
        return f(0);
      }`],
    ["field alias mutated", "box", `
      export function viaFieldAlias(): number {
        const box = { xs: [1] };
        const f = (k: number): number => box.xs.length + k;
        const ys = box.xs;
        ys.push(2);
        return f(0);
      }`],
    ["alias returned from identity helper", "arr", `
      function id(a: number[]): number[] { return a; }
      export function viaReturnedAlias(): number {
        const arr: number[] = [];
        const f = (k: number): number => arr.length + k;
        const b = id(arr);
        b.push(1);
        return f(0);
      }`],
    ["alias through Object.assign", "arr", `
      export function viaObjectAssign(): number {
        const arr: number[] = [1];
        const dst: { xs: number[] } = { xs: [] };
        Object.assign(dst, { xs: arr });
        const f = (k: number): number => arr.length + k;
        dst.xs.push(2);
        return f(0);
      }`],
    ["alias through Object.values", "box", `
      export function viaObjectValues(): number {
        const box = { xs: [1] };
        const vals = Object.values(box);
        const f = (k: number): number => box.xs.length + k;
        vals[0].push(2);
        return f(0);
      }`],
    ["alias through map returning non-primitive elements", "arr", `
      export function viaMapNonPrimitive(): number {
        const arr: number[] = [1];
        const nested = [0].map((): number[] => arr);
        const f = (k: number): number => arr.length + k;
        nested[0].push(2);
        return f(0);
      }`],
  ];
  for (const [label, name, text] of cases) {
    assert.throws(() => extractModule(source(text)),
      new RegExp(`Unsupported closure over mutable variable '${name}' at line \\d+`), label);
  }
});

test("rejects closures that mutate captured outer bindings in their own body (#267)", () => {
  const cases: [string, string, string][] = [
    ["stored closure mutating let", "c", `
      export function bumpStored(xs: number[]): number {
        let c = 0;
        const bump = (x: number): number => { c = c + x; return c; };
        return xs.map(bump).length;
      }`],
    ["inline map callback mutating let", "c", `
      export function bumpInline(xs: number[]): number {
        let c = 0;
        return xs.map((x: number): number => { c = c + x; return c; }).length;
      }`],
    ["returned counter closure", "n", `
      export function counter(): () => number {
        let n = 0;
        return (): number => { n = n + 1; return n; };
      }`],
    ["inline map callback pushing outer array", "log", `
      export function pushInline(xs: number[]): number {
        const log: number[] = [];
        return xs.map((x: number): number => { log.push(x); return x; }).length;
      }`],
    ["inline map callback calling mutating helper on outer array", "log", `
      function push1(a: number[]): void { a.push(1); }
      export function callMutInline(xs: number[]): number {
        const log: number[] = [];
        return xs.map((x: number): number => { push1(log); return x; }).length;
      }`],
  ];
  for (const [label, name, text] of cases) {
    assert.throws(() => extractModule(source(text)),
      new RegExp(`Unsupported closure over mutable variable '${name}' at line \\d+`), label);
  }
});

test("rejects closures capturing mutated class 'this' and sort callbacks capturing receiver", () => {
  const mutatedThis = `
    export class Counter {
      count: number = 0;
      //@ verify
      bad(): number {
        const f = (k: number): number => this.count + k;
        this.count = 5;
        return f(1);
      }
    }`;
  assert.throws(() => extractModule(source(mutatedThis)),
    /Unsupported closure over mutable 'this' at line 6/);

  const selfMutatedThis = `
    export class Counter {
      count: number = 0;
      //@ verify
      bad(xs: number[]): number {
        return xs.map((x: number): number => { this.count = x; return x; }).length;
      }
    }`;
  assert.throws(() => extractModule(source(selfMutatedThis)),
    /Unsupported closure over mutable 'this' at line 6/);

  const sortCapture = `
    export function badSort(a: number[]): number[] {
      return a.sort((x: number, y: number): number => x - y + a.length);
    }`;
  assert.throws(() => extractModule(source(sortCapture)),
    /Unsupported closure over mutable variable 'a' at line 3/);

  const sortAliasedCapture = `
    export function badAliasedSort(a: number[]): number[] {
      const b = a;
      return b.sort((x: number, y: number): number => x - y + a.length);
    }`;
  assert.throws(() => extractModule(source(sortAliasedCapture)),
    /Unsupported closure over mutable variable 'a' at line 4/);
});

test("allows pure captures, snapshots, pure helper calls, shadowed locals, and immediate callbacks in loops", () => {
  const text = `
    //@ ensures \\result === a.length
    function countItems(a: number[]): number {
      return a.length;
    }

    //@ ensures \\result === 2
    export function primitiveSnapshot(): number {
      let n = 1;
      const snap = n;
      const f = (x: number): number => x + snap;
      n = 5;
      return f(1);
    }

    //@ ensures \\result === 1
    export function arraySliceSnapshot(): number {
      const a: number[] = [1];
      const snap = a.slice();
      const f = (k: number): number => snap.length + k;
      a.push(2);
      return f(0);
    }

    //@ ensures \\result === 1
    export function arrayRebindOnly(): number {
      let a: number[] = [1];
      const b = a;
      const f = (k: number): number => b.length + k;
      a = [1, 2];
      return f(0);
    }

    //@ ensures \\result === 4
    export function pureHelperCall(): number {
      const arr: number[] = [1, 2];
      const f = (k: number): number => arr.length + k;
      const n = countItems(arr);
      return f(n);
    }

    export function inlineCallbackInLoop(xs: number[]): number {
      let total = 0;
      for (let i = 0; i < 3; i++) {
        const ys = xs.filter((x: number): boolean => x > i);
        total = total + ys.length;
      }
      return total;
    }

    export function shadowedAndLocal(): number {
      let n = 1;
      const f = (x: number): number => {
        const local = x + 1;
        return local;
      };
      const g = (n: number): number => n + 1;
      n = 9;
      return f(1) + g(n);
    }`;
  const dafny = generate(text, "dafny");
  const result = verifyDafny(dafny);
  assert.equal(result.status, 0, result.output);

  // Mutable local declared inside the closure itself is not an outer capture.
  const innerMutable = `
    export function innerLocalMut(): number {
      const f = (x: number): number => {
        let acc = 0;
        acc = x + 1;
        return acc;
      };
      return f(5);
    }`;
  const leanInner = generate(innerMutable, "lean");
  assert.match(leanInner, /let mut acc/);
});

test("both CLIs reject mutable closures before writing verification artifacts", () => {
  const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
  const loader = createRequire(import.meta.url).resolve("tsx");
  const text = `
    export function late(): number {
      let n = 1;
      const f = (x: number): number => x + n;
      n = 5;
      return f(1);
    }`;
  for (const backend of ["dafny", "lean"] as const) {
    const dir = mkdtempSync(join(tmpdir(), `lsc-mutable-${backend}-`));
    try {
      const file = join(dir, "late.ts");
      writeFileSync(file, text);
      const res = spawnSync(process.execPath, ["--import", loader, cli, "gen", `--backend=${backend}`, file],
        { encoding: "utf8" });
      assert.notEqual(res.status, 0, `${backend} should reject mutable capture`);
      assert.match(res.stdout + res.stderr, /Unsupported closure over mutable variable 'n'/);
      assert.equal(existsSync(join(dir, backend === "dafny" ? "late.dfy.gen" : "late.def.lean")), false);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }
});

test("Lean backend emits valid syntax for zero-parameter arrows (#267)", () => {
  const text = `
    function topZero(): number { return 7; }

    export function zeroParam(): number {
      const a: number[] = [1, 2];
      const len = (): number => a.length;
      const get = () => 3;
      return len() + get() + topZero();
    }

    export function applyThunk(f: () => number): number {
      return f();
    }`;
  const lean = generate(text, "lean");
  assert.doesNotMatch(lean, /fun\s+=>/, `invalid zero-param fun syntax:\n${lean}`);
  assert.match(lean, /fun \(\) => a\.size/);
  assert.match(lean, /fun \(\) => 3/);
  assert.match(lean, /\blen \(\)/);
  assert.match(lean, /\bget \(\)/);
  assert.match(lean, /\bf \(\)/);
  assert.match(lean, /\(f : Unit → Int\)/);
  assert.doesNotMatch(lean, /topZero \(\)/);
});
