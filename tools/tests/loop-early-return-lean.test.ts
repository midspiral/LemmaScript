import { test } from "node:test";
import assert from "node:assert/strict";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function compileLean(tsText: string, fileName: string): string {
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true },
    useInMemoryFileSystem: true,
  });
  const sf = project.createSourceFile(fileName, tsText, { overwrite: true });
  const diags = project.getPreEmitDiagnostics().map(d => d.getMessageText());
  assert.deepEqual(diags, [], `invalid TS in ${fileName}: ${JSON.stringify(diags)}`);
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(narrowModule(resolveModule(extractModule(sf))));
  const optTypes = typesFile ? peepholeModule(typesFile, "lean") : null;
  const optDef = peepholeModule(defFile, "lean");
  return [optTypes ? emitLeanFile(optTypes) : "", emitLeanFile(optDef)].filter(Boolean).join("\n\n");
}

test("early return in loop lowers via Option T and preserves post-loop state", () => {
  const lean = compileLean(`
export function countBeforeNeg(xs: number[]): number {
  //@ verify
  //@ type i nat
  //@ ensures 0 <= \\result && \\result <= xs.length
  let count = 0;
  let i = 0;
  while (i < xs.length) {
    //@ invariant 0 <= i && i <= xs.length
    //@ invariant 0 <= count && count <= i
    //@ decreases xs.length - i
    //@ done_with true
    if (xs[i]! < 0) {
      return count;
    }
    count = count + 1;
    i = i + 1;
  }
  return count;
}
`, "count_before_neg.ts");

  assert.match(lean, /let mut _loopRet : Option Int := none/, lean);
  assert.doesNotMatch(lean, /let mut _loopRet : Int := count/, lean);
  assert.match(lean, /_loopRet := some count\n\s+break/, lean);
  assert.match(lean, /∀ \(_h0 : \(_loopRet\.isSome\) = true\), 0 ≤ \(\(_loopRet\)\.get \(by grind\)\)/, lean);
  assert.match(lean, /if h__loopRet : \(_loopRet\)\.isSome = true then\n\s+let _loopRet_val := \(_loopRet\)\.get h__loopRet\n\s+return _loopRet_val\n\s+else\n\s+return count/, lean);
});

test("loop early-return temp avoids colliding with user parameters", () => {
  const lean = compileLean(`
export function collideParam(n: number, _loopRet: boolean, _loopRet_val: number): number {
  //@ verify
  //@ ensures _loopRet ==> \\result === 1
  //@ ensures !_loopRet ==> \\result === 2
  let i = 0;
  while (i < n) {
    //@ invariant 0 <= i
    //@ decreases n - i
    //@ done_with true
    if (i === 999) {
      return _loopRet ? 1 : 2;
    }
    i = i + 1;
  }
  if (_loopRet) {
    return _loopRet_val - _loopRet_val + 1;
  }
  return 2;
}
`, "collide_param.ts");

  assert.match(lean, /let mut _loopRet' : Option Int := none/, lean);
  assert.match(lean, /_loopRet' := some \(if _loopRet then 1 else 2\)\n\s+break/, lean);
  assert.match(lean, /let _loopRet_val' := \(_loopRet'\)\.get/, lean);
  assert.match(lean, /else\n\s+if _loopRet then/, lean);
});

test("generic return type with fallthrough emits Option T without default : T", () => {
  const lean = compileLean(`
export function pickOrFallback<T>(n: number, x: T, fallback: T): T {
  //@ verify
  //@ type i nat
  //@ ensures \\result === x || \\result === fallback
  let i = 0;
  while (i < n) {
    //@ invariant 0 <= i
    //@ decreases n - i
    //@ done_with true
    if (i === 0) {
      return x;
    }
    i = i + 1;
  }
  return fallback;
}
`, "generic_loop_ret.ts");

  assert.match(lean, /let mut _loopRet : Option T := none/, lean);
  assert.doesNotMatch(lean, /\(default : T\)/, lean);
  assert.match(lean, /_loopRet := some x\n\s+break/, lean);
  assert.match(lean, /else\n\s+return fallback/, lean);
});

test("optional return type distinguishes early return undefined from fallthrough", () => {
  const lean = compileLean(`
export function stopAtZero(xs: number[]): number | undefined {
  //@ verify
  //@ type i nat
  let i = 0;
  while (i < xs.length) {
    //@ invariant 0 <= i && i <= xs.length
    //@ decreases xs.length - i
    //@ done_with true
    if (xs[i]! === 0) {
      return undefined;
    }
    i = i + 1;
  }
  return i;
}
`, "optional_loop_ret.ts");

  assert.match(lean, /let mut _loopRet : Option \(Option Int\) := none/, lean);
  assert.match(lean, /_loopRet := some none\n\s+break/, lean);
  assert.match(lean, /else\n\s+return some/, lean);
});
