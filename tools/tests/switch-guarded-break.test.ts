import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

function compile(tsText: string, fileName: string, backend: "dafny" | "lean"): string {
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true },
    useInMemoryFileSystem: true,
  });
  const sf = project.createSourceFile(fileName, tsText, { overwrite: true });
  const diags = project.getPreEmitDiagnostics().map(d => d.getMessageText());
  assert.deepEqual(diags, [], `invalid TS in ${fileName}: ${JSON.stringify(diags)}`);
  const typed = narrowModule(resolveModule(extractModule(sf)));
  if (backend === "dafny") {
    const { typesFile, defFile } = transformModuleDafny(typed);
    const optTypes = typesFile ? peepholeModule(typesFile, "dafny") : null;
    const optDef = peepholeModule(defFile, "dafny");
    return emitDafnyFile({ ...optDef, decls: [...(optTypes?.decls ?? []), ...optDef.decls] }, fileName);
  }
  resetLeanModule();
  const { typesFile, defFile } = transformModuleLean(typed);
  const optTypes = typesFile ? peepholeModule(typesFile, "lean") : null;
  const optDef = peepholeModule(defFile, "lean");
  return [optTypes ? emitLeanFile(optTypes) : "", emitLeanFile(optDef)].filter(Boolean).join("\n\n");
}

function verifyDafny(dfyText: string): { status: number | null; output: string } {
  const dir = mkdtempSync(join(tmpdir(), "lsc-switch-break-"));
  try {
    const file = join(dir, "repro.dfy");
    writeFileSync(file, dfyText);
    const res = spawnSync("dafny", ["verify", "--verification-time-limit:15", file], {
      encoding: "utf8",
      timeout: 60_000,
    });
    assert.ifError(res.error);
    return { status: res.status, output: `${res.stdout ?? ""}\n${res.stderr ?? ""}` };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const guardedBreakInLoopSource = `
type Tag = "a" | "b";

export function switchGuardedBreak(t: Tag, flag: boolean): number {
  //@ verify
  //@ ensures t === "a" && flag ==> \\result === 2
  //@ ensures t === "a" && !flag ==> \\result === 22
  //@ ensures t === "b" ==> \\result === 2
  let count = 0;
  let i = 0;
  while (i < 2) {
    //@ invariant 0 <= i && i <= 2
    //@ invariant t === "a" && flag ==> count === i
    //@ invariant t === "a" && !flag ==> count === 11 * i
    //@ invariant t === "b" ==> count === i
    //@ decreases 2 - i
    switch (t) {
      case "a":
        if (flag) break;
        count = count + 10;
        break;
      case "b":
        break;
    }
    count = count + 1;
    i = i + 1;
  }
  return count;
}

export function switchGuardedBreakFallthrough(t: Tag, flag: boolean): number {
  //@ verify
  //@ ensures t === "a" && flag ==> \\result === 0
  //@ ensures t === "a" && !flag ==> \\result === 11
  //@ ensures t === "b" ==> \\result === 10
  let x = 0;
  switch (t) {
    case "a":
      if (flag) break;
      x = 1;
    case "b":
      x = x + 10;
      break;
  }
  return x;
}

export function switchBothBranchesBreakNoFallthrough(t: Tag, flag: boolean): number {
  //@ verify
  //@ ensures t === "a" && flag ==> \\result === 1
  //@ ensures t === "a" && !flag ==> \\result === 2
  //@ ensures t === "b" ==> \\result === 99
  let x = 0;
  switch (t) {
    case "a":
      if (flag) {
        x = 1;
        break;
      } else {
        x = 2;
        break;
      }
    case "b":
      x = 99;
      break;
  }
  return x;
}
`;

test("guarded break inside switch does not escape to enclosing loop in Dafny", () => {
  const dfy = compile(guardedBreakInLoopSource, "switch_guarded_break.ts", "dafny");
  assert.doesNotMatch(dfy, /\bbreak;/, dfy);
  const res = verifyDafny(dfy);
  assert.equal(res.status, 0, `${dfy}\n${res.output}`);
});

test("Dafny rejects false loop-exit postcondition on one-iteration loop (passes on buggy base)", () => {
  const falseSource = `
type Tag = "a" | "b";

export function switchGuardedBreakFalse(t: Tag, flag: boolean): number {
  //@ verify
  //@ ensures t === "a" && flag ==> \\result === 0
  let x = 0;
  let i = 0;
  while (i < 1) {
    //@ invariant 0 <= i && i <= 1
    //@ invariant t === "a" && flag ==> x === 0
    //@ decreases 1 - i
    switch (t) {
      case "a":
        if (flag) break;
        break;
      case "b":
        break;
    }
    x = 1;
    i = i + 1;
  }
  return x;
}
`;
  const dfy = compile(falseSource, "switch_guarded_break_false.ts", "dafny");
  const res = verifyDafny(dfy);
  assert.notEqual(res.status, 0, `${dfy}\n${res.output}`);
});

test("sequential nested break guards stay linear via a fresh switch-exit flag", () => {
  const guards = Array.from({ length: 10 }, () => "if (p) { if (q) break; }").join("\n        ");
  const src = `
type Tag = "a" | "b";

export function manyNestedGuards(t: Tag, p: boolean, q: boolean, _switchBroken: number): number {
  //@ verify
  //@ ensures t === "a" && !(p && q) ==> \\result === _switchBroken + 1
  //@ ensures t === "a" && p && q ==> \\result === _switchBroken
  //@ ensures t === "b" ==> \\result === _switchBroken
  let x = _switchBroken;
  switch (t) {
    case "a":
        ${guards}
        x = x + 1;
        break;
    case "b":
        break;
  }
  return x;
}
`;
  const dfy = compile(src, "many_nested_guards.ts", "dafny");
  assert.doesNotMatch(dfy, /\bbreak;/, dfy);
  assert.match(dfy, /var i_switchBroken' := false;/, dfy);
  const assignCount = (dfy.match(/x := \(x \+ 1\);/g) ?? []).length;
  assert.equal(assignCount, 1, `expected x := (x + 1) once, got ${assignCount}\n${dfy}`);
  const res = verifyDafny(dfy);
  assert.equal(res.status, 0, `${dfy}\n${res.output}`);

  const lean = compile(src, "many_nested_guards.ts", "lean");
  assert.doesNotMatch(lean, /\bbreak\b/, lean);
  assert.match(lean, /let mut _switchBroken' : Bool := false/, lean);
  const leanAssignCount = (lean.match(/x := x \+ 1/g) ?? []).length;
  assert.equal(leanAssignCount, 1, `expected x := x + 1 once in Lean, got ${leanAssignCount}\n${lean}`);
});

test("flag-based switch break lowering preserves TypeScript narrowing on single-branch guards", () => {
  const reviewerRepro = `
type Tag = "a" | "b";

export function flagGuardPreservesNarrowing(t: Tag, p: boolean, q: boolean, v: number | undefined): number {
  //@ verify
  //@ ensures t === "a" && !(p && q) && v !== undefined ==> \\result === v + 1
  //@ ensures t === "a" && ((p && q) || v === undefined) ==> \\result === 0
  //@ ensures t === "b" ==> \\result === 0
  let n = 0;
  switch (t) {
    case "a":
      if (p) { if (q) break; }
      if (v === undefined) break;
      n = v + 1;
      break;
    case "b":
      break;
  }
  return n;
}
`;
  const dfy = compile(reviewerRepro, "flag_guard_narrowing.ts", "dafny");
  assert.doesNotMatch(dfy, /\bbreak;/, dfy);
  assert.match(dfy, /case Some\(i_v_val\) =>/, dfy);
  const addCount = (dfy.match(/n := \(i_v_val \+ 1\);/g) ?? []).length;
  assert.equal(addCount, 1, `expected n := (i_v_val + 1) once, got ${addCount}\n${dfy}`);
  const res = verifyDafny(dfy);
  assert.equal(res.status, 0, `${dfy}\n${res.output}`);

  const lean = compile(reviewerRepro, "flag_guard_narrowing.ts", "lean");
  assert.doesNotMatch(lean, /\bbreak\b/, lean);
  assert.match(lean, /\(v\)\.isSome = true/, lean);
  const leanAddCount = (lean.match(/n := _v_val \+ 1/g) ?? []).length;
  assert.equal(leanAddCount, 1, `expected n := _v_val + 1 once in Lean, got ${leanAddCount}\n${lean}`);

  const nestedAndLeading = `
type Tag = "a" | "b";

export function nestedNarrowingInsideFlagGuard(t: Tag, p: boolean, v: number | undefined): number {
  //@ verify
  //@ ensures t === "a" && p && v === undefined ==> \\result === 0
  //@ ensures t === "a" && p && v !== undefined ==> \\result === v + 11
  //@ ensures t === "a" && !p ==> \\result === 10
  //@ ensures t === "b" ==> \\result === 0
  let n = 0;
  switch (t) {
    case "a":
      if (p) {
        if (v === undefined) break;
        n = v + 1;
      }
      n = n + 10;
      break;
    case "b":
      break;
  }
  return n;
}

export function narrowingBeforeFlagGuard(t: Tag, p: boolean, q: boolean, v: number | undefined): number {
  //@ verify
  //@ ensures t === "a" && !(p && q) && v !== undefined ==> \\result === v + 1
  //@ ensures t === "a" && ((p && q) || v === undefined) ==> \\result === 0
  //@ ensures t === "b" ==> \\result === 0
  let n = 0;
  switch (t) {
    case "a":
      if (v === undefined) break;
      if (p) { if (q) break; }
      n = v + 1;
      break;
    case "b":
      break;
  }
  return n;
}
`;
  const dfy2 = compile(nestedAndLeading, "flag_guard_narrowing_nested.ts", "dafny");
  assert.doesNotMatch(dfy2, /\bbreak;/, dfy2);
  assert.match(dfy2, /case Some\(i_v_val\) =>/, dfy2);
  const res2 = verifyDafny(dfy2);
  assert.equal(res2.status, 0, `${dfy2}\n${res2.output}`);

  const lean2 = compile(nestedAndLeading, "flag_guard_narrowing_nested.ts", "lean");
  assert.doesNotMatch(lean2, /\bbreak\b/, lean2);
  assert.match(lean2, /\(v\)\.isSome = true/, lean2);
  assert.match(lean2, /n := _v_val \+ 1/, lean2);
});

test("guarded break inside switch emits structured if/else without break in Lean", () => {
  const lean = compile(guardedBreakInLoopSource, "switch_guarded_break.ts", "lean");
  assert.doesNotMatch(lean, /\bbreak\b/, lean);
  assert.match(lean, /if flag then\n\s+pure \(\)\n\s+else\n\s+count := count \+ 10/, lean);
});

test("break inside a nested loop inside a switch case is preserved", () => {
  const src = `
type Tag = "a" | "b";

export function nestedLoopBreakInSwitch(t: Tag): number {
  //@ verify
  //@ ensures t === "a" ==> \\result === 1
  //@ ensures t === "b" ==> \\result === 0
  let x = 0;
  switch (t) {
    case "a": {
      let j = 0;
      while (j < 5) {
        //@ invariant 0 <= j && j <= 5
        //@ invariant j === 0 ==> x === 0
        //@ invariant j > 0 ==> x === 1
        //@ decreases 5 - j
        x = 1;
        break;
      }
      break;
    }
    case "b":
      break;
  }
  return x;
}
`;
  const dfy = compile(src, "nested_loop_break.ts", "dafny");
  assert.match(dfy, /\bbreak;/, dfy);
  const res = verifyDafny(dfy);
  assert.equal(res.status, 0, `${dfy}\n${res.output}`);
});
