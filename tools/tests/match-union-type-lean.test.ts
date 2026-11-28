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

test("switch on second string union sharing a variant name uses scrutinee union, not first matching decl", () => {
  const lean = compileLean(`
type A = "skip" | "keep";
type B = "skip" | "stop";

export function useA(a: A): number {
  //@ verify
  return a === "skip" ? 0 : 1;
}

export function switchOnB(t: B): number {
  //@ verify
  //@ ensures t === "skip" ==> \\result === 1
  //@ ensures t === "stop" ==> \\result === 2
  let x = 0;
  switch (t) {
    case "skip":
      x = 1;
      break;
    case "stop":
      x = 2;
      break;
  }
  return x;
}

export function switchOnBWithEmptyArm(t: B): number {
  //@ verify
  //@ ensures t === "skip" ==> \\result === 0
  //@ ensures t === "stop" ==> \\result === 2
  let x = 0;
  switch (t) {
    case "skip":
      break;
    case "stop":
      x = 2;
      break;
  }
  return x;
}
`, "shared_string_union.ts");

  const startB = lean.indexOf("method switchOnB ");
  assert.notEqual(startB, -1, lean);
  const bodyB = lean.slice(startB);
  assert.match(bodyB, /if t = B\.skip then\n\s+x := 1\n\s+else\n\s+x := 2/, bodyB);
  assert.match(bodyB, /if t = B\.skip then\n\s+pure \(\)\n\s+else\n\s+x := 2/, bodyB);
  assert.doesNotMatch(bodyB, /A\.skip/, bodyB);
});

test("switch on second discriminated union sharing variant names uses scrutinee union", () => {
  const lean = compileLean(`
type UA = { kind: "ok"; v: number } | { kind: "err" };
type UB = { kind: "ok"; w: number } | { kind: "err" };

export function useUA(u: UA): number {
  //@ verify
  return u.kind === "ok" ? u.v : 0;
}

export function switchOnUB(u: UB): number {
  //@ verify
  let x = 0;
  switch (u.kind) {
    case "ok":
      x = u.w;
      break;
    case "err":
      x = -1;
      break;
  }
  return x;
}
`, "shared_discriminated_union.ts");

  const startUB = lean.indexOf("method switchOnUB ");
  assert.notEqual(startUB, -1, lean);
  const bodyUB = lean.slice(startUB);
  assert.doesNotMatch(bodyUB, /UA\./, bodyUB);
  assert.match(bodyUB, /match u with \| \.ok/, bodyUB);
});

test("Option match is not hijacked by a user string union with 'some' / 'none' variants", () => {
  const lean = compileLean(`
type Mode = "some" | "none";

export function useMode(m: Mode): number {
  //@ verify
  return m === "some" ? 1 : 0;
}

export function incOptional(x?: number): number {
  //@ verify
  let n = 0;
  if (x !== undefined) {
    n = x + 1;
  }
  return n;
}
`, "mode_option_collision.ts");

  const startOpt = lean.indexOf("method incOptional ");
  assert.notEqual(startOpt, -1, lean);
  const bodyOpt = lean.slice(startOpt);
  assert.match(bodyOpt, /\(x\)\.isSome = true/, bodyOpt);
  assert.match(bodyOpt, /let _x_val := \(x\)\.get/, bodyOpt);
  assert.doesNotMatch(bodyOpt, /Mode\.some/, bodyOpt);
});
