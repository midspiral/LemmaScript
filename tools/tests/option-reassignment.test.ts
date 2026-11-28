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
import { transformModuleDafny } from "../src/transform.ts";
import { peepholeModule } from "../src/peephole.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";

function compileDafny(tsText: string, fileName: string): string {
  const project = new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true },
    useInMemoryFileSystem: true,
  });
  const sf = project.createSourceFile(fileName, tsText, { overwrite: true });
  const diags = project.getPreEmitDiagnostics().map(d => d.getMessageText());
  assert.deepEqual(diags, [], `invalid TS in ${fileName}: ${JSON.stringify(diags)}`);
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(sf))));
  const optTypes = typesFile ? peepholeModule(typesFile, "dafny") : null;
  const optDef = peepholeModule(defFile, "dafny");
  return emitDafnyFile({ ...optDef, decls: [...(optTypes?.decls ?? []), ...optDef.decls] }, fileName);
}

function verifyDafny(dfyText: string): { status: number | null; output: string } {
  const dir = mkdtempSync(join(tmpdir(), "lsc-opt-reassign-"));
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

test("option reassignment inside narrowed branches verifies true contracts in Dafny", () => {
  const validTs = `
export interface Box { val?: number }

//@ requires input === 1
//@ ensures \\result === 5
export function reassignInIf(input?: number): number {
  let x = input;
  if (x !== undefined) {
    x = 5;
    return x;
  }
  return 0;
}

//@ requires input === 1
//@ ensures \\result === 5
export function reassignAfterEarlyReturn(input?: number): number {
  let x = input;
  if (x === undefined) {
    return 0;
  }
  x = 5;
  return x;
}

//@ requires xIn === 1 && yIn === 2
//@ ensures flag ==> \\result === 9
//@ ensures !flag ==> \\result === 1
export function conditionalClearViaClearedAlias(xIn: number | undefined, yIn: number | undefined, flag: boolean): number {
  let x = xIn;
  let y = yIn;
  if (x !== undefined && y !== undefined) {
    if (flag) {
      y = undefined;
      x = y;
    }
    return x ?? 9;
  }
  return 0;
}

//@ requires input.val === 1
//@ ensures \\result === 5
export function reassignOptionalField(input: Box): number {
  let box = input;
  if (box.val !== undefined) {
    box.val = 5;
    return box.val;
  }
  return 0;
}
`;
  const dfy = compileDafny(validTs, "opt_reassign_valid.ts");
  const res = verifyDafny(dfy);
  assert.equal(res.status, 0, `${dfy}\n${res.output}`);
});

test("option reassignment rejects stale-value false postconditions in Dafny", () => {
  const falseCases: Array<[string, string]> = [
    [
      "direct-stale",
      `//@ requires input === 1
      //@ ensures \\result === 1
      export function f(input?: number): number {
        let x = input;
        if (x !== undefined) {
          x = 5;
          return x;
        }
        return 0;
      }`,
    ],
    [
      "conditional-clear-via-alias-stale",
      `//@ requires xIn === 1 && yIn === 2
      //@ ensures flag ==> \\result === 1
      export function f(xIn: number | undefined, yIn: number | undefined, flag: boolean): number {
        let x = xIn;
        let y = yIn;
        if (x !== undefined && y !== undefined) {
          if (flag) {
            y = undefined;
            x = y;
          }
          return x ?? 9;
        }
        return 0;
      }`,
    ],
    [
      "field-stale",
      `export interface Box { val?: number }
      //@ requires input.val === 1
      //@ ensures \\result === 1
      export function f(input: Box): number {
        let box = input;
        if (box.val !== undefined) {
          box.val = 5;
          return box.val;
        }
        return 0;
      }`,
    ],
  ];

  for (const [label, src] of falseCases) {
    const dfy = compileDafny(src, `${label}.ts`);
    const res = verifyDafny(dfy);
    assert.notEqual(res.status, 0, `${label} should fail verification!\n${dfy}\n${res.output}`);
    assert.match(res.output, /postcondition could not be proved|might not hold/, `${label}:\n${res.output}`);
  }
});
