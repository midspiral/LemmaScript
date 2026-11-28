import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { Project, ScriptTarget, SyntaxKind, type Type, type TypeNode } from "ts-morph";
import {
  extractTy,
  extractTyFromNode,
  eraseGenericTy,
  typeToTsString,
  wrapNullability,
  type ExtractTypeCtx,
} from "../src/extract-types.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { runInfo, runTypedInfo } from "../src/info-command.ts";
import { DEFAULT_OPTIONS } from "../src/config.ts";
import type { TypeDeclInfo } from "../src/types.ts";

function makeProject(strictNullChecks = true) {
  return new Project({
    useInMemoryFileSystem: true,
    compilerOptions: {
      target: ScriptTarget.ES2022,
      strict: strictNullChecks,
      strictNullChecks,
    },
  });
}

function getVarType(
  code: string,
  varName = "x",
  opts: { strictNullChecks?: boolean; useTypeNode?: boolean; ctx?: ExtractTypeCtx } = {},
) {
  const project = makeProject(opts.strictNullChecks ?? true);
  const sf = project.createSourceFile("test.ts", code, { overwrite: true });
  const decl = sf.getVariableDeclarationOrThrow(varName);
  const type: Type = decl.getType();
  const tn: TypeNode | undefined = opts.useTypeNode ? decl.getTypeNode() : undefined;
  return {
    type,
    tn,
    ty: extractTy(type, tn, opts.ctx),
    tsText: typeToTsString(type, opts.ctx),
  };
}

function getFnReturn(
  code: string,
  fnName = "f",
  opts: { strictNullChecks?: boolean; useTypeNode?: boolean; ctx?: ExtractTypeCtx } = {},
) {
  const project = makeProject(opts.strictNullChecks ?? true);
  const sf = project.createSourceFile("test.ts", code, { overwrite: true });
  const fn = sf.getFunctionOrThrow(fnName);
  const type = fn.getReturnType();
  const tn = opts.useTypeNode ? fn.getReturnTypeNode() : undefined;
  return { type, tn, ty: extractTy(type, tn, opts.ctx) };
}

test("primitives and bigint via both checker Type and syntactic TypeNode", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(getVarType("declare const x: number;", "x", { useTypeNode }).ty, { kind: "int" });
    assert.deepEqual(getVarType("declare const x: bigint;", "x", { useTypeNode }).ty, { kind: "int", big: true });
    assert.deepEqual(getVarType("declare const x: string;", "x", { useTypeNode }).ty, { kind: "string" });
    assert.deepEqual(getVarType("declare const x: boolean;", "x", { useTypeNode }).ty, { kind: "bool" });
    assert.deepEqual(getVarType("declare const x: void;", "x", { useTypeNode }).ty, { kind: "void" });
    assert.deepEqual(getVarType("declare const x: undefined;", "x", { useTypeNode }).ty, { kind: "void" });
    assert.deepEqual(getVarType("declare const x: null;", "x", { useTypeNode }).ty, { kind: "null" });
    assert.deepEqual(getVarType("declare const x: unknown;", "x", { useTypeNode }).ty, { kind: "unknown" });
    assert.deepEqual(getVarType("declare const x: any;", "x", { useTypeNode }).ty, { kind: "unknown" });
  }
});

test("built-in collection aliases (Record, ReadonlyArray, ReadonlySet, ReadonlyMap) resolve before getAliasSymbol()", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType("declare const x: Record<string, number>;", "x", { useTypeNode }).ty,
      { kind: "map", key: { kind: "string" }, value: { kind: "int" } },
    );
    assert.deepEqual(
      getVarType("declare const x: Map<string, bigint>;", "x", { useTypeNode }).ty,
      { kind: "map", key: { kind: "string" }, value: { kind: "int", big: true } },
    );
    assert.deepEqual(
      getVarType("declare const x: ReadonlyMap<number, boolean>;", "x", { useTypeNode }).ty,
      { kind: "map", key: { kind: "int" }, value: { kind: "bool" } },
    );
    assert.deepEqual(
      getVarType("declare const x: ReadonlyArray<string>;", "x", { useTypeNode }).ty,
      { kind: "array", elem: { kind: "string" } },
    );
    assert.deepEqual(
      getVarType("declare const x: readonly number[];", "x", { useTypeNode }).ty,
      { kind: "array", elem: { kind: "int" } },
    );
    assert.deepEqual(
      getVarType("declare const x: Set<string>;", "x", { useTypeNode }).ty,
      { kind: "set", elem: { kind: "string" } },
    );
    assert.deepEqual(
      getVarType("declare const x: ReadonlySet<number>;", "x", { useTypeNode }).ty,
      { kind: "set", elem: { kind: "int" } },
    );
  }
});

test("optional, null, nullish, and non-strict TypeNode nullability preservation", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType("declare const x: number | undefined;", "x", { useTypeNode }).ty,
      { kind: "optional", inner: { kind: "int" } },
    );
    assert.deepEqual(
      getVarType("declare const x: number | null;", "x", { useTypeNode }).ty,
      { kind: "optional", inner: { kind: "int" }, absent: "null" },
    );
    assert.deepEqual(
      getVarType("declare const x: number | null | undefined;", "x", { useTypeNode }).ty,
      { kind: "nullish", inner: { kind: "int" } },
    );
    assert.deepEqual(
      getVarType("declare const x: boolean | undefined;", "x", { useTypeNode }).ty,
      { kind: "optional", inner: { kind: "bool" } },
    );
    assert.deepEqual(
      getVarType("declare const x: boolean | null | undefined;", "x", { useTypeNode }).ty,
      { kind: "nullish", inner: { kind: "bool" } },
    );
    assert.deepEqual(
      getVarType("declare const x: null | undefined;", "x", { useTypeNode }).ty,
      { kind: "nullish", inner: { kind: "void" } },
    );
  }
  // In non-strict mode, TS erases `| null` / `| undefined` from `decl.getType()`,
  // so passing the syntactic TypeNode must preserve nullability.
  assert.deepEqual(
    getVarType("declare const x: string | undefined;", "x", { strictNullChecks: false, useTypeNode: true }).ty,
    { kind: "optional", inner: { kind: "string" } },
  );
  assert.deepEqual(
    getVarType("declare const x: string | null | undefined;", "x", { strictNullChecks: false, useTypeNode: true }).ty,
    { kind: "nullish", inner: { kind: "string" } },
  );
});

test("inline string-literal unions preserve values; named string-union aliases keep alias name", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType('declare const x: "a" | "b";', "x", { useTypeNode }).ty,
      { kind: "string", values: ["a", "b"] },
    );
    assert.deepEqual(
      getVarType('declare const x: "a" | "b" | undefined;', "x", { useTypeNode }).ty,
      { kind: "optional", inner: { kind: "string", values: ["a", "b"] } },
    );
    assert.deepEqual(
      getVarType('type Priority = "low" | "high"; declare const x: Priority;', "x", { useTypeNode }).ty,
      { kind: "user", name: "Priority" },
    );
    assert.deepEqual(
      getVarType('type Priority = "low" | "high"; declare const x: Priority | undefined;', "x", { useTypeNode }).ty,
      { kind: "optional", inner: { kind: "user", name: "Priority" } },
    );
  }
});

test("numeric literal unions and const enums lower to int", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType("declare const x: 0 | 1 | 2;", "x", { useTypeNode }).ty,
      { kind: "int" },
    );
    assert.deepEqual(
      getVarType("declare const x: -1 | 0 | 1 | undefined;", "x", { useTypeNode }).ty,
      { kind: "optional", inner: { kind: "int" } },
    );
  }
  const isConstEnum = (t: Type) =>
    (t.getSymbol()?.getDeclarations() ?? []).some(d => d.getKind() === SyntaxKind.EnumDeclaration);
  assert.deepEqual(
    getVarType("const enum Mode { A = 0, B = 1 } declare const x: Mode;", "x", {
      useTypeNode: false,
      ctx: { isConstEnum },
    }).ty,
    { kind: "int" },
  );
});

test("tuples: empty, homogeneous -> array, heterogeneous -> tuple, readonly tuples", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType("declare const x: [];", "x", { useTypeNode }).ty,
      { kind: "array", elem: { kind: "unknown" } },
    );
    assert.deepEqual(
      getVarType("declare const x: [number, number];", "x", { useTypeNode }).ty,
      { kind: "array", elem: { kind: "int" } },
    );
    assert.deepEqual(
      getVarType("declare const x: [string, number];", "x", { useTypeNode }).ty,
      { kind: "tuple", elems: [{ kind: "string" }, { kind: "int" }] },
    );
    assert.deepEqual(
      getVarType("declare const x: readonly [string, boolean];", "x", { useTypeNode }).ty,
      { kind: "tuple", elems: [{ kind: "string" }, { kind: "bool" }] },
    );
  }
});

test("callable types and TypePredicate return annotations", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType("declare const x: (a: number, b: string) => boolean;", "x", { useTypeNode }).ty,
      { kind: "fn", params: [{ kind: "int" }, { kind: "string" }], result: { kind: "bool" } },
    );
  }
  assert.deepEqual(
    getFnReturn("function f(v: unknown): v is string { return typeof v === 'string'; }", "f", { useTypeNode: true }).ty,
    { kind: "bool" },
  );
});

test("IndexedAccessType resolves through checker Type even when TypeNode is supplied", () => {
  const code = `
    interface Entry { id: number; tags: string[]; mode: "fast" | "slow"; }
    declare const a: Entry["id"];
    declare const b: Entry["tags"][number];
    declare const c: Entry["mode"];
  `;
  assert.deepEqual(getVarType(code, "a", { useTypeNode: true }).ty, { kind: "int" });
  assert.deepEqual(getVarType(code, "b", { useTypeNode: true }).ty, { kind: "string" });
  assert.deepEqual(getVarType(code, "c", { useTypeNode: true }).ty, { kind: "string", values: ["fast", "slow"] });
});

test("synthesized T[] | U array union and Opaque_* multi-member union", () => {
  for (const useTypeNode of [false, true]) {
    const synthDecls: TypeDeclInfo[] = [];
    const res = getVarType(
      "interface Part { text: string; } declare const x: Part[] | string;",
      "x",
      { useTypeNode, ctx: { synthArrayUnions: synthDecls } },
    );
    assert.deepEqual(res.ty, { kind: "user", name: "ArrayOf_Part_Or_string" });
    assert.equal(synthDecls.length, 1);
    assert.equal(synthDecls[0].kind, "discriminated-union");
    assert.equal(synthDecls[0].discriminant, "__isArray__");
    assert.deepEqual(synthDecls[0].variants?.[0].fields[0].type, {
      kind: "array",
      elem: { kind: "user", name: "Part" },
    });
    assert.deepEqual(synthDecls[0].variants?.[1].fields[0].type, { kind: "string" });
  }

  const opaqueDecls: TypeDeclInfo[] = [];
  const opaque = getVarType(
    "interface A { a: number } interface B { b: string } declare const x: A | B | undefined;",
    "x",
    { useTypeNode: false, ctx: { synthArrayUnions: opaqueDecls } },
  );
  assert.deepEqual(opaque.ty, { kind: "optional", inner: { kind: "user", name: "Opaque_A_or_B" } });
  assert.deepEqual(opaqueDecls, [{ name: "Opaque_A_or_B", kind: "opaque" }]);
});

test("collapsed single-variant union recovery via collapsedUnionMap", () => {
  const collapsedUnionMap = new Map([["kind,value", "SingleVariant"]]);
  const res = getVarType(
    'declare const x: { kind: "only"; value: number };',
    "x",
    { useTypeNode: false, ctx: { collapsedUnionMap } },
  );
  assert.deepEqual(res.ty, { kind: "user", name: "SingleVariant" });
});

test("generic bounds erasure via typeParamMap and eraseGenericTy", () => {
  const typeParamMap = new Map([["T", { text: "Base", ty: { kind: "user" as const, name: "Base" } }]]);
  const code = `
    interface Base { id: number }
    function f<T extends Base>(items: T[], opt: T | undefined, pair: [T, number]): T {
      return items[0];
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("test.ts", code, { overwrite: true });
  const fn = sf.getFunctionOrThrow("f");
  const ctx: ExtractTypeCtx = { typeParamMap };
  assert.deepEqual(
    extractTyFromNode(fn.getParameters()[0].getTypeNodeOrThrow(), undefined, ctx),
    { kind: "array", elem: { kind: "user", name: "Base" } },
  );
  assert.deepEqual(
    extractTyFromNode(fn.getParameters()[1].getTypeNodeOrThrow(), undefined, ctx),
    { kind: "optional", inner: { kind: "user", name: "Base" } },
  );
  assert.deepEqual(
    extractTyFromNode(fn.getParameters()[2].getTypeNodeOrThrow(), undefined, ctx),
    { kind: "tuple", elems: [{ kind: "user", name: "Base" }, { kind: "int" }] },
  );
  assert.deepEqual(
    eraseGenericTy({ kind: "map", key: { kind: "string" }, value: { kind: "user", name: "T" } }, typeParamMap),
    { kind: "map", key: { kind: "string" }, value: { kind: "user", name: "Base" } },
  );
});

test("wrapNullability flattens nested optional/nullish without double wrapping", () => {
  const intTy = { kind: "int" as const };
  assert.deepEqual(wrapNullability(intTy, false, false), intTy);
  assert.deepEqual(wrapNullability(intTy, false, true), { kind: "optional", inner: intTy });
  assert.deepEqual(wrapNullability(intTy, true, false), { kind: "optional", inner: intTy, absent: "null" });
  assert.deepEqual(wrapNullability({ kind: "optional", inner: intTy, absent: "null" }, false, true), {
    kind: "nullish",
    inner: intTy,
  });
  assert.deepEqual(wrapNullability({ kind: "optional", inner: intTy }, false, true), {
    kind: "optional",
    inner: intTy,
  });
  assert.deepEqual(wrapNullability({ kind: "nullish", inner: intTy }, true, true), {
    kind: "nullish",
    inner: intTy,
  });
});

test("TypeOperatorTypeNode only unwraps readonly, not keyof", () => {
  const code = `
    interface Config { host: string; port: number; }
    declare const ro: readonly number[];
    declare const key: keyof Config;
  `;
  assert.deepEqual(getVarType(code, "ro", { useTypeNode: true }).ty, {
    kind: "array",
    elem: { kind: "int" },
  });
  // keyof Config must NOT unwrap to { kind: "user", name: "Config" }
  assert.deepEqual(getVarType(code, "key", { useTypeNode: true }).ty, {
    kind: "user",
    name: "keyof Config",
  });
});

test("extractModule populates structured Ty while lsc info --typed preserves Map vs Record tsType", () => {
  const code = `
    export function lookup(m: Map<string, number>, r: Record<string, number>): number {
      const a = m.get("k") ?? 0;
      const b = r["k"] ?? 0;
      return a + b;
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("info-test.ts", code, { overwrite: true });
  const raw = extractModule(sf);
  const fn = raw.functions.find(f => f.name === "lookup");
  assert.ok(fn);
  assert.deepEqual(fn.params[0].type, { kind: "map", key: { kind: "string" }, value: { kind: "int" } });
  assert.deepEqual(fn.params[1].type, { kind: "map", key: { kind: "string" }, value: { kind: "int" } });
  assert.deepEqual(fn.returnTy, { kind: "int" });
  assert.equal(fn.params[0].tsType, "Map<string, number>");
  assert.equal(fn.params[1].tsType, "Record<string, number>");

  // Verify runInfo renders canonical signature from structured Ty
  const tmp = mkdtempSync(path.join(tmpdir(), "lsc-info-test-"));
  try {
    const outPath = path.join(tmp, "info-test.ts.json");
    const origLog = console.log;
    let typedOutput = "";
    try {
      console.log = () => {};
      runInfo(raw, outPath);
      const infoJson = JSON.parse(readFileSync(outPath, "utf-8"));
      assert.equal(infoJson.lookup.sig, "(m: map<string, int>, r: map<string, int>): int");

      const typed = resolveModule(raw);
      console.log = (s: unknown) => { typedOutput += String(s); };
      runTypedInfo(raw, typed, "0.0.0-test", null, DEFAULT_OPTIONS, {});
    } finally {
      console.log = origLog;
    }
    const typedJson = JSON.parse(typedOutput);
    assert.equal(typedJson.functions[0].params[0].tsType, "Map<string, number>");
    assert.equal(typedJson.functions[0].params[1].tsType, "Record<string, number>");
    assert.deepEqual(typedJson.functions[0].params[0].ty, { kind: "map", key: { kind: "string" }, value: { kind: "int" } });
    assert.deepEqual(typedJson.functions[0].params[1].ty, { kind: "map", key: { kind: "string" }, value: { kind: "int" } });
  } finally {
    rmSync(tmp, { recursive: true, force: true });
  }
});

test("inferLambdaParamTypes propagates complex Ty directly without string round-trip", () => {
  const code = `
    type Handler = (
      m: Map<string, number>,
      pair: [string, number],
      optNull: number | null,
      both: number | null | undefined,
    ) => number;
    function applyHandler(
      h: Handler,
      m: Map<string, number>,
      pair: [string, number],
      optNull: number | null,
      both: number | null | undefined,
    ): number {
      return h(m, pair, optNull, both);
    }
    export function caller(
      m: Map<string, number>,
      pair: [string, number],
      optNull: number | null,
      both: number | null | undefined,
    ): number {
      return applyHandler((a, b, c, d) => {
        const v = a.get(b[0]) ?? 0;
        const cVal = c ?? 0;
        const dVal = d ?? 0;
        return v + b[1] + cVal + dVal;
      }, m, pair, optNull, both);
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("lambda-infer.ts", code, { overwrite: true });
  const raw = extractModule(sf);
  const typed = resolveModule(raw);
  const callerFn = typed.functions.find(f => f.name === "caller");
  assert.ok(callerFn);
  const ret = callerFn.body[0];
  assert.equal(ret.kind, "return");
  assert.equal(ret.value?.kind, "call");
  const lam = ret.value.args[0];
  assert.equal(lam.kind, "lambda");
  assert.deepEqual(lam.params.map(p => p.ty), [
    { kind: "map", key: { kind: "string" }, value: { kind: "int" } },
    { kind: "tuple", elems: [{ kind: "string" }, { kind: "int" }] },
    { kind: "optional", inner: { kind: "int" }, absent: "null" },
    { kind: "nullish", inner: { kind: "int" } },
  ]);
});

test("module-level const resolves primitive type alias consistently with tsType", () => {
  const code = `
    type UserId = string;
    const INITIAL_OWNER: UserId = "__initial__";
    export function getOwner(): string {
      return INITIAL_OWNER;
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("const-alias.ts", code, { overwrite: true });
  const raw = extractModule(sf);
  const c = raw.constants.find(x => x.name === "INITIAL_OWNER");
  assert.ok(c);
  assert.equal(c.tsType, "string");
  assert.deepEqual(c.type, { kind: "string" });
  const typed = resolveModule(raw);
  const tc = typed.constants.find(x => x.name === "INITIAL_OWNER");
  assert.ok(tc);
  assert.deepEqual(tc.ty, { kind: "string" });
});

test("nullability parity edge cases across checker Type and TypeNode", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(getVarType("declare const x: void | undefined;", "x", { useTypeNode }).ty, { kind: "void" });
    assert.deepEqual(getVarType("declare const x: void | null;", "x", { useTypeNode }).ty, {
      kind: "nullish",
      inner: { kind: "void" },
    });
    assert.deepEqual(getVarType("declare const x: void | null | undefined;", "x", { useTypeNode }).ty, {
      kind: "nullish",
      inner: { kind: "void" },
    });
    assert.deepEqual(getVarType("declare const x: (null) | undefined;", "x", { useTypeNode }).ty, {
      kind: "nullish",
      inner: { kind: "void" },
    });
    assert.deepEqual(getVarType("declare const x: (undefined) | null;", "x", { useTypeNode }).ty, {
      kind: "nullish",
      inner: { kind: "void" },
    });
    assert.deepEqual(getVarType("declare const x: (null) | null;", "x", { useTypeNode }).ty, { kind: "null" });
    assert.deepEqual(getVarType("declare const x: (undefined) | undefined;", "x", { useTypeNode }).ty, { kind: "void" });
  }
});

test("optional function params, optional tuple elements, and Readonly<T> across Type and TypeNode", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType("declare const x: (a: number, b?: string) => boolean;", "x", { useTypeNode }).ty,
      {
        kind: "fn",
        params: [{ kind: "int" }, { kind: "optional", inner: { kind: "string" } }],
        result: { kind: "bool" },
      },
    );
    assert.deepEqual(
      getVarType("declare const x: [a: number, b?: string];", "x", { useTypeNode }).ty,
      {
        kind: "tuple",
        elems: [{ kind: "int" }, { kind: "optional", inner: { kind: "string" } }],
      },
    );
    assert.deepEqual(
      getVarType("declare const x: [number, string?];", "x", { useTypeNode }).ty,
      {
        kind: "tuple",
        elems: [{ kind: "int" }, { kind: "optional", inner: { kind: "string" } }],
      },
    );
    assert.deepEqual(
      getVarType("interface Foo { a: number } declare const x: Readonly<Foo>;", "x", { useTypeNode }).ty,
      { kind: "user", name: "Foo" },
    );
    assert.deepEqual(
      getVarType("declare const x: Readonly<number[]>;", "x", { useTypeNode }).ty,
      { kind: "array", elem: { kind: "int" } },
    );
  }
});

test("recursive callable interfaces and named callable interfaces preserve name without overflowing", () => {
  for (const useTypeNode of [false, true]) {
    assert.deepEqual(
      getVarType("interface Fix { (x: Fix): void } declare const x: Fix;", "x", { useTypeNode }).ty,
      { kind: "user", name: "Fix" },
    );
    assert.deepEqual(
      getVarType("interface Comparator { (a: number, b: number): boolean } declare const x: Comparator;", "x", { useTypeNode }).ty,
      { kind: "user", name: "Comparator" },
    );
    assert.deepEqual(
      getVarType("type SelfArr = SelfArr[]; declare const x: SelfArr;", "x", { useTypeNode }).ty,
      { kind: "user", name: "SelfArr" },
    );
  }
  // Arrow functions and declared function values still lower to fn types (not "__function" or fn name)
  assert.deepEqual(
    getVarType("const x = (n: number) => n + 1;", "x").ty,
    { kind: "fn", params: [{ kind: "int" }], result: { kind: "int" } },
  );
  assert.deepEqual(
    getVarType("function helper(n: number): boolean { return n > 0; } const x = helper;", "x").ty,
    { kind: "fn", params: [{ kind: "int" }], result: { kind: "bool" } },
  );
});

test("extractModule populates structured Ty on discriminated unions, records, aliases, and classes", () => {
  const code = `
    type Scores = number[];
    interface Box {
      scores: Scores;
      label?: string;
    }
    type Result = { kind: "ok"; value: Box } | { kind: "err"; code: number };
    export class Counter {
      value: number;
      constructor(init: number) { this.value = init; }
      //@ verify
      inc(by: number): number {
        this.value = this.value + by;
        return this.value;
      }
    }
    //@ verify
    export function unwrap(r: Result, fallback: Scores): number {
      if (r.kind === "ok") return r.value.scores.length;
      return r.code + fallback.length;
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("decls-test.ts", code, { overwrite: true });
  const raw = extractModule(sf);
  const scores = raw.typeDecls.find(d => d.name === "Scores");
  assert.ok(scores);
  assert.deepEqual(scores.aliasOfTy, { kind: "array", elem: { kind: "int" } });

  const box = raw.typeDecls.find(d => d.name === "Box");
  assert.ok(box && box.fields);
  assert.deepEqual(box.fields.find(f => f.name === "scores")?.type, { kind: "user", name: "Scores" });
  const labelField = box.fields.find(f => f.name === "label");
  assert.ok(labelField);
  assert.equal(labelField.optionalKey, true);
  assert.deepEqual(labelField.type, { kind: "optional", inner: { kind: "string" } });

  const res = raw.typeDecls.find(d => d.name === "Result");
  assert.ok(res && res.kind === "discriminated-union" && res.variants);
  assert.deepEqual(
    res.variants.find(v => v.name === "ok")?.fields.find(f => f.name === "value")?.type,
    { kind: "user", name: "Box" },
  );

  const cls = raw.classes.find(c => c.name === "Counter");
  assert.ok(cls);
  assert.deepEqual(cls.fields[0].type, { kind: "int" });
  assert.deepEqual(cls.methods[0].params[0].type, { kind: "int" });
  assert.deepEqual(cls.methods[0].returnTy, { kind: "int" });
});

test("brownfield pruning retains synthesized T[] | U declared on an annotated local", () => {
  const code = `
    interface Part { text: string }
    //@ verify
    export function check(p: Part[]): number {
      const x: Part[] | string = p;
      return Array.isArray(x) ? x.length : 0;
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("brownfield-synth.ts", code, { overwrite: true });
  const raw = extractModule(sf);
  const synth = raw.typeDecls.find(d => d.name === "ArrayOf_Part_Or_string");
  assert.ok(synth, "expected ArrayOf_Part_Or_string to be retained under brownfield pruning");
  const fn = raw.functions.find(f => f.name === "check");
  assert.ok(fn);
  const letStmt = fn.body[0];
  assert.equal(letStmt.kind, "let");
  assert.equal(letStmt.tsType, "ArrayOf_Part_Or_string");
  assert.deepEqual(letStmt.type, { kind: "user", name: "ArrayOf_Part_Or_string" });
});

test("bounded generic T[] | U erases T in synthesized datatype name and fields", () => {
  const code = `
    interface Base { id: number }
    export function accept<T extends Base>(x: T[] | string): number {
      return Array.isArray(x) ? x.length : 0;
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("generic-synth.ts", code, { overwrite: true });
  const raw = extractModule(sf);
  const synth = raw.typeDecls.find(d => d.name === "ArrayOf_Base_Or_string");
  assert.ok(synth, `expected ArrayOf_Base_Or_string, found: ${raw.typeDecls.map(d => d.name).join(", ")}`);
  assert.equal(raw.typeDecls.some(d => d.name.includes("ArrayOf_T_")), false);
  assert.deepEqual(synth.variants?.[0].fields[0].type, {
    kind: "array",
    elem: { kind: "user", name: "Base" },
  });
  const fn = raw.functions.find(f => f.name === "accept");
  assert.ok(fn);
  assert.deepEqual(fn.params[0].type, { kind: "user", name: "ArrayOf_Base_Or_string" });
});

test("uninitialized let declarations dispatch default initializers from structured Ty", () => {
  const code = `
    export function defaults(): number {
      let a: number;
      let b: string | undefined;
      let c: number[];
      let d: Map<string, number>;
      let e: Set<string>;
      let f: boolean;
      let g: string;
      a = 1;
      b = undefined;
      c = [];
      d = new Map<string, number>();
      e = new Set<string>();
      f = true;
      g = "";
      return a + c.length + (b ? 1 : 0) + (f ? 1 : 0) + g.length + d.size + e.size;
    }
  `;
  const project = makeProject(true);
  const sf = project.createSourceFile("defaults.ts", code, { overwrite: true });
  const raw = extractModule(sf);
  const fn = raw.functions.find(f => f.name === "defaults");
  assert.ok(fn);
  const lets = fn.body.slice(0, 7);
  assert.equal(lets[0].kind === "let" && lets[0].init.kind, "num");
  assert.equal(lets[1].kind === "let" && lets[1].init.kind === "var" && lets[1].init.name, "undefined");
  assert.equal(lets[2].kind === "let" && lets[2].init.kind, "arrayLiteral");
  assert.equal(lets[3].kind === "let" && lets[3].init.kind === "emptyCollection" && lets[3].init.collectionType, "Map");
  assert.equal(lets[4].kind === "let" && lets[4].init.kind === "emptyCollection" && lets[4].init.collectionType, "Set");
  assert.equal(lets[5].kind === "let" && lets[5].init.kind, "bool");
  assert.equal(lets[6].kind === "let" && lets[6].init.kind, "str");
});

