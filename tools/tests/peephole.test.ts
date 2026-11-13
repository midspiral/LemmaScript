import { test } from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { peepholeModule } from "../src/peephole.ts";
import { pCtor, type Expr, type Module } from "../src/ir.ts";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit.ts";

const variable = (name: string): Expr => ({ kind: "var", name });
const identity = (name: string): Expr => ({
  kind: "if", cond: variable(name),
  then: { kind: "bool", value: true }, else: { kind: "bool", value: false },
});

function optimize(expr: Expr, backend: "dafny" | "lean" = "dafny"): Expr {
  const mod: Module = {
    comment: "", imports: [], options: [],
    decls: [{ kind: "const", name: "result", type: { kind: "unknown" }, value: expr }],
  };
  const result = peepholeModule(mod, backend).decls[0];
  assert.ok(result.kind === "const");
  return result.value;
}

test("Dafny simplifies multiple and nested constructor arguments like direct expressions", () => {
  const empty: Expr = { kind: "constructor", name: "none", type: "Option", args: [] };
  const unchanged: Expr = { kind: "binop", op: "+", left: variable("x"), right: { kind: "num", value: 1 } };
  const input: Expr = {
    kind: "constructor", name: "bundle", type: "Bundle",
    args: [
      identity("p"), empty,
      { kind: "constructor", name: "some", type: "Option", args: [identity("q")] },
      { kind: "arrayLiteral", elems: [identity("r"), unchanged] },
    ],
  };
  const original = structuredClone(input);
  assert.deepEqual(optimize(identity("p")), variable("p"));
  assert.deepEqual(optimize(input), {
    kind: "constructor", name: "bundle", type: "Bundle",
    args: [
      variable("p"), empty,
      { kind: "constructor", name: "some", type: "Option", args: [variable("q")] },
      { kind: "arrayLiteral", elems: [variable("r"), unchanged] },
    ],
  });
  assert.deepEqual(input, original, "the pass must not mutate its input");
});

const mapType = { kind: "map", key: { kind: "string" }, value: { kind: "int" } } as const;
const get: Expr = {
  kind: "methodCall", obj: variable("values"), objTy: mapType, method: "get",
  args: [{ kind: "str", value: "key" }], monadic: false,
};
const lookup: Expr = {
  kind: "match", scrutinee: get, arms: [
    { pattern: pCtor("none"), body: { kind: "num", value: 0 } },
    {
      pattern: pCtor("some", "value"),
      body: { kind: "let", name: "value", value: { kind: "num", value: 7 }, body: variable("value") },
    },
  ],
};
const rewrittenLookup: Expr = {
  kind: "if",
  cond: {
    kind: "methodCall", obj: variable("values"), objTy: mapType, method: "has",
    args: [{ kind: "str", value: "key" }], monadic: false,
  },
  then: {
    kind: "let", name: "value",
    value: { kind: "index", arr: variable("values"), idx: { kind: "str", value: "key" } },
    body: { kind: "let", name: "value", value: { kind: "num", value: 7 }, body: variable("value") },
  },
  else: { kind: "num", value: 0 },
};

for (const backend of ["dafny", "lean"] as const) {
  test(`${backend} rewrites nested map lookups with their existing binders and shadowing`, () => {
    const input: Expr = {
      kind: "constructor", name: "box", type: "Box", args: [
        lookup,
        { kind: "mapLiteral", entries: [
          { key: lookup, value: { kind: "constructor", name: "some", type: "Option", args: [lookup] } },
        ] },
      ],
    };
    assert.deepEqual(optimize(input, backend), {
      kind: "constructor", name: "box", type: "Box", args: [
        rewrittenLookup,
        { kind: "mapLiteral", entries: [
          { key: rewrittenLookup, value: { kind: "constructor", name: "some", type: "Option", args: [rewrittenLookup] } },
        ] },
      ],
    });
  });

  test(`${backend} keeps a map-get binding used inside a nested match arm`, () => {
    const retained: Expr = {
      kind: "let", name: "cached", value: get,
      body: { kind: "match", scrutinee: variable("cached"), arms: [
        {
          pattern: pCtor("some", "value"),
          body: { kind: "constructor", name: "pair", args: [variable("value"), variable("cached")] },
        },
        { pattern: pCtor("none"), body: { kind: "constructor", name: "empty", args: [] } },
      ] },
    };
    const input: Expr = {
      kind: "mapLiteral", entries: [
        { key: retained, value: { kind: "constructor", name: "box", args: [retained] } },
      ],
    };
    assert.deepEqual(optimize(input, backend), input);
  });
}

test("Lean leaves Dafny-only Boolean rules disabled at every new child position", () => {
  const input: Expr = {
    kind: "constructor", name: "box", args: [
      identity("p"),
      { kind: "mapLiteral", entries: [{ key: identity("q"), value: identity("r") }] },
    ],
  };
  assert.deepEqual(optimize(input, "lean"), input);
  assert.deepEqual(optimize(input, "dafny"), {
    kind: "constructor", name: "box", args: [
      variable("p"),
      { kind: "mapLiteral", entries: [{ key: variable("q"), value: variable("r") }] },
    ],
  });
  assert.deepEqual(optimize(input, "lean"), input, "backend selection must not leak between calls");
});

test("Dafny simplifies all map keys and values recursively without reordering entries", () => {
  const unchanged: Expr = { kind: "app", fn: "unchanged", args: [variable("x")] };
  const input: Expr = {
    kind: "mapLiteral", entries: [
      { key: identity("p"), value: identity("q") },
      {
        key: { kind: "unop", op: "¬", expr: identity("r") },
        value: { kind: "constructor", name: "some", args: [identity("s")] },
      },
      {
        key: { kind: "str", value: "nested" },
        value: { kind: "mapLiteral", entries: [{ key: identity("t"), value: identity("u") }] },
      },
      { key: { kind: "str", value: "untouched" }, value: unchanged },
    ],
  };
  const original = structuredClone(input);
  assert.deepEqual(optimize(input), {
    kind: "mapLiteral", entries: [
      { key: variable("p"), value: variable("q") },
      {
        key: { kind: "unop", op: "¬", expr: variable("r") },
        value: { kind: "constructor", name: "some", args: [variable("s")] },
      },
      {
        key: { kind: "str", value: "nested" },
        value: { kind: "mapLiteral", entries: [{ key: variable("t"), value: variable("u") }] },
      },
      { key: { kind: "str", value: "untouched" }, value: unchanged },
    ],
  });
  assert.deepEqual(optimize({ kind: "mapLiteral", entries: [] }), { kind: "mapLiteral", entries: [] });
  assert.deepEqual(input, original, "the pass must not mutate its input");
});

function sourceModule(name: string, backend: "dafny" | "lean"): Module {
  const project = new Project({ compilerOptions: {
    strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true,
  } });
  const source = project.addSourceFileAtPath(fileURLToPath(new URL(`../fixtures/${name}.ts`, import.meta.url)));
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), [], "valid TypeScript");
  const typed = narrowModule(resolveModule(extractModule(source)));
  const { typesFile, defFile } = backend === "dafny" ? transformModuleDafny(typed) : transformModuleLean(typed);
  return { ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] };
}

function definition(mod: Module, name: string): Expr {
  const decl = mod.decls.flatMap(d => d.kind === "namespace" ? d.decls : [d])
    .find(d => d.kind === "def" && d.name === name);
  assert.ok(decl?.kind === "def", name);
  return decl.body;
}

for (const backend of ["dafny", "lean"] as const) {
  test(`${backend} optimizes source optional constructors through generation`, () => {
    const raw = sourceModule("peephole-children", backend);
    const flag = definition(raw, "optionalFlag");
    const lookup = definition(raw, "optionalLookup");
    assert.ok(flag.kind === "if" && flag.then.kind === "constructor");
    assert.ok(lookup.kind === "if" && lookup.then.kind === "constructor");
    assert.equal(flag.then.args[0].kind, "if", "lowering produces a Boolean expression inside Some");
    assert.equal(lookup.then.args[0].kind, "match", "lowering produces a map-get match inside Some");

    const optimized = peepholeModule(raw, backend);
    const expectedFlag: Expr = {
      kind: "if", cond: variable("enabled"),
      then: { kind: "constructor", name: "some", type: "Option",
        args: [backend === "dafny" ? variable("flag") : identity("flag")] },
      else: { kind: "constructor", name: "none", type: "Option", args: [] },
    };
    assert.deepEqual(definition(optimized, "optionalFlag"), expectedFlag);
    const optimizedLookup = definition(optimized, "optionalLookup");
    assert.ok(optimizedLookup.kind === "if" && optimizedLookup.then.kind === "constructor");
    const child = optimizedLookup.then.args[0];
    assert.ok(child.kind === "if" && child.cond.kind === "methodCall" && child.then.kind === "let");
    assert.equal(child.cond.method, "has");
    assert.equal(child.then.value.kind, "index");
    assert.deepEqual(child.then.body, variable(child.then.name), "the match binder still denotes the indexed value");

    if (backend === "dafny") {
      const text = emitDafnyFile(optimized);
      assert.match(text, /Option\.Some\(flag\)/);
      assert.match(text, /Option\.Some\(\(if \(key in values\) then/);
      assert.doesNotMatch(text, /match /);
    } else {
      resetLeanModule();
      const text = emitLeanFile(optimized);
      assert.match(text, /Option\.some \(if flag then true else false\)/);
      assert.match(text, /Option\.some \(if values\.contains key then/);
      assert.doesNotMatch(text, /match /);
    }
  });
}

test("Dafny optimizes source record-map values and retains literal key order", () => {
  const raw = sourceModule("peephole-map-entries", "dafny");
  const flags = definition(raw, "flags");
  assert.ok(flags.kind === "mapLiteral");
  assert.deepEqual(flags.entries.map(e => e.key), [{ kind: "str", value: "first" }, { kind: "str", value: "second" }]);
  assert.ok(flags.entries.every(e => e.value.kind === "if"));
  const optimized = peepholeModule(raw, "dafny");
  assert.deepEqual(definition(optimized, "flags"), {
    kind: "mapLiteral", entries: [
      { key: { kind: "str", value: "first" }, value: variable("first") },
      { key: { kind: "str", value: "second" }, value: variable("second") },
    ],
  });
  const text = emitDafnyFile(optimized);
  assert.match(text, /map\["first" := first, "second" := second\]/);
  assert.match(text, /map\["value" := \(if \(key in values\) then/);
  assert.doesNotMatch(text, /match /);
});
