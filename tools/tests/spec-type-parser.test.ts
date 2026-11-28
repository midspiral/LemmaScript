import { test } from "node:test";
import assert from "node:assert/strict";
import { readdirSync, readFileSync, statSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { join, resolve } from "node:path";
import { parseSpecType } from "../src/spec-type.ts";
import { parseSpecTypeKernel, tokenizeSpecType, isOptionalSpecTy } from "../src/spec-type-parser.ts";
import { parseTsType } from "../src/types.ts";

const REPO_ROOT = resolve(import.meta.dirname, "../..");

function collectTsFiles(dir: string): string[] {
  const out: string[] = [];
  for (const entry of readdirSync(dir)) {
    const full = join(dir, entry);
    const st = statSync(full);
    if (st.isDirectory()) {
      out.push(...collectTsFiles(full));
    } else if (entry.endsWith(".ts") && !entry.endsWith(".d.ts")) {
      out.push(full);
    }
  }
  return out;
}

function mineSpecTypesFromDir(dir: string, found: Set<string>): void {
  const files = collectTsFiles(dir);
  for (const file of files) {
    const src = readFileSync(file, "utf8");
    for (const line of src.split("\n")) {
      const idx = line.indexOf("//@");
      if (idx === -1) continue;
      const before = line.slice(0, idx).trim();
      if (before.startsWith("//")) continue;
      const body = line.slice(idx + 3).trim();

      // Trailing field/param override: `field: T; //@ type <Type>`
      // Standalone override: `//@ type <name> <Type>` (skip Dafny trait constraints like `//@ type T (==)`)
      const typeMatch = body.match(/^type\s+(.+)$/);
      if (typeMatch) {
        const rest = typeMatch[1].trim();
        if (before.length > 0) {
          if (rest !== "(==)") found.add(rest);
        } else {
          const named = rest.match(/^(?:\\result|[A-Za-z_$][\w$]*)\s+(.+)$/);
          if (named) {
            const tyText = named[1].trim();
            if (tyText !== "(==)" && !tyText.startsWith("(")) {
              found.add(tyText);
            }
          }
        }
      }

      // //@ havoc : <T>
      const havocMatch = body.match(/^havoc\s*:\s*(.+)$/);
      if (havocMatch) found.add(havocMatch[1].trim());

      // //@ ghost (let|const) name: <T> = ...
      const ghostMatch = body.match(/^ghost\s+(?:let|const)\s+[A-Za-z_$][\w$]*\s*:\s*([^=]+?)\s*=/);
      if (ghostMatch) found.add(ghostMatch[1].trim());

      // //@ declare-type Name = <T>
      const declAlias = body.match(/^declare-type\s+[A-Za-z_$][\w$]*\s*=\s*(.+)$/);
      if (declAlias) {
        const rhs = declAlias[1].trim();
        // Skip string-literal enum declarations handled as enum in extract.ts
        if (!/^"[^"]*"(\s*\|\s*"[^"]*")+$/.test(rhs)) {
          found.add(rhs);
        }
      }

      // //@ declare-type Name { field: T; ... }
      const declRec = body.match(/^declare-type\s+[A-Za-z_$][\w$]*\s*\{([^}]+)\}$/);
      if (declRec) {
        for (const part of declRec[1].split(/[;,]/)) {
          const fm = part.trim().match(/^[A-Za-z_$][\w$]*\??\s*:\s*(.+)$/);
          if (fm) found.add(fm[1].trim());
        }
      }

      // Quantifier binders: forall(x: T, body) or exists(x: T, body)
      for (const qm of body.matchAll(/\b(?:forall|exists)\(\s*[A-Za-z_$][\w$]*\s*:\s*([^,)]+)\s*,/g)) {
        found.add(qm[1].trim());
      }

      // Empty collection constructors in specs: new Set<T>(), new Map<K, V>()
      for (const sm of body.matchAll(/\bnew\s+(?:Set|Map)<([^>]+)>\(\)/g)) {
        for (const arg of sm[1].split(",")) {
          if (arg.trim()) found.add(arg.trim());
        }
      }
    }
  }
}

test("differential: parseSpecType agrees with parseTsType across all //@ type annotations in examples/ and tools/fixtures/", () => {
  const mined = new Set<string>();
  mineSpecTypesFromDir(join(REPO_ROOT, "examples"), mined);
  mineSpecTypesFromDir(join(REPO_ROOT, "tools/fixtures"), mined);
  assert.ok(mined.size >= 10, `expected at least 10 mined spec type strings, found ${mined.size}`);
  for (const text of mined) {
    assert.deepStrictEqual(
      parseSpecType(text),
      parseTsType(text),
      `mismatch on mined spec type: ${JSON.stringify(text)}`,
    );
  }
});

test("differential: parseSpecType agrees with parseTsType across comprehensive synthetic grammar matrix", () => {
  const cases = [
    // Primitives & LemmaScript spec keywords
    "number",
    "bigint",
    "boolean",
    "string",
    "void",
    "null",
    "undefined",
    "unknown",
    "any",
    "nat",
    "real",
    "int",
    // Arrays & readonly
    "number[]",
    "string[][]",
    "readonly number[]",
    "readonly (number | null)[]",
    "Array<number>",
    "ReadonlyArray<string>",
    "Array<Array<boolean>>",
    // Sets, Maps, Records
    "Set<string>",
    "ReadonlySet<number>",
    "Map<string, number>",
    "ReadonlyMap<string, Set<number[]>>",
    "Record<string, number>",
    "Record<string, Map<number, Set<string>>>",
    // Tuples (empty, single, homogeneous, heterogeneous, readonly, trailing comma)
    "[]",
    "[number]",
    "[number, number]",
    "[string, string, string]",
    "[string, number]",
    "[boolean, number, string]",
    "readonly [number, string]",
    "[number, string,]",
    "readonly [number, number]",
    // Unions & nullability normalization/flattening
    "number | undefined",
    "undefined | number",
    "number | null",
    "null | number",
    "number | null | undefined",
    "undefined | number | null",
    "(number | null) | undefined",
    "(number | undefined) | null",
    "(number | null) | null",
    "(number | undefined) | undefined",
    "(number | null | undefined) | undefined",
    "null | undefined",
    "undefined | null",
    "true | false",
    "true | false | undefined",
    "true | false | null",
    "true | false | null | undefined",
    '"pending" | "done"',
    "'a' | 'b' | null",
    '"a" | "b" | undefined',
    '"a" | "b" | null | undefined',
    "1 | 2 | 3",
    "0 | -1 | 1 | null",
    "Foo | Bar",
    "Foo | Bar | undefined",
    "Foo | Bar | null",
    "Foo | Bar | null | undefined",
    '| "a" | "b"',
    // Literals
    "true",
    "false",
    "42",
    "-7",
    '"hello"',
    // Function types
    "() => void",
    "() => number",
    "(x: number) => boolean",
    "(a: string, b: number) => void",
    "(a: string, b?: number) => boolean",
    "((x: number) => number) | null",
    "(cb: (x: number) => boolean) => void",
    "(a: Map<string, number>, b: [string, number]) => Set<string>",
    // User / generic / dotted names & parens
    "RunnerView",
    "Box<number>",
    "Result<string, Error>",
    "Foo.Bar",
    "Foo.Bar<number>",
    "Promise<Complex>",
    "(number)",
    "((string))",
    "((number | null))[]",
  ];

  for (const text of cases) {
    assert.deepStrictEqual(
      parseSpecType(text),
      parseTsType(text),
      `mismatch on synthetic spec type: ${JSON.stringify(text)}`,
    );
  }
});

test("parseSpecType handles named tuple elements and string literal escapes", () => {
  assert.deepStrictEqual(parseSpecType("[x: number, y: number]"), {
    kind: "array",
    elem: { kind: "int" },
  });
  assert.deepStrictEqual(parseSpecType("[key: string, value: number]"), {
    kind: "tuple",
    elems: [{ kind: "string" }, { kind: "int" }],
  });
  assert.deepStrictEqual(parseSpecType('"a\\nb" | "c\\"d"'), {
    kind: "string",
    values: ["a\nb", 'c"d'],
  });
});

test("parseSpecType fails closed with descriptive errors on malformed input", () => {
  const malformed = [
    "",
    "   ",
    "Map<string, number",
    "Set<number",
    "Set<>",
    "Map<string, >",
    "Array<number, string>",
    "ReadonlyArray<number, string>",
    "Set<number, string>",
    "Map<string>",
    "Map<string, number, boolean>",
    "Record<string>",
    "Record<string, number, boolean>",
    "(number | string",
    "(x: number => void",
    "[number, string",
    '"unterminated',
    "'unterminated",
    "number string",
    "number]",
    "number>",
    "number)",
    "number |",
    "number | | string",
    "|",
    "readonly",
    "-foo",
    "@invalid",
    "number & string",
    "Foo.",
    "() =>",
  ];

  for (const bad of malformed) {
    assert.throws(
      () => parseSpecType(bad),
      (err: unknown) => err instanceof Error && err.message.includes("Invalid spec type annotation"),
      `expected parseSpecType(${JSON.stringify(bad)}) to fail closed`,
    );
  }
});

test("verified core invariants: nullability flattening and full token consumption", () => {
  const nested = parseSpecTypeKernel("(number | null) | undefined");
  assert.equal(nested.kind, "ok");
  assert.equal(nested.ty.kind, "nullish");
  assert.equal(isOptionalSpecTy(nested.ty.inner), false);

  const toks = tokenizeSpecType("(number | null) | undefined");
  assert.equal(toks.kind, "ok");
  assert.equal(nested.nextPos, toks.tokens.length);
});

test("spec-type-parser.ts and spec-type.ts do not import ts-morph or typescript", () => {
  for (const rel of ["tools/src/spec-type-parser.ts", "tools/src/spec-type.ts"]) {
    const src = readFileSync(join(REPO_ROOT, rel), "utf8");
    assert.doesNotMatch(src, /from\s+["']ts-morph["']/, `${rel} must not import ts-morph`);
    assert.doesNotMatch(src, /from\s+["']typescript["']/, `${rel} must not import typescript`);
  }
});

test("self-verification: spec-type-parser.ts is in LemmaScript-files.txt, axiom-free, and passes lsc check --backend=dafny", () => {
  const manifest = readFileSync(join(REPO_ROOT, "LemmaScript-files.txt"), "utf8")
    .split("\n")
    .map(l => l.trim())
    .filter(l => l.length > 0 && !l.startsWith("#"));
  assert.ok(manifest.includes("tools/src/spec-type-parser.ts"), "spec-type-parser.ts must be registered in LemmaScript-files.txt");

  const dfy = readFileSync(join(REPO_ROOT, "tools/src/spec-type-parser.dfy"), "utf8");
  assert.doesNotMatch(dfy, /\bassume\b/, "spec-type-parser.dfy must not contain assume");
  assert.doesNotMatch(dfy, /\bhavoc\b/, "spec-type-parser.dfy must not contain havoc");
  assert.doesNotMatch(dfy, /\{:axiom\}/, "spec-type-parser.dfy must not contain {:axiom}");

  const out = execFileSync(
    process.execPath,
    [join(REPO_ROOT, "tools/dist/lsc.js"), "check", "--backend=dafny", join(REPO_ROOT, "tools/src/spec-type-parser.ts")],
    { cwd: REPO_ROOT, encoding: "utf8" },
  );
  assert.match(out, /0 errors/, `expected Dafny verification with 0 errors, got:\n${out}`);
});
