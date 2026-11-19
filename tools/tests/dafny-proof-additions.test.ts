import { test, mock } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { dafnyCheckDiff } from "../src/dafny-commands.ts";

/** Run the additions-only check on a generated/proof pair, returning its verdict and diagnostics. */
function check(gen: string, proof: string): { ok: boolean; errors: string } {
  const dir = mkdtempSync(join(tmpdir(), "lsc-proof-additions-"));
  const errors = mock.method(console, "error", () => {});
  try {
    const g = join(dir, "file.dfy.gen");
    const p = join(dir, "file.dfy");
    writeFileSync(g, gen);
    writeFileSync(p, proof);
    const ok = dafnyCheckDiff(g, p);
    return { ok, errors: errors.mock.calls.map(c => c.arguments.join(" ")).join("\n") };
  } finally {
    errors.mock.restore();
    rmSync(dir, { recursive: true, force: true });
  }
}

function accepts(gen: string, proof: string): void {
  const { ok, errors } = check(gen, proof);
  assert.equal(ok, true, errors);
}

function rejects(gen: string, proof: string, reason: RegExp, line?: number): void {
  const { ok, errors } = check(gen, proof);
  assert.equal(ok, false, "expected the proof additions to be rejected");
  assert.match(errors, reason);
  if (line !== undefined) assert.match(errors, new RegExp(`file\\.dfy:${line}:`));
}

const method = [
  "method increment(c: int) returns (r: int)",
  "  requires c >= 0",
  "  ensures r > c",
  "{",
  "  r := c + 1;",
  "}",
  "",
].join("\n");

const lemma = [
  "lemma increment_ensures(c: int)",
  "  requires c >= 0",
  "  ensures c + 1 > c",
  "{",
  "}",
  "",
].join("\n");

const fn = [
  "function double(x: int): int",
  "  requires x >= 0",
  "{",
  "  x * 2",
  "}",
  "",
].join("\n");

const predicate = [
  "predicate positive(x: int)",
  "{",
  "  x > 0",
  "}",
  "",
].join("\n");

function insertAfter(text: string, anchor: string, added: string): string {
  const at = text.indexOf(anchor);
  assert.ok(at >= 0, `anchor not found: ${anchor}`);
  const end = text.indexOf("\n", at + anchor.length) + 1;
  return text.slice(0, end) + added + text.slice(end);
}

// Proof-bypass constructs

test("rejects an assume statement added to a generated body", () => {
  rejects(method, insertAfter(method, "r := c + 1;", "  assume r > 0;\n"), /assume/, 6);
});

test("rejects assume {:axiom} added to a generated body", () => {
  rejects(lemma, insertAfter(lemma, "ensures c + 1 > c\n{", "  assume {:axiom} false;\n"), /assume/, 5);
});

test("rejects an {:axiom} helper lemma", () => {
  rejects(lemma, lemma + "lemma {:axiom} Cheat()\n  ensures false\n", /\{:axiom\}/, 6);
});

test("rejects assume and @Axiom in auxiliary declarations", () => {
  rejects(lemma, lemma + "lemma Helper()\n  ensures false\n{\n  assume false;\n}\n", /assume/, 9);
  rejects(lemma, lemma + "@Axiom\nlemma Cheat()\n  ensures false\n", /@Axiom/, 6);
});

test("diagnostics name the proof line and its text", () => {
  const { ok, errors } = check(method, insertAfter(method, "r := c + 1;", "  assume r > 0;\n"));
  assert.equal(ok, false);
  assert.match(errors, /file\.dfy:6: .*assume.*\n?.*assume r > 0;/);
});

test("generated assume and {:axiom} lines remain allowed", () => {
  const gen = "function {:axiom} f(x: int): int\n\nmethod M(t: string) returns (r: int)\n{\n  var c: string := *;\n  assume {:axiom} (|c| <= |t|);\n  return |c|;\n}\n";
  accepts(gen, gen);
  accepts(gen, insertAfter(gen, "assume {:axiom}", "  assert |c| <= |t|;\n"));
});

// Lexical accuracy

for (const [name, text] of [
  ["line comment", "  // assume false; {:axiom} requires false {\n"],
  ["block comment", "  /* assume false; {:axiom} } */\n"],
  ["multi-line block comment", "  /* requires false\n     assume false; {\n  */\n"],
  ["nested block comment", "  /* outer /* assume false; */ still {:axiom} comment } */\n"],
  ["string literal", "  var s := \"assume false; {:axiom} } {\";\n"],
  ["escaped quote in a string", "  var s := \"say \\\"assume\\\" {:axiom}\";\n"],
  ["verbatim string", "  var s := @\"assume \"\"{:axiom}\"\" }\n  requires {\";\n"],
  ["character literals", "  var a, b, c := '{', '}', '\\'';\n"],
] as const) {
  test(`ignores proof-bypass text inside a ${name}`, () => {
    accepts(method, insertAfter(method, "r := c + 1;", text));
  });
}

test("ignores comment text in a generated header", () => {
  accepts(method, insertAfter(method, "requires c >= 0", "  // assume nothing; requires false is just text\n  /* {:axiom} */\n\n"));
});

test("primes in identifiers are not character literals", () => {
  accepts(method, insertAfter(method, "r := c + 1;", "  ghost var r' := r; assert r' == r;\n"));
});

// Added lsc options header

test("rejects an added lsc options line", () => {
  rejects(method, "// lsc options: string-semantics=unicode-scalar\n" + method, /lsc options/, 1);
  rejects(method, insertAfter(method, "r := c + 1;", "// lsc options:\n"), /lsc options/, 6);
});

test("allows a generated lsc options line and indented mentions of it", () => {
  const gen = "// lsc options: string-semantics=javascript-utf16\n" + method;
  accepts(gen, gen);
  accepts(method, insertAfter(method, "r := c + 1;", "  // lsc options: are read from the generated file\n"));
});

// Permitted proof additions

test("allows clauses added to generated headers and bodies for bodyless functions", () => {
  accepts(method, insertAfter(method, "ensures r > c", "  modifies {}\n  ensures r == c + 1\n  requires c < 100\n"));
  const gen = "function f_fun_spec(x: int): int\n\nmethod M() {}\n";
  accepts(gen, insertAfter(gen, "function f_fun_spec", "{\n  x + 1\n}\n"));
});


test("allows top-level auxiliary declarations with their own clauses", () => {
  const aux = [
    "lemma Aux(x: int)",
    "  requires x >= 0",
    "  ensures x * 2 >= x",
    "  decreases x",
    "{",
    "  if x > 0 { Aux(x - 1); }",
    "}",
    "twostate lemma Two() {}",
    "least lemma Least() {}",
    "greatest lemma Greatest() {}",
    "function Sq(x: int): int",
    "  requires x >= 0",
    "  ensures Sq(x) >= 0",
    "{ x * x }",
    "ghost function G(x: int): int { x }",
    "predicate P(x: int) { x > 0 }",
    "ghost predicate Q(s: set<int>)",
    "  reads {}",
    "{ s == {} }",
    "datatype Pair = Pair(a: int, b: int)",
    "codatatype Stream = Cons(head: int, tail: Stream)",
    "type Small = x: int | 0 <= x < 10",
    "newtype Byte = x: int | 0 <= x < 256",
    "const LIMIT: int := 10",
    "",
  ].join("\n");
  accepts(method, method + aux);
  accepts(method, aux + method);
});

test("allows proof statements inside generated method and lemma bodies", () => {
  const body = [
    "  assert r == c + 1;",
    "  increment_ensures(c);",
    "  calc { r; == c + 1; > c; }",
    "  forall x | 0 <= x < 3 ensures x < 3 { }",
    "  reveal double();",
    "  ghost var k := r;",
    "",
  ].join("\n");
  accepts(method, insertAfter(method, "r := c + 1;", body));
  accepts(lemma, insertAfter(lemma, "ensures c + 1 > c\n{", body));
});

test("allows loop invariants inside generated bodies", () => {
  const gen = "method M(n: int)\n{\n  var i := 0;\n  while i < n\n  {\n    i := i + 1;\n  }\n}\n";
  accepts(gen, insertAfter(gen, "while i < n", "    invariant i <= n || n < 0\n    decreases n - i\n"));
});

test("allows an added auxiliary lemma whose lines repeat generated header text", () => {
  accepts(lemma, lemma + lemma.replace("increment_ensures", "increment_ensures_copy"));
});
