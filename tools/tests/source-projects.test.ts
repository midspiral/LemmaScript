import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { SourceProjects } from "../src/source-projects.ts";

const cli = fileURLToPath(new URL("../src/lsc.ts", import.meta.url));
const loader = createRequire(import.meta.url).resolve("tsx");
const tsconfig = JSON.stringify({ compilerOptions: { strict: true, types: [] }, include: ["*.ts"] });
const events = "export interface EventMap { start: number; stop: number; }\n";
const augmentation = 'import "./events";\ndeclare module "./events" { interface EventMap { pause: number; } }\n';
const source = `import type { EventMap } from "./events";
type EventName = keyof EventMap;
export function supported(event: EventName): boolean {
  //@ verify
  //@ ensures \\result
  return event === "start" || event === "stop";
}
`;

function withFiles(files: Record<string, string>, fn: (dir: string) => void) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), "lsc-source-projects-")));
  try {
    for (const [name, text] of Object.entries(files)) {
      const target = join(dir, name);
      mkdirSync(dirname(target), { recursive: true });
      writeFileSync(target, text);
    }
    fn(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function eventNames(file: ReturnType<SourceProjects["load"]>) {
  return file.getTypeAliasOrThrow("EventName").getType().getUnionTypes().map(t => t.getLiteralValue()).sort();
}

test("files in one tsconfig reuse a full project, including ambient augmentations", () => {
  withFiles({
    "tsconfig.json": tsconfig, "events.ts": events, "extra-events.d.ts": augmentation,
    "first.ts": source, "second.ts": source,
  }, dir => {
    const projects = new SourceProjects();
    const first = projects.load(join(dir, "first.ts"));
    const second = projects.load(join(dir, "second.ts"));
    assert.equal(first.getProject(), second.getProject());
    assert.deepEqual(eventNames(first), ["pause", "start", "stop"]);
    assert.deepEqual(eventNames(second), ["pause", "start", "stop"]);
    assert.equal(projects.load(join(dir, "first.ts")), first);
    assert.notEqual(new SourceProjects().load(join(dir, "first.ts")).getProject(), first.getProject());
  });
});

test("distinct tsconfigs with identical options keep their global types separate", () => {
  withFiles({
    "one/tsconfig.json": tsconfig, "two/tsconfig.json": tsconfig,
    "one/globals.d.ts": "interface EventMap { start: number; stop: number; }",
    "two/globals.d.ts": "interface EventMap { pause: number; resume: number; }",
    "one/source.ts": "export type EventName = keyof EventMap;",
    "two/source.ts": "export type EventName = keyof EventMap;",
  }, dir => {
    const projects = new SourceProjects();
    const one = projects.load(join(dir, "one/source.ts"));
    const two = projects.load(join(dir, "two/source.ts"));
    assert.notEqual(one.getProject(), two.getProject());
    assert.deepEqual(eventNames(one), ["start", "stop"]);
    assert.deepEqual(eventNames(two), ["pause", "resume"]);
    assert.equal(projects.load(join(dir, "one/source.ts")), one);
  });
});

test("files without a tsconfig do not share global declarations", () => {
  withFiles({
    "one.ts": "interface EventMap { start: number; stop: number; }\ntype EventName = keyof EventMap;",
    "two.ts": "interface EventMap { pause: number; resume: number; }\ntype EventName = keyof EventMap;",
  }, dir => {
    const projects = new SourceProjects();
    const one = projects.load(join(dir, "one.ts"));
    const two = projects.load(join(dir, "two.ts"));
    assert.notEqual(one.getProject(), two.getProject());
    assert.deepEqual(eventNames(one), ["start", "stop"]);
    assert.deepEqual(eventNames(two), ["pause", "resume"]);
  });
});

for (const excludedFirst of [false, true]) {
  test(`an excluded entry cannot add augmentations to the shared project (excluded first: ${excludedFirst})`, () => {
    withFiles({
      "tsconfig.json": JSON.stringify({ compilerOptions: { strict: true, types: [] }, files: ["source.ts"] }),
      "events.ts": events, "source.ts": source,
      "excluded.ts": augmentation + source,
    }, dir => {
      const projects = new SourceProjects();
      const loadIncluded = () => projects.load(join(dir, "source.ts"));
      const loadExcluded = () => projects.load(join(dir, "excluded.ts"));
      const first = excludedFirst ? loadExcluded() : loadIncluded();
      const second = excludedFirst ? loadIncluded() : loadExcluded();
      const included = excludedFirst ? second : first;
      const excluded = excludedFirst ? first : second;
      assert.notEqual(included.getProject(), excluded.getProject());
      assert.deepEqual(eventNames(excluded), ["pause", "start", "stop"]);
      assert.deepEqual(eventNames(included), ["start", "stop"]);
      assert.equal(loadIncluded(), included);
      assert.deepEqual(eventNames(loadIncluded()), ["start", "stop"]);
    });
  });
}

function runCli(dir: string, args: string[]) {
  const result = spawnSync(process.execPath, ["--import", loader, cli, ...args], {
    cwd: dir, env: { ...process.env, LSC_RUN_LOG: "false" }, encoding: "utf8", timeout: 30_000,
  });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stdout + result.stderr);
}

for (const backend of ["dafny", "lean"]) {
  test(`${backend} batch output matches separate runs across reused projects and per-file options`, () => {
    const utf16 = backend === "dafny" ? "//@ option string-semantics javascript-utf16\n" : "";
    withFiles({
      "tsconfig.json": tsconfig, "events.ts": events, "extra-events.d.ts": augmentation,
      "source.ts": source,
      "globals.ts": "function globalSize(value: string): number { return value.length; }\n",
      "caller.ts": 'export function read(): number { return globalSize("a"); }\n',
      "local.ts": utf16 + "//@ option dafny-library local\nexport function size(value: string): number { return value.length; }\n",
      "nested/tsconfig.json": tsconfig,
      "nested/globals.d.ts": "interface EventMap { pause: number; resume: number; }\n",
      "nested/source.ts": `type EventName = keyof EventMap;
export function supported(event: EventName): boolean { return event === "pause"; }
`,
    }, dir => {
      const entries = ["caller.ts", "source.ts", "nested/source.ts", "local.ts", "source.ts"];
      const expected = new Map<string, string>();
      const extensions = backend === "dafny" ? [".dfy.gen"] : [".types.lean", ".def.lean"];
      for (const entry of new Set(entries)) {
        runCli(dir, ["gen", `--backend=${backend}`, entry]);
        for (const ext of extensions) {
          const artifact = join(dir, entry.replace(/\.ts$/, ext));
          if (existsSync(artifact)) expected.set(artifact, readFileSync(artifact, "utf8"));
        }
      }
      writeFileSync(join(dir, "LemmaScript-files.txt"), entries.join("\n") + "\n");
      runCli(dir, ["gen", `--backend=${backend}`]);
      for (const [artifact, text] of expected) {
        assert.equal(readFileSync(artifact, "utf8"), text, artifact);
      }
      if (backend === "dafny") {
        assert.match(readFileSync(join(dir, "source.dfy.gen"), "utf8"), /datatype EventName = start \| stop \| pause/);
        assert.match(readFileSync(join(dir, "local.dfy.gen"), "utf8"), /string-semantics=javascript-utf16/);
      }
    });
  });
}
