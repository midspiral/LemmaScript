/**
 * LemmaScript project configuration.
 *
 * Config is discovered per source file, validated from one registry, then
 * layered with eligible file directives before consumers see a resolved set.
 * Filesystem policy stays here/lsc.ts; extractors and emitters receive options.
 */

import { existsSync, readFileSync } from "fs";
import path from "path";

export const OPTION_SPECS = {
  "extern-default": {
    type: "enum",
    values: ["pure", "impure"],
    default: "pure",
    fileOverride: true,
    description: "Default model for externs without //@ pure or //@ impure.",
  },
  "safe-slice": {
    type: "boolean",
    default: false,
    fileOverride: true,
    directiveAliases: ["safe-slice"],
    description: "Use JavaScript-clamping semantics for two-argument array slice.",
  },
  "proof-dir": {
    type: "path",
    default: null,
    fileOverride: false,
    description: "Directory for Dafny artifacts, relative to lemmascript.json.",
  },
} as const;

type OptionSpecs = typeof OPTION_SPECS;
type OptionValue<S> =
  S extends { type: "boolean" } ? boolean :
  S extends { type: "enum"; values: readonly (infer V extends string)[] } ? V :
  S extends { type: "path" } ? string | null :
  never;

export type LscOptions = {
  readonly [K in keyof OptionSpecs]: OptionValue<OptionSpecs[K]>;
};
export type ExplicitOptions = Partial<LscOptions>;

export const DEFAULT_OPTIONS = Object.freeze(Object.fromEntries(
  Object.entries(OPTION_SPECS).map(([key, spec]) => [key, spec.default]),
)) as LscOptions;

type AnyOptionSpec = OptionSpecs[keyof OptionSpecs];
const KNOWN_KEYS = Object.keys(OPTION_SPECS) as (keyof OptionSpecs)[];
const CONFIG_CACHE = new Map<string, ExplicitOptions>();

function fail(source: string, message: string): never {
  throw new Error(`${source}: ${message}`);
}

function isKnownKey(key: string): key is keyof OptionSpecs {
  return Object.hasOwn(OPTION_SPECS, key);
}

function parseValue(key: keyof OptionSpecs, raw: unknown, source: string): LscOptions[typeof key] {
  const spec = OPTION_SPECS[key] as AnyOptionSpec;
  if (spec.type === "boolean") {
    if (typeof raw !== "boolean") fail(source, `option '${key}' must be true or false`);
    return raw as LscOptions[typeof key];
  }
  if (spec.type === "enum") {
    if (typeof raw !== "string" || !(spec.values as readonly string[]).includes(raw)) {
      fail(source, `option '${key}' must be one of: ${spec.values.join(", ")}`);
    }
    return raw as LscOptions[typeof key];
  }
  if (typeof raw !== "string" || raw.trim().length === 0) {
    fail(source, `option '${key}' must be a non-empty relative path`);
  }
  if (path.isAbsolute(raw)) fail(source, `option '${key}' must be relative to lemmascript.json`);
  return raw as LscOptions[typeof key];
}

/** Validate a parsed lemmascript.json object, returning only explicitly set keys. */
export function validateOptions(raw: unknown, source: string): ExplicitOptions {
  if (raw === null || typeof raw !== "object" || Array.isArray(raw)) {
    fail(source, "expected a JSON object");
  }
  const out: Record<string, unknown> = {};
  for (const [key, value] of Object.entries(raw as Record<string, unknown>)) {
    if (key === "$schema") continue;
    if (!isKnownKey(key)) {
      fail(source, `unknown option '${key}' (known options: ${KNOWN_KEYS.join(", ")})`);
    }
    out[key] = parseValue(key, value, source);
  }
  return out as ExplicitOptions;
}

/** Last line in the leading-comment region. Directives after code are errors. */
function leadingCommentLineCount(lines: string[]): number {
  let inBlock = false;
  for (let i = 0; i < lines.length; i++) {
    let rest = lines[i];
    if (i === 0) rest = rest.replace(/^\uFEFF/, "");
    if (i === 0 && rest.startsWith("#!")) continue;
    while (true) {
      rest = rest.trimStart();
      if (inBlock) {
        const end = rest.indexOf("*/");
        if (end < 0) break;
        inBlock = false;
        rest = rest.slice(end + 2);
        continue;
      }
      if (rest.length === 0 || rest.startsWith("//")) break;
      if (rest.startsWith("/*")) {
        const end = rest.indexOf("*/", 2);
        if (end < 0) { inBlock = true; break; }
        rest = rest.slice(end + 2);
        continue;
      }
      return i;
    }
  }
  return lines.length;
}

function parseDirectiveValue(key: keyof OptionSpecs, text: string, source: string): LscOptions[typeof key] {
  const spec = OPTION_SPECS[key] as AnyOptionSpec;
  if (spec.type === "boolean") {
    if (text !== "true" && text !== "false") fail(source, `option '${key}' must be true or false`);
    return (text === "true") as LscOptions[typeof key];
  }
  if (spec.type === "enum") return parseValue(key, text, source);
  // Config-only today, but keep the diagnostic precise if a future path is
  // made file-overridable.
  return parseValue(key, text, source);
}

/** Parse top-of-file `//@ option key value` directives and legacy aliases. */
export function parseFileOptions(sourceText: string, source: string): ExplicitOptions {
  const lines = sourceText.split(/\r?\n/);
  const leadingLines = leadingCommentLineCount(lines);
  const seen = new Map<keyof OptionSpecs, number>();
  const out: Record<string, unknown> = {};

  const setOption = (key: keyof OptionSpecs, value: LscOptions[typeof key], line: number): void => {
    const previous = seen.get(key);
    if (previous !== undefined) {
      fail(`${source}:${line}`, `duplicate option '${key}' (first set on line ${previous})`);
    }
    seen.set(key, line);
    out[key] = value;
  };

  const parseLine = (lineText: string, index: number, inLeadingRegion: boolean): void => {
    const line = index + 1;
    const optionMatch = lineText.match(/^[ \t]*\/\/@[ \t]+option(?:[ \t]+(.*?))?[ \t]*$/);
    if (optionMatch) {
      if (!inLeadingRegion) fail(`${source}:${line}`, "//@ option directives must appear before the first source statement");
      const parts = (optionMatch[1] ?? "").trim().split(/\s+/).filter(Boolean);
      if (parts.length !== 2) fail(`${source}:${line}`, "expected //@ option <key> <value>");
      const [rawKey, rawValue] = parts;
      if (!isKnownKey(rawKey)) {
        fail(`${source}:${line}`, `unknown option '${rawKey}' (known options: ${KNOWN_KEYS.join(", ")})`);
      }
      const spec = OPTION_SPECS[rawKey];
      if (!spec.fileOverride) fail(`${source}:${line}`, `option '${rawKey}' is config-only`);
      setOption(rawKey, parseDirectiveValue(rawKey, rawValue, `${source}:${line}`), line);
      return;
    }

    const aliasMatch = lineText.match(/^[ \t]*\/\/@[ \t]+([A-Za-z][A-Za-z0-9-]*)[ \t]*$/);
    if (!aliasMatch) return;
    const alias = aliasMatch[1];
    for (const key of KNOWN_KEYS) {
      const aliases = "directiveAliases" in OPTION_SPECS[key]
        ? OPTION_SPECS[key].directiveAliases as readonly string[]
        : [];
      if (!aliases.includes(alias)) continue;
      // Legacy aliases retain their pre-config placement behavior. New generic
      // option directives are deliberately restricted to the file preamble.
      setOption(key, true as LscOptions[typeof key], line);
      return;
    }
  };

  for (let i = 0; i < lines.length; i++) parseLine(lines[i], i, i < leadingLines);
  return out as ExplicitOptions;
}

/** Apply defaults and all cross-option rules after explicit layers are merged. */
export function resolveOptions(explicit: ExplicitOptions, source: string): LscOptions {
  // There are no cross-option constraints in the initial registry. Keep this
  // as the single resolution gate: future dependent defaults (UTF-16 → local
  // Dafny library) and incompatibilities belong here, before any consumer runs.
  void source;
  return Object.freeze({ ...DEFAULT_OPTIONS, ...explicit });
}

/** Find `fileName` at or above `fromPath`. */
export function findUp(fileName: string, fromPath: string, fromIsDirectory = false): string | null {
  let dir = fromIsDirectory ? path.resolve(fromPath) : path.dirname(path.resolve(fromPath));
  while (true) {
    const candidate = path.join(dir, fileName);
    if (existsSync(candidate)) return candidate;
    const parent = path.dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
}

/** Discover, parse, and validate a config without materializing defaults. */
export function loadConfigOptions(
  sourcePath: string,
  configPath?: string,
): { explicit: ExplicitOptions; configFile: string | null } {
  const configFile = configPath ? path.resolve(configPath) : findUp("lemmascript.json", sourcePath);
  if (!configFile) return { explicit: {}, configFile: null };
  if (!existsSync(configFile)) fail(configFile, "config file not found");

  const cached = CONFIG_CACHE.get(configFile);
  if (cached) return { explicit: { ...cached }, configFile };

  let parsed: unknown;
  try {
    parsed = JSON.parse(readFileSync(configFile, "utf8"));
  } catch (err) {
    const detail = err instanceof Error ? err.message : String(err);
    fail(configFile, `invalid JSON (${detail})`);
  }
  const explicit = validateOptions(parsed, configFile);
  CONFIG_CACHE.set(configFile, explicit);
  return { explicit: { ...explicit }, configFile };
}

/** Resolve the directory containing one source file's Dafny companions. */
export function resolveDafnyArtifactDir(
  sourcePath: string,
  configFile: string | null,
  options: LscOptions,
): string {
  const source = path.resolve(sourcePath);
  const proofDir = options["proof-dir"];
  if (proofDir === null) return path.dirname(source);
  if (!configFile) fail(source, "proof-dir requires a lemmascript.json file");

  const configDir = path.dirname(path.resolve(configFile));
  const relativeSource = path.relative(configDir, source);
  if (relativeSource === ".." || relativeSource.startsWith(`..${path.sep}`) || path.isAbsolute(relativeSource)) {
    fail(source, `is outside the config directory ${configDir}; cannot map proof-dir`);
  }
  const proofRoot = path.resolve(configDir, proofDir);
  return path.join(proofRoot, path.dirname(relativeSource));
}
