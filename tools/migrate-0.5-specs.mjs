#!/usr/bin/env node

/**
 * Migrate LemmaScript 0.5 annotation expressions to the valid-TypeScript
 * syntax introduced for 0.6.
 *
 * This is deliberately a standalone, versioned codemod. It does not add 0.5
 * compatibility to the production parser.
 */

import { execFileSync } from "node:child_process";
import { lstatSync, readFileSync, writeFileSync } from "node:fs";
import { extname, isAbsolute, join, relative, resolve } from "node:path";

import { parseLegacyExpr } from "./migrations/specparser-0.5.mjs";

const EXPRESSION_DIRECTIVES = new Set([
  "requires", "ensures", "invariant", "decreases", "done_with", "assert", "assume",
]);
const SOURCE_EXTENSIONS = new Set([".ts", ".tsx", ".mts", ".cts", ".md", ".mdx"]);
const LEGACY_QUANTIFIER = /\b(forall|exists)\s*\(\s*([A-Za-z_]\w*)\s*(?::\s*([A-Za-z_]\w*))?\s*,/g;
const LEGACY_SYNTAX = /\\result|<==>|==>|\b(?:forall|exists)\s*\(\s*[A-Za-z_]\w*\s*(?::\s*[A-Za-z_]\w*)?\s*,/;

function usage() {
  console.log(`Usage: node tools/migrate-0.5-specs.mjs [--check] [path ...]

Migrate tracked TypeScript and Markdown files under each path. Paths default to
the current Git repository. Pass a file explicitly to migrate an untracked file.

  --check   report required changes without writing; exit non-zero if any exist
  --help    show this help`);
}

function parseArgs(argv) {
  let check = false;
  const targets = [];
  for (const arg of argv) {
    if (arg === "--check") check = true;
    else if (arg === "--help" || arg === "-h") {
      usage();
      process.exit(0);
    } else if (arg.startsWith("-")) {
      throw new Error(`Unknown option: ${arg}`);
    } else {
      targets.push(arg);
    }
  }
  return { check, targets: targets.length > 0 ? targets : ["."] };
}

function gitOutput(args) {
  return execFileSync("git", args, { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] });
}

function filesForTarget(target) {
  const absolute = resolve(target);
  const stat = lstatSync(absolute);
  if (stat.isSymbolicLink()) {
    console.warn(`skipping symlink: ${displayPath(absolute)}`);
    return [];
  }
  if (stat.isFile()) return [absolute];
  if (!stat.isDirectory()) throw new Error(`Not a file or directory: ${target}`);

  let root;
  try {
    root = gitOutput(["-C", absolute, "rev-parse", "--show-toplevel"]).trim();
  } catch {
    throw new Error(`Directory target must be inside a Git repository: ${target}`);
  }
  const withinRoot = relative(root, absolute);
  if (withinRoot.startsWith("..") || isAbsolute(withinRoot)) {
    throw new Error(`Target is outside its Git repository: ${target}`);
  }
  const args = ["-C", root, "ls-files", "-z", "--"];
  if (withinRoot) args.push(withinRoot);
  return gitOutput(args)
    .split("\0")
    .filter(Boolean)
    .map(file => join(root, file))
    .filter(file => SOURCE_EXTENSIONS.has(extname(file)))
    .filter(file => {
      try {
        if (!lstatSync(file).isSymbolicLink()) return true;
        console.warn(`skipping symlink: ${displayPath(file)}`);
        return false;
      } catch (error) {
        if (error.code !== "ENOENT") throw error;
        console.warn(`skipping missing tracked path: ${displayPath(file)}`);
        return false;
      }
    });
}

function collectFiles(targets) {
  const files = new Set();
  for (const target of targets) {
    for (const file of filesForTarget(target)) files.add(file);
  }
  return [...files].sort();
}

function quantifierMetadata(source) {
  return [...source.matchAll(LEGACY_QUANTIFIER)].map(match => ({
    kind: match[1],
    name: match[2],
    type: match[3],
  }));
}

const PRECEDENCE = {
  "||": 2,
  "&&": 3,
  "===": 4,
  "!==": 4,
  "==": 4,
  "!=": 4,
  ">": 5,
  "<": 5,
  ">=": 5,
  "<=": 5,
  in: 5,
  "+": 6,
  "-": 6,
  "*": 7,
  "/": 7,
  "%": 7,
};

function printExpr(expr, metadata, parentPrecedence = 0) {
  let text;
  let ownPrecedence = 10;

  switch (expr.kind) {
    case "var":
      text = expr.name;
      break;
    case "result":
      text = "$result";
      break;
    case "num":
      if (!Number.isFinite(expr.value)) throw new Error(`Cannot migrate non-finite number ${expr.value}`);
      text = String(expr.value);
      break;
    case "bigint":
      text = `${expr.value}n`;
      break;
    case "str":
      text = JSON.stringify(expr.value);
      break;
    case "bool":
      text = String(expr.value);
      break;
    case "binop": {
      if (expr.op === "==>" || expr.op === "<==>") {
        const name = expr.op === "==>" ? "implies" : "iff";
        text = `${name}(${printExpr(expr.left, metadata)}, ${printExpr(expr.right, metadata)})`;
        break;
      }
      const op = expr.op === "==" ? "===" : expr.op === "!=" ? "!==" : expr.op;
      ownPrecedence = PRECEDENCE[op];
      if (ownPrecedence === undefined) throw new Error(`Cannot migrate operator '${op}'`);
      text = `${printExpr(expr.left, metadata, ownPrecedence)} ${op} ${printExpr(expr.right, metadata, ownPrecedence + 1)}`;
      break;
    }
    case "unop":
      ownPrecedence = 8;
      text = `${expr.op}${printExpr(expr.expr, metadata, ownPrecedence)}`;
      break;
    case "field":
      ownPrecedence = 9;
      text = `${printExpr(expr.obj, metadata, ownPrecedence)}.${expr.field}`;
      break;
    case "index":
      ownPrecedence = 9;
      text = `${printExpr(expr.obj, metadata, ownPrecedence)}[${printExpr(expr.idx, metadata)}]`;
      break;
    case "call":
      ownPrecedence = 9;
      text = `${printExpr(expr.fn, metadata, ownPrecedence)}(${expr.args.map(arg => printExpr(arg, metadata)).join(", ")})`;
      break;
    case "conditional":
      ownPrecedence = 1;
      text = `${printExpr(expr.cond, metadata, ownPrecedence + 1)} ? ${printExpr(expr.then, metadata, ownPrecedence)} : ${printExpr(expr.else, metadata, ownPrecedence)}`;
      break;
    case "arrayLiteral":
      text = `[${expr.elems.map(elem => printExpr(elem, metadata)).join(", ")}]`;
      break;
    case "record":
      text = `{ ${expr.fields.map(field => `${field.name}: ${printExpr(field.value, metadata)}`).join(", ")} }`;
      break;
    case "emptyCollection":
      text = `new ${expr.tsType}()`;
      break;
    case "forall":
    case "exists": {
      const info = metadata.shift();
      if (!info || info.kind !== expr.kind || info.name !== expr.var) {
        throw new Error(`Quantifier metadata did not match ${expr.kind}(${expr.var}, ...)`);
      }
      const parameter = info.type ? `(${expr.var}: ${info.type})` : expr.var;
      let body = printExpr(expr.body, metadata);
      if (expr.body.kind === "record") body = `(${body})`;
      text = `${expr.kind}(${parameter} => ${body})`;
      break;
    }
    default:
      throw new Error(`Cannot migrate legacy expression node '${expr.kind}'`);
  }

  return ownPrecedence < parentPrecedence ? `(${text})` : text;
}

function migrateExpression(source) {
  const metadata = quantifierMetadata(source);
  const result = printExpr(parseLegacyExpr(source), metadata);
  if (metadata.length > 0) throw new Error("Unused quantifier metadata");
  return result;
}

function trailingCommentIndex(source) {
  let quote = null;
  let escaped = false;
  let depth = 0;
  for (let i = 0; i + 1 < source.length; i++) {
    const char = source[i];
    if (quote !== null) {
      if (escaped) escaped = false;
      else if (char === "\\") escaped = true;
      else if (char === quote) quote = null;
      continue;
    }
    if (char === '"' || char === "'") quote = char;
    else if ("([{".includes(char)) depth++;
    else if (")]}".includes(char)) depth--;
    else if (char === "/" && source[i + 1] === "/" && depth === 0) return i;
  }
  return -1;
}

function migrateExpressionAndComment(source) {
  try {
    return migrateExpression(source);
  } catch (wholeError) {
    const commentAt = trailingCommentIndex(source);
    if (commentAt < 0) throw wholeError;
    const expression = source.slice(0, commentAt).trimEnd();
    const comment = source.slice(commentAt);
    return `${migrateExpression(expression)}  ${comment}`;
  }
}

function migrateDirective(body) {
  if (/^type\s+\\result\b/.test(body)) {
    return body.replace(/^(type\s+)\\result\b/, "$1$result");
  }

  const directive = body.match(/^([A-Za-z_]+)(\s+)(.*)$/);
  if (!directive) return null;
  const [, keyword, spacing, rest] = directive;

  if (EXPRESSION_DIRECTIVES.has(keyword)) {
    return `${keyword}${spacing}${migrateExpressionAndComment(rest)}`;
  }

  if (keyword === "ghost") {
    const declaration = rest.match(/^(let\s+[A-Za-z_]\w*(?:\s*:\s*[^=]+)?\s*=\s*)(.*)$/);
    if (declaration) return `${keyword}${spacing}${declaration[1]}${migrateExpressionAndComment(declaration[2])}`;
    const assignment = rest.match(/^([A-Za-z_]\w*\s*=\s*)(.*)$/);
    if (assignment) return `${keyword}${spacing}${assignment[1]}${migrateExpressionAndComment(assignment[2])}`;
  }

  return null;
}

function migrateLine(line) {
  if (!LEGACY_SYNTAX.test(line)) return { line, changed: false };

  const leading = line.match(/^(\s*(?:\*\s*)?\/\/@\s*)(.*)$/);
  if (leading) {
    const body = migrateDirective(leading[2]);
    if (body === null) throw new Error("unsupported or multiline annotation directive");
    return { line: `${leading[1]}${body}`, changed: body !== leading[2] };
  }

  // Markdown commonly quotes complete annotations as `//@ ...` inside prose.
  let changed = false;
  const migrated = line.replace(/(`\/\/@\s*)([^`]+)(`)/g, (whole, prefix, oldBody, suffix) => {
    if (!LEGACY_SYNTAX.test(oldBody)) return whole;
    const newBody = migrateDirective(oldBody);
    if (newBody === null) throw new Error("unsupported inline annotation directive");
    changed ||= newBody !== oldBody;
    return `${prefix}${newBody}${suffix}`;
  });
  if (changed) return { line: migrated, changed: true };

  return { line, changed: false };
}

function displayPath(file) {
  const rel = relative(process.cwd(), file);
  return rel && !rel.startsWith("..") ? rel : file;
}

function main() {
  const { check, targets } = parseArgs(process.argv.slice(2));
  const files = collectFiles(targets);
  const failures = [];
  const updates = [];
  let changedLines = 0;

  for (const file of files) {
    const original = readFileSync(file, "utf8");
    const eol = original.includes("\r\n") ? "\r\n" : "\n";
    const lines = original.split(/\r?\n/);
    let fileChanged = false;
    const migrated = lines.map((line, index) => {
      try {
        const result = migrateLine(line);
        if (result.changed) {
          fileChanged = true;
          changedLines++;
        }
        return result.line;
      } catch (error) {
        failures.push(`${displayPath(file)}:${index + 1}: ${error.message}`);
        return line;
      }
    }).join(eol);
    if (fileChanged) updates.push({ file, text: migrated });
  }

  if (!check) {
    for (const update of updates) writeFileSync(update.file, update.text);
  }

  const verb = check ? "would migrate" : "migrated";
  console.log(`${verb} ${changedLines} annotation line(s) in ${updates.length} file(s)`);
  if (failures.length > 0) {
    console.error(`${failures.length} line(s) need manual migration:`);
    for (const failure of failures) console.error(`  ${failure}`);
  }

  if (failures.length > 0 || (check && updates.length > 0)) process.exitCode = 1;
}

try {
  main();
} catch (error) {
  console.error(`ERROR: ${error.message}`);
  process.exitCode = 1;
}
