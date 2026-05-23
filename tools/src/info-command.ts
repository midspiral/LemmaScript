/**
 * `lsc info` — emit a JSON summary of verified functions in a TS file.
 *
 * Pipeline: extract only (no resolve/transform/emit). Walks Raw IR for
 * top-level functions and class methods, preserving the original `//@ `
 * source text for clauses (no specparser round-trip).
 *
 * Output: `foo.ts.json` next to `foo.ts`, with shape:
 *   { method: { sig, requires, ensures, decreases }, ... }
 * Class methods key as `ClassName.method`.
 */

import { writeFileSync } from "fs";
import type { RawFunction, RawModule } from "./rawir.js";
import { parseTsType, tyToCanonical } from "./types.js";

interface FnInfo {
  sig: string;
  requires: string[];
  ensures: string[];
  decreases: string | null;
}

function renderSig(fn: RawFunction): string {
  const params = fn.params.map(p => `${p.name}: ${tyToCanonical(parseTsType(p.tsType))}`).join(", ");
  return `(${params}): ${tyToCanonical(parseTsType(fn.returnType))}`;
}

function fnToInfo(fn: RawFunction): FnInfo {
  return {
    sig: renderSig(fn),
    requires: fn.requires,
    ensures: fn.ensures,
    decreases: fn.decreases,
  };
}

export function runInfo(raw: RawModule, outPath: string): void {
  const out: Record<string, FnInfo> = {};
  for (const fn of raw.functions) {
    out[fn.name] = fnToInfo(fn);
  }
  for (const cls of raw.classes) {
    for (const m of cls.methods) {
      out[`${cls.name}.${m.name}`] = fnToInfo(m);
    }
  }
  writeFileSync(outPath, JSON.stringify(out, null, 2) + "\n");
  console.log(`Wrote ${outPath}`);
}
