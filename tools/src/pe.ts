/**
 * pe — Partial-evaluation pass for narrowing emulation.
 *
 * Pipeline: resolve → pe → transform → emit.
 *
 * Operates on the typed IR (TExpr/TStmt) with an environment threaded
 * through the walk. Currently a no-op identity rewrite — the walker shape
 * is in place so future rules slot in without restructuring.
 *
 * The intent is to consolidate narrowing emulation here. Each pattern
 * (`if (x !== undefined) ...`, `x ? a : b`, `&&`, `||`, early return) gets
 * a rule in pe; the corresponding handling in resolve and transform gets
 * removed in lockstep.
 */

import type { TModule, TFunction, TStmt, TExpr } from "./typedir.js";

// ── Environment ──────────────────────────────────────────────
//
// Will eventually carry:
//   - bindings  (var → translated value, for inlined consts)
//   - narrowing facts (var → known-Some / known-None)
// For now it's a placeholder so the walker has the shape.

interface Env { /* empty for now */ }

const emptyEnv: Env = {};

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr, _env: Env): TExpr {
  // No-op: return as-is. Walker shape is here so future rules slot in.
  return e;
}

function walkStmt(s: TStmt, _env: Env): TStmt {
  // No-op
  return s;
}

function walkStmts(stmts: TStmt[], env: Env): TStmt[] {
  return stmts.map(s => walkStmt(s, env));
}

// ── Function / module entry ──────────────────────────────────

function peFunction(fn: TFunction): TFunction {
  return {
    ...fn,
    requires: fn.requires.map(e => walkExpr(e, emptyEnv)),
    ensures: fn.ensures.map(e => walkExpr(e, emptyEnv)),
    decreases: fn.decreases ? walkExpr(fn.decreases, emptyEnv) : null,
    body: walkStmts(fn.body, emptyEnv),
  };
}

export function peModule(mod: TModule): TModule {
  return {
    ...mod,
    constants: mod.constants.map(c => ({ ...c, value: walkExpr(c.value, emptyEnv) })),
    functions: mod.functions.map(peFunction),
    classes: mod.classes.map(cls => ({
      ...cls,
      methods: cls.methods.map(peFunction),
    })),
  };
}
