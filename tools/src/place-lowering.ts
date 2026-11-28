/**
 * Place-driven mutation write-back lowering for `transform.ts`
 * (`midspiral/LemmaScript#387`, Milestone 3a / `robertpenner/LemmaScript#49`).
 *
 * Consumes the self-verified `PlacePath` representation in `places.ts` and
 * maintains the active stack of narrowing write-back frames (`someMatch`
 * unwraps and `switch`/`tagMatch` union variants) so in-place mutations
 * (`push`, `unshift`, `sort`, `pop`, `set`, `add`, `delete`, index updates,
 * and record-field assignments) always propagate back to the owning lexical
 * storage variable instead of mutating a discarded copy or match binder.
 */

import type { Expr, Stmt } from "./ir.js";
import type { TExpr, Ty } from "./typedir.js";
import {
  extendFieldPlace,
  extendUnwrapPlace,
  makeVarPlace,
  type PlacePath,
} from "./places.js";

export type WriteBackFrame = {
  kind: "unwrap";
  /** Match binder introduced by `someMatch`, e.g. `_arr_val`. */
  binder: string;
  /** Root variable name of the `someMatch` scrutinee (may be an outer binder). */
  rootVar: string;
  /** Field chain on `rootVar` before unwrapping, e.g. `["items"]` for `_b_val.items`. */
  fields: string[];
  /** Self-verified PlacePath for this unwrap step. */
  place: PlacePath;
};

export function makeUnwrapFrame(binder: string, rootVar: string, fields: string[]): WriteBackFrame {
  let place: PlacePath = makeVarPlace(rootVar);
  for (const f of fields) place = extendFieldPlace(place, f);
  place = extendUnwrapPlace(place);
  return { kind: "unwrap", binder, rootVar, fields, place };
}

/** True for in-place mutating collection methods modeled by functional write-back. */
export function isMutatingCollectionMethod(recvTy: Ty, method: string): boolean {
  if ((recvTy.kind === "map" || recvTy.kind === "set") &&
      (method === "set" || method === "add" || method === "delete")) {
    return true;
  }
  if (recvTy.kind === "array" && (method === "push" || method === "unshift" || method === "sort")) {
    return true;
  }
  return false;
}

/** Build a nested record-update expression rooted at `rootVar` for `fields`
 *  (length >= 1), setting the innermost field to `newVal`. Optional
 *  `unionsByDepth` pins the union constructor/type at each nesting depth `i`
 *  whose owner is a discriminated union (for collision-renamed destructors in
 *  Dafny and match-updates in Lean). */
export function buildNestedFieldExpr(
  rootVar: string,
  fields: string[],
  newVal: Expr,
  unionsByDepth?: ({ ctor?: string; ctorOf: string } | undefined)[],
): Expr {
  const baseFor = (len: number): Expr => {
    let cur: Expr = { kind: "var", name: rootVar };
    for (let i = 0; i < len; i++) {
      const u = unionsByDepth?.[i];
      const unionTag = u ? { fromUnion: u.ctorOf, ctor: u.ctor } : {};
      cur = { kind: "field", obj: cur, field: fields[i], ...unionTag, datatypeField: true };
    }
    return cur;
  };
  let curVal = newVal;
  for (let i = fields.length - 1; i >= 0; i--) {
    const u = unionsByDepth?.[i];
    const unionTag = u ? { ctor: u.ctor, ctorOf: u.ctorOf } : {};
    curVal = {
      kind: "record",
      spread: baseFor(i),
      fields: [{ name: fields[i], value: curVal }],
      ...unionTag,
    };
  }
  return curVal;
}

function optionSome(value: Expr): Expr {
  return { kind: "constructor", name: "some", type: "Option", args: [value] };
}

/**
 * Given a variable `mutatedTarget` that was just assigned in the lowered IR,
 * walk `frames` from innermost to outermost and emit the cascading write-back
 * assignments that synchronize every enclosing `someMatch` binder and the owning
 * lexical storage variable.
 */
export function emitWriteBacksForTarget(mutatedTarget: string, frames: readonly WriteBackFrame[]): Stmt[] {
  const out: Stmt[] = [];
  let current = mutatedTarget;

  for (let i = frames.length - 1; i >= 0; i--) {
    const frame = frames[i];
    if (frame.binder === current) {
      const wrapped = optionSome({ kind: "var", name: frame.binder });
      if (frame.fields.length === 0) {
        out.push({ kind: "assign", target: frame.rootVar, value: wrapped });
      } else {
        out.push({
          kind: "assign",
          target: frame.rootVar,
          value: buildNestedFieldExpr(frame.rootVar, frame.fields, wrapped),
        });
      }
      current = frame.rootVar;
    }
  }

  return out;
}

/** Find the innermost active `unwrap` frame whose scrutinee matches `(rootVar, fields)`. */
export function findActiveUnwrapFrame(
  rootVar: string,
  fields: string[],
  frames: readonly WriteBackFrame[],
): WriteBackFrame | null {
  for (let i = frames.length - 1; i >= 0; i--) {
    const frame = frames[i];
    if (
      frame.rootVar === rootVar &&
      frame.fields.length === fields.length &&
      frame.fields.every((f, idx) => f === fields[idx])
    ) {
      return frame;
    }
  }
  return null;
}

/** Resolve a source dotted path like `["b", "count"]` through any enclosing
 *  `someMatch` unwrap frames. */
export function resolveWriteTargetThroughFrames(
  rootVar: string,
  fields: string[],
  frames: readonly WriteBackFrame[],
): {
  currentRoot: string;
  remainingFields: string[];
  leafUnwrapFrame: WriteBackFrame | null;
} {
  let currentRoot = rootVar;
  let idx = 0;
  let lastUnwrap: WriteBackFrame | null = null;

  while (true) {
    // 1. Bare unwrap on `currentRoot` (e.g. `b` -> `_b_val`).
    const bareUnwrap = findActiveUnwrapFrame(currentRoot, [], frames);
    if (bareUnwrap) {
      currentRoot = bareUnwrap.binder;
      lastUnwrap = bareUnwrap;
      continue;
    }

    if (idx >= fields.length) break;

    // 2. Field-prefix unwrap on `currentRoot` (e.g. `_b_val.items` -> `_b_val_items_val`).
    let matchedLen = 0;
    let matchedUnwrap: WriteBackFrame | null = null;
    for (let len = fields.length - idx; len >= 1; len--) {
      const sub = fields.slice(idx, idx + len);
      const hit = findActiveUnwrapFrame(currentRoot, sub, frames);
      if (hit) {
        matchedLen = len;
        matchedUnwrap = hit;
        break;
      }
    }
    if (matchedUnwrap) {
      currentRoot = matchedUnwrap.binder;
      idx += matchedLen;
      lastUnwrap = matchedUnwrap;
      continue;
    }

    break;
  }

  return {
    currentRoot,
    remainingFields: fields.slice(idx),
    leafUnwrapFrame: idx === fields.length ? lastUnwrap : null,
  };
}

/** Collect every variable name assigned anywhere in lowered IR `Stmt[]`
 *  (both `assign` and Lean monadic `bind`). */
export function collectAssignedIrTargets(stmts: readonly Stmt[]): Set<string> {
  const assigned = new Set<string>();
  const walk = (ss: readonly Stmt[]) => {
    for (const s of ss) {
      if ((s.kind === "assign" || s.kind === "bind") && s.target !== "_" && !s.target.includes(".")) {
        assigned.add(s.target);
      } else if (s.kind === "if") {
        walk(s.then);
        walk(s.else);
      } else if (s.kind === "while" || s.kind === "forin") {
        walk(s.body);
      } else if (s.kind === "match") {
        for (const a of s.arms) walk(a.body);
      }
    }
  };
  walk(stmts);
  return assigned;
}

/** Describe a non-Place receiver for a clear fail-closed diagnostic. */
export function describeReceiver(recv: TExpr): string {
  switch (recv.kind) {
    case "var": return recv.name;
    case "field": return `${describeReceiver(recv.obj)}.${recv.field}`;
    case "call": return `${describeReceiver(recv.fn)}(...)`;
    case "index": return `${describeReceiver(recv.obj)}[...]`;
    default: return `<${recv.kind}>`;
  }
}
