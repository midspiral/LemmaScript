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
  extendVariantPlace,
  makeVarPlace,
  type PlacePath,
} from "./places.js";

export type WriteBackFrame =
  | {
      kind: "unwrap";
      /** Match binder introduced by `someMatch`, e.g. `_arr_val`. */
      binder: string;
      /** Root variable name of the `someMatch` scrutinee (may be an outer binder). */
      rootVar: string;
      /** Field chain on `rootVar` before unwrapping, e.g. `["items"]` for `_b_val.items`. */
      fields: string[];
      /** Self-verified PlacePath for this unwrap step. */
      place: PlacePath;
    }
  | {
      kind: "variant";
      /** Enclosing union variable name, e.g. `u`. */
      unionVar: string;
      /** Union datatype base name, e.g. `Item`. */
      typeName: string;
      /** Matched variant constructor name, e.g. `b`. */
      ctorName: string;
      /** Ordered variant fields and their match binder names. */
      fields: { fieldName: string; binder: string }[];
      /** Self-verified PlacePath for this variant projection. */
      place: PlacePath;
    };

export function makeUnwrapFrame(binder: string, rootVar: string, fields: string[]): WriteBackFrame {
  let place: PlacePath = makeVarPlace(rootVar);
  for (const f of fields) place = extendFieldPlace(place, f);
  place = extendUnwrapPlace(place);
  return { kind: "unwrap", binder, rootVar, fields, place };
}

export function makeVariantFrame(
  unionVar: string,
  typeName: string,
  ctorName: string,
  fields: { fieldName: string; binder: string }[],
): WriteBackFrame {
  const place = extendVariantPlace(makeVarPlace(unionVar), ctorName);
  return { kind: "variant", unionVar, typeName, ctorName, fields, place };
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
 *  (length >= 1), setting the innermost field to `newVal`. */
export function buildNestedFieldExpr(rootVar: string, fields: string[], newVal: Expr): Expr {
  const baseFor = (len: number): Expr => {
    let cur: Expr = { kind: "var", name: rootVar };
    for (let i = 0; i < len; i++) {
      cur = { kind: "field", obj: cur, field: fields[i], datatypeField: true };
    }
    return cur;
  };
  let curVal = newVal;
  for (let i = fields.length - 1; i >= 0; i--) {
    curVal = {
      kind: "record",
      spread: baseFor(i),
      fields: [{ name: fields[i], value: curVal }],
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
 * assignments that synchronize every enclosing narrowing binder and the owning
 * lexical storage variable.
 */
export function emitWriteBacksForTarget(mutatedTarget: string, frames: readonly WriteBackFrame[]): Stmt[] {
  const out: Stmt[] = [];
  let current = mutatedTarget;

  for (let i = frames.length - 1; i >= 0; i--) {
    const frame = frames[i];
    if (frame.kind === "unwrap" && frame.binder === current) {
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
      continue;
    }

    if (frame.kind === "variant" && frame.fields.some(f => f.binder === current)) {
      const reconstructed: Expr = {
        kind: "app",
        fn: frame.ctorName,
        ctorOf: frame.typeName,
        args: frame.fields.map(f => ({ kind: "var", name: f.binder })),
      };
      out.push({ kind: "assign", target: frame.unionVar, value: reconstructed });
      current = frame.unionVar;
    }
  }

  return out;
}

/** Find the innermost active `unwrap` frame whose scrutinee matches `(rootVar, fields)`. */
export function findActiveUnwrapFrame(
  rootVar: string,
  fields: string[],
  frames: readonly WriteBackFrame[],
): Extract<WriteBackFrame, { kind: "unwrap" }> | null {
  for (let i = frames.length - 1; i >= 0; i--) {
    const frame = frames[i];
    if (
      frame.kind === "unwrap" &&
      frame.rootVar === rootVar &&
      frame.fields.length === fields.length &&
      frame.fields.every((f, idx) => f === fields[idx])
    ) {
      return frame;
    }
  }
  return null;
}

/** Resolve a source dotted path like `["b", "count"]`, `["u", "v"]`, or
 *  `["u", "box", "count"]` through any enclosing `unwrap` and `variant` frames.
 *  Returns:
 *    - `currentRoot`: the deepest active binder/variable reached,
 *    - `remainingFields`: any field steps remaining below `currentRoot`,
 *    - `leafUnwrapFrame`: if the entire path ended at an active `unwrap` frame
 *      (so non-optional writes update `leafUnwrapFrame.binder` and cascade,
 *      while `undefined`/optional writes update `leafUnwrapFrame.rootVar`),
 *    - `leafVariantBinder`: if the entire path ended directly at a union
 *      variant field binder (e.g. `u.v` -> `i_u_v`). */
export function resolveWriteTargetThroughFrames(
  rootVar: string,
  fields: string[],
  frames: readonly WriteBackFrame[],
): {
  currentRoot: string;
  remainingFields: string[];
  leafUnwrapFrame: Extract<WriteBackFrame, { kind: "unwrap" }> | null;
  leafVariantBinder: string | null;
} {
  let currentRoot = rootVar;
  let idx = 0;
  let lastUnwrap: Extract<WriteBackFrame, { kind: "unwrap" }> | null = null;
  let lastVariantBinder: string | null = null;

  // Iteratively step through active `unwrap` (0-field or prefix-field) and
  // `variant` (1-field) frames until no more frames match.
  while (true) {
    // 1. Bare unwrap on `currentRoot` (e.g. `b` -> `_b_val`, or `u` -> `_u_val`).
    const bareUnwrap = findActiveUnwrapFrame(currentRoot, [], frames);
    if (bareUnwrap) {
      currentRoot = bareUnwrap.binder;
      lastUnwrap = bareUnwrap;
      lastVariantBinder = null;
      continue;
    }

    if (idx >= fields.length) break;

    // 2. Variant field projection on `currentRoot` (e.g. `u.v` -> `i_u_v`, `u.box` -> `i_u_box`).
    let matchedVariant: string | null = null;
    for (let i = frames.length - 1; i >= 0; i--) {
      const frame = frames[i]!;
      if (frame.kind === "variant" && frame.unionVar === currentRoot) {
        const hit = frame.fields.find(f => f.fieldName === fields[idx]);
        if (hit) {
          matchedVariant = hit.binder;
          break;
        }
      }
    }
    if (matchedVariant) {
      currentRoot = matchedVariant;
      idx += 1;
      lastUnwrap = null;
      lastVariantBinder = matchedVariant;
      continue;
    }

    // 3. Field-prefix unwrap on `currentRoot` (e.g. `_b_val.items` -> `_b_val_items_val`).
    let matchedLen = 0;
    let matchedUnwrap: Extract<WriteBackFrame, { kind: "unwrap" }> | null = null;
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
      lastVariantBinder = null;
      continue;
    }

    break;
  }

  return {
    currentRoot,
    remainingFields: fields.slice(idx),
    leafUnwrapFrame: idx === fields.length ? lastUnwrap : null,
    leafVariantBinder: idx === fields.length ? lastVariantBinder : null,
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
