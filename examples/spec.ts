/**
 * Spec coverage — exercises all LemmaScript features systematically.
 * Each function targets specific spec sections noted in comments.
 */

// ═══ §8.2: String literal union → inductive with DecidableEq ═══
type Priority = "low" | "medium" | "high"

// ═══ §8.3: Discriminated union with data → inductive ═══
type Expr =
  | { kind: "lit"; val: number }
  | { kind: "add"; a: number; b: number }
  | { kind: "neg"; inner: number }

// ═══ §8.5: Interface → structure, with §3.3 field-level //@ type nat ═══
export interface Config {
  threshold: number; //@ type nat
  maxRetries: number; //@ type nat
  enabled: boolean;
}

// ═══════════════════════════════════════════════════════════════
// Pure functions (§6.1) — no while, no mutable let → def generation
// ═══════════════════════════════════════════════════════════════

// §5.4: if-chain on discriminant → match (partial dispatch, natural default)
function evalPartial(e: Expr): number {
  //@ ensures implies(e.kind === "lit", $result === e.val)
  //@ ensures implies(e.kind === "add", $result === e.a + e.b)
  if (e.kind === "lit") return e.val;
  if (e.kind === "add") return e.a + e.b;
  return 0;
}

// §5.4: switch on discriminant → match (exhaustive, no default needed)
function evalSwitch(e: Expr): number {
  //@ ensures implies(e.kind === "lit", $result === e.val)
  //@ ensures implies(e.kind === "add", $result === e.a + e.b)
  //@ ensures implies(e.kind === "neg", $result === 0 - e.inner)
  switch (e.kind) {
    case "lit": return e.val;
    case "add": return e.a + e.b;
    case "neg": return 0 - e.inner;
  }
}

// §8.2: enum-like equality → constructor comparison
function isHighPriority(p: Priority): boolean {
  //@ ensures implies(p === "high", $result === true)
  //@ ensures implies(p !== "high", $result === false)
  if (p === "high") return true;
  return false;
}

// §8.5: record literal construction
function defaultConfig(): Config {
  //@ ensures $result.threshold === 0 && $result.enabled === true
  return { threshold: 0, maxRetries: 3, enabled: true };
}

// §8.5: record spread / functional update (§4.2)
function withThreshold(c: Config, t: number): Config {
  //@ type t nat
  //@ ensures $result.threshold === t
  //@ ensures $result.enabled === c.enabled
  return { ...c, threshold: t };
}

// Ternary / conditional expression
function clampTernary(x: number, lo: number, hi: number): number {
  //@ requires lo <= hi
  //@ ensures $result >= lo && $result <= hi
  //@ ensures $result === (x < lo ? lo : x > hi ? hi : x)
  return x < lo ? lo : x > hi ? hi : x;
}

// Ternary with string→constructor coercion
function demoteOnFail(p: Priority, ok: boolean): Priority {
  return ok ? p : "low";
}

// Record field string→constructor coercion
export interface PriorityItem {
  level: Priority;
  value: number;
}

function makeHighItem(v: number): PriorityItem {
  return { level: "high", value: v };
}

// §4.2: Math.floor — integer (floor) division. Bare `/` is real division, so
// the postcondition must floor too: `(lo + hi) / 2` alone would be the real 1.5.
function midpoint(lo: number, hi: number): number {
  //@ ensures $result === Math.floor((lo + hi) / 2)
  return Math.floor((lo + hi) / 2);
}

// §6.1.1: BigInt literals stay exact past Number.MAX_SAFE_INTEGER. The two
// postconditions straddle 2^53, where a double can't tell 9007199254740993
// from 9007199254740992 — so this only verifies if the literal never rounds
// through Number, in the body *or* in the annotation.
function exactBigIntLiteral(): bigint {
  //@ ensures $result === 9007199254740993n
  //@ ensures $result !== 9007199254740992n
  return 0x20000000000001n;
}

// §6.1.1: same, through unary minus — a negative literal must not be folded
// by negating a JS number.
function exactNegativeBigIntLiteral(): bigint {
  //@ ensures $result === -9007199254740993n
  //@ ensures $result !== -9007199254740992n
  return -9007199254740993n;
}

// §4.2: array literal
function wrapOne(x: number): number[] {
  //@ ensures $result.length === 1
  return [x];
}

function threeElems(a: number, b: number, c: number): number[] {
  //@ ensures $result.length === 3
  return [a, b, c];
}

// §4.2, §4.8: array spread → Array.push
function append(arr: number[], x: number): number[] {
  return [...arr, x];
}

// ═══════════════════════════════════════════════════════════════
// Higher-order functions (§4.7) — DOT_METHODS dispatch
// ═══════════════════════════════════════════════════════════════

// map
function doubleAll(arr: number[]): number[] {
  //@ ensures $result.length === arr.length
  return arr.map((x) => x * 2);
}

// filter
function keepPositive(arr: number[]): number[] {
  return arr.filter((x) => x > 0);
}

// every → all
function allBelow(arr: number[], cap: number): boolean {
  return arr.every((x) => x < cap);
}

// some → any
function anyNegative(arr: number[]): boolean {
  return arr.some((x) => x < 0);
}

// pure function call in HOF lambda — no monadic lifting (§4.7)
function negate(x: number): number {
  //@ ensures $result === 0 - x
  return 0 - x;
}

function negateAll(arr: number[]): number[] {
  //@ ensures $result.length === arr.length
  return arr.map((x) => negate(x));
}

// includes → contains
function hasValue(arr: number[], v: number): boolean {
  return arr.includes(v);
}

// with → set! (functional array update, §4.8), Nat index
function replaceAt(arr: number[], i: number, v: number): number[] {
  //@ type i nat
  //@ requires i < arr.length
  return arr.with(i, v);
}

// with → set! with Int index — needs .toNat
function replaceAtInt(arr: number[], i: number, v: number): number[] {
  //@ requires i >= 0 && i < arr.length
  return arr.with(i, v);
}

// ═══════════════════════════════════════════════════════════════
// Method table dispatch (§4.8) — METHOD_TABLE: string operations
// ═══════════════════════════════════════════════════════════════

// indexOf → JSString.indexOf
function findSubstr(s: string, sub: string): number {
  return s.indexOf(sub);
}

// slice → JSString.slice
function getSlice(s: string, start: number, end: number): string {
  //@ type start nat
  //@ type end nat
  //@ requires start <= end && end <= s.length
  return s.slice(start, end);
}

// ═══════════════════════════════════════════════════════════════
// While loop + all annotations (§5.2, §3.1, §3.3)
// ═══════════════════════════════════════════════════════════════

// §5.1: compound assignment (+=), increment (i++), §3.3 type nat
function countAbove(arr: number[], threshold: number): number {
  //@ type i nat
  //@ type count nat
  //@ ensures $result <= arr.length
  let count = 0;
  let i = 0;
  while (i < arr.length) {
    //@ invariant i <= arr.length
    //@ invariant count <= i
    //@ decreases arr.length - i
    if (arr[i] > threshold) {
      count += 1;
    }
    i++;
  }
  return count;
}

// §4.4: implication flattening (implies(A && B, C) → A → B → C)
// §4.5: conjunction splitting (ensures A && B → two clauses)
// §5.2: done_with, break
function search(arr: number[], target: number): number {
  //@ type i nat
  //@ ensures $result >= -1 && $result < arr.length
  //@ ensures implies($result >= 0, arr[$result] === target)
  //@ ensures implies(arr.length > 0 && $result === -1, forall((k: nat) => implies(k < arr.length, arr[k] !== target)))
  let result = -1;
  let i = 0;
  while (i < arr.length) {
    //@ invariant i <= arr.length
    //@ invariant result === -1 || (result >= 0 && result < arr.length && arr[result] === target)
    //@ invariant forall((k: nat) => implies(k < i, arr[k] !== target))
    //@ decreases arr.length - i
    //@ done_with result !== -1 || i >= arr.length
    if (arr[i] === target) {
      result = i;
      break;
    }
    i = i + 1;
  }
  return result;
}

// ═══════════════════════════════════════════════════════════════
// Monadic lifting (§4.6) — embedded method calls in return expr
// ═══════════════════════════════════════════════════════════════

// Mutable let makes this non-pure; embedded method calls get lifted to let ← binds
function sumSearchResults(arr: number[], a: number, b: number): number {
  let sum = 0;
  sum = search(arr, a) + search(arr, b);
  return sum;
}

// ═══════════════════════════════════════════════════════════════
// For-of loop (§5.1) — desugared to for-in over range
// ═══════════════════════════════════════════════════════════════

function forOfContains(arr: number[], target: number): boolean {
  //@ ensures implies($result === true, exists((k: nat) => k < arr.length && arr[k] === target))
  let found = false;
  for (const x of arr) {
    //@ invariant implies(found === false, forall((k: nat) => implies(k < _x_idx, arr[k] !== target)))
    //@ invariant implies(found === true, exists((k: nat) => k < arr.length && arr[k] === target))
    //@ done_with found === true || !(_x_idx < arr.length)
    if (x === target) {
      found = true;
      break;
    }
  }
  return found;
}

// ═══════════════════════════════════════════════════════════════
// Monadic lifting in records and nested args
// ═══════════════════════════════════════════════════════════════

// Method call results in record fields — needs monadic lifting in records
function clampedItem(x: number): PriorityItem {
  //@ ensures $result.level === "high"
  let tmp = x;  // mutable → non-pure → full method body
  return { level: "high", value: clampTernary(tmp, 0, 100) };
}

// Nested method call: method result passed as arg to another method call
function clampedMidpoint(a: number, b: number): number {
  //@ requires a <= b
  //@ ensures $result >= a && $result <= b
  let mid = midpoint(a, b);  // mutable → non-pure → full method body
  return clampTernary(mid, a, b);
}

// ═══════════════════════════════════════════════════════════════
// Optional narrowing — TS-faithful: vars, obj.field, and deep paths
// ═══════════════════════════════════════════════════════════════

interface Leaf { value: number }
interface Middle { leaf: Leaf | undefined }
interface Tree { middle: Middle | undefined }

// Deep-path narrowing: `&&` chain of `t.middle !== undefined` then
// `t.middle.leaf !== undefined` narrows both paths in the then-branch,
// so `t.middle.leaf.value` typechecks as `number`. Lowers to nested matches.
function deepAccess(t: Tree): number {
  //@ ensures implies(t.middle !== undefined && t.middle.leaf !== undefined, $result === t.middle.leaf.value)
  //@ ensures implies(t.middle === undefined, $result === 0)
  if (t.middle !== undefined && t.middle.leaf !== undefined) {
    return t.middle.leaf.value;
  }
  return 0;
}

// ═══════════════════════════════════════════════════════════════
// Optional chaining `?.` — all flavors: field, method call, index, chained
// ═══════════════════════════════════════════════════════════════

interface Inner { val: number }
interface Outer { inner: Inner | undefined }

// `?.field`: simple property access — single short-circuit
function ocField(o: Outer | undefined): Inner | undefined {
  //@ ensures implies(o === undefined, $result === undefined)
  //@ ensures implies(o !== undefined, $result === o.inner)
  return o?.inner;
}

// `?.field.field`: ?. then non-? continuation — short-circuit only at first ?
function ocChain(o: Outer | undefined): number | undefined {
  //@ ensures implies(o === undefined, $result === undefined)
  //@ ensures implies(o !== undefined && o.inner === undefined, $result === undefined)
  //@ ensures implies(o !== undefined && o.inner !== undefined, $result === o.inner.val)
  return o?.inner?.val;
}

// `?.foo()`: method call after ?. — peephole collapses set.has to `in`
function ocMethodCall(s: Set<string> | undefined, k: string): boolean | undefined {
  //@ ensures implies(s === undefined, $result === undefined)
  //@ ensures implies(s !== undefined, $result === s.has(k))
  return s?.has(k);
}

// `?.[k]`: index access via ?.[ ] — Record indexes return Option<value>
function ocIndex(m: Record<string, string> | undefined, k: string): string | undefined {
  //@ ensures implies(m === undefined, $result === undefined)
  //@ ensures implies(m !== undefined, $result === m[k])
  return m?.[k];
}

// ═══════════════════════════════════════════════════════════════
// Nullish coalescing `a ?? b` — single-eval; defaults if a is undefined
// ═══════════════════════════════════════════════════════════════

// Optional var with default
function nullishVar(o: Inner | undefined, fallback: number): number {
  //@ ensures implies(o === undefined, $result === fallback)
  //@ ensures implies(o !== undefined, $result === o.val)
  return o?.val ?? fallback;
}

// Map.get + ?? — peephole collapses to `if k in m then m[k] else fallback`
function nullishMapGet(m: Map<string, number>, k: string, fallback: number): number {
  //@ ensures implies(!(k in m), $result === fallback)
  //@ ensures implies(k in m, $result === m.get(k))
  return m.get(k) ?? fallback;
}

// `k in m ? m[k] : default` on a Record<K,V> — narrow rule rewrites to a
// someMatch over m[k]; the peephole then collapses to
// `if k in m then m[k] else default`, same as the `??` form above.
function inCheckRecordGet(m: Record<string, number>, k: string, fallback: number): number {
  //@ ensures implies(!(k in m), $result === fallback)
  //@ ensures implies(k in m, $result === m[k])
  return k in m ? m[k] : fallback;
}

// `requires k in m` — atom in scope for the whole body, `m[k]` narrowed to V directly.
function requiresInMap(m: Record<string, number>, k: string): number {
  //@ requires k in m
  //@ ensures $result === m[k]
  return m[k];
}

// `if (k in m) { ... m[k] ... }` — positive check narrows the then-branch.
function ifInMapBlock(m: Record<string, number>, k: string, fallback: number): number {
  //@ ensures implies(k in m, $result === m[k])
  //@ ensures implies(!(k in m), $result === fallback)
  if (k in m) return m[k];
  return fallback;
}

// `if (!(k in m)) return ...; rest` — early-return narrows the rest.
function ifNotInMapEarlyReturn(m: Record<string, number>, k: string, fallback: number): number {
  //@ ensures implies(!(k in m), $result === fallback)
  //@ ensures implies(k in m, $result === m[k])
  if (!(k in m)) return fallback;
  return m[k];
}

// `//@ assert k in m` — atom from assert narrows subsequent accesses in the block.
function assertInMap(m: Record<string, number>, k: string, fallback: number): number {
  //@ ensures implies(k in m, $result === m[k])
  //@ ensures implies(!(k in m), $result === fallback)
  if (!(k in m)) return fallback;
  //@ assert k in m
  return m[k];
}

// While-loop: `invariant k in m` narrows map index access inside the loop.
function whileInvariantInMap(m: Record<string, number>, k: string, reps: number): number {
  //@ type reps nat
  //@ type i nat
  //@ requires k in m
  //@ ensures $result === m[k] * reps
  let total = 0;
  let i = 0;
  while (i < reps) {
    //@ invariant k in m
    //@ invariant i <= reps
    //@ invariant total === m[k] * i
    //@ decreases reps - i
    total = total + m[k];
    i = i + 1;
  }
  return total;
}

// ═══════════════════════════════════════════════════════════════
// Negative truthiness `if (!x)` — equivalent to `x === undefined`
// ═══════════════════════════════════════════════════════════════

// Var early-return: !o narrows o to Inner after the if
function negVar(o: Inner | undefined, fallback: number): number {
  //@ ensures implies(o === undefined, $result === fallback)
  //@ ensures implies(o !== undefined, $result === o.val)
  if (!o) return fallback;
  return o.val;
}

// Field-chain early-return: !o.inner narrows o.inner to Inner after the if
function negField(o: Outer, fallback: number): number {
  //@ ensures implies(o.inner === undefined, $result === fallback)
  //@ ensures implies(o.inner !== undefined, $result === o.inner.val)
  if (!o.inner) return fallback;
  return o.inner.val;
}

// Bare optional truthiness: `if (o)` is the same as `if (o !== undefined)`.
function truthyVar(o: Inner | undefined, fallback: number): number {
  //@ ensures implies(o !== undefined, $result === o.val)
  //@ ensures implies(o === undefined, $result === fallback)
  if (o) return o.val;
  return fallback;
}

// Chained `&&` of optional checks in a ternary — both checks narrow.
// Tests that ruleConditionalAndOptional walks its inner conditional so
// nested optional checks become nested someMatches.
function nestedAndTernary(o: Outer | undefined, fallback: number): number {
  //@ ensures implies(o === undefined, $result === fallback)
  //@ ensures implies(o !== undefined && o.inner === undefined, $result === fallback)
  //@ ensures implies(o !== undefined && o.inner !== undefined, $result === o.inner.val)
  return o !== undefined && o.inner !== undefined ? o.inner.val : fallback;
}

// ═══════════════════════════════════════════════════════════════
// `'key' in obj` narrowing — discriminate by field presence
// ═══════════════════════════════════════════════════════════════

type Shape =
  | { kind: 'circle'; radius: number }
  | { kind: 'square'; side: number }

// `'radius' in s` narrows s to the variant containing 'radius' (circle).
function area(s: Shape): number {
  //@ ensures implies(s.kind === "circle", $result === s.radius * s.radius)
  //@ ensures implies(s.kind === "square", $result === s.side * s.side)
  if ('radius' in s) return s.radius * s.radius;
  return s.side * s.side;
}

// Negative discriminant + early return: `s.kind !== "circle"` narrows s to
// circle in the rest of the block.
function describeIfCircle(s: Shape, fallback: number): number {
  //@ ensures implies(s.kind === "circle", $result === s.radius * s.radius)
  //@ ensures implies(s.kind === "square", $result === fallback)
  if (s.kind !== 'circle') return fallback;
  return s.radius * s.radius;
}

// Ternary inside a spec exercising option narrowing in the spec language
// itself: the `o !== undefined` check must narrow `o` to `Inner` inside the
// `then` branch so that `o.val` is well-typed.
function ternarySpecOpt(o: Inner | undefined, fallback: number): number {
  //@ ensures $result === (o !== undefined ? o.val : fallback)
  if (o !== undefined) return o.val;
  return fallback;
}

// ═══════════════════════════════════════════════════════════════
// Structural helper boundary from a narrowed union arm
// ═══════════════════════════════════════════════════════════════

// TypeScript permits the rpc-error arm value (which also carries `kind`) to be
// passed to a helper that only exposes this structural view. Dafny and Lean use
// nominal records, so switch lowering must project the matched payload fields
// into RpcErrorView rather than pass the enclosing union value directly.
interface RpcErrorView {
  code: number;
  message: string;
  data?: string;
}

type ProjectedOutcome =
  | { kind: "rpc-error"; code: number; message: string; data?: string }
  | { kind: "done" };

function projectedCodePure(error: RpcErrorView): number {
  //@ ensures $result === error.code
  return error.code;
}

function dispatchProjectedPure(outcome: ProjectedOutcome): number {
  //@ ensures implies(outcome.kind === "rpc-error", $result === outcome.code)
  switch (outcome.kind) {
    case "rpc-error":
      return projectedCodePure(outcome);
    case "done":
      return 0;
  }
}

function projectedCode(error: RpcErrorView): number {
  //@ ensures $result === error.code
  // Keep this helper imperative so the regression exercises method-call
  // lowering, the path used by brownfield helpers containing proof seams.
  let code = error.code;
  return code;
}

function dispatchProjected(outcome: ProjectedOutcome): number {
  //@ ensures implies(outcome.kind === "rpc-error", $result === outcome.code)
  switch (outcome.kind) {
    case "rpc-error":
      return projectedCode(outcome);
    case "done":
      return 0;
  }
}
