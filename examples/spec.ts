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
  //@ ensures e.kind === "lit" ==> \result === e.val
  //@ ensures e.kind === "add" ==> \result === e.a + e.b
  if (e.kind === "lit") return e.val;
  if (e.kind === "add") return e.a + e.b;
  return 0;
}

// §5.4: switch on discriminant → match (exhaustive, no default needed)
function evalSwitch(e: Expr): number {
  //@ ensures e.kind === "lit" ==> \result === e.val
  //@ ensures e.kind === "add" ==> \result === e.a + e.b
  //@ ensures e.kind === "neg" ==> \result === 0 - e.inner
  switch (e.kind) {
    case "lit": return e.val;
    case "add": return e.a + e.b;
    case "neg": return 0 - e.inner;
  }
}

// §8.2: enum-like equality → constructor comparison
function isHighPriority(p: Priority): boolean {
  //@ ensures p === "high" ==> \result === true
  //@ ensures p !== "high" ==> \result === false
  if (p === "high") return true;
  return false;
}

// §8.5: record literal construction
function defaultConfig(): Config {
  //@ ensures \result.threshold === 0 && \result.enabled === true
  return { threshold: 0, maxRetries: 3, enabled: true };
}

// §8.5: record spread / functional update (§4.2)
function withThreshold(c: Config, t: number): Config {
  //@ type t nat
  //@ ensures \result.threshold === t
  //@ ensures \result.enabled === c.enabled
  return { ...c, threshold: t };
}

// Ternary / conditional expression
function clampTernary(x: number, lo: number, hi: number): number {
  //@ requires lo <= hi
  //@ ensures \result >= lo && \result <= hi
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

// §4.2: Math.floor (identity in Int division)
function midpoint(lo: number, hi: number): number {
  //@ ensures \result === (lo + hi) / 2
  return Math.floor((lo + hi) / 2);
}

// §4.2: array literal
function wrapOne(x: number): number[] {
  //@ ensures \result.length === 1
  return [x];
}

function threeElems(a: number, b: number, c: number): number[] {
  //@ ensures \result.length === 3
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
  //@ ensures \result.length === arr.length
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
  //@ ensures \result === 0 - x
  return 0 - x;
}

function negateAll(arr: number[]): number[] {
  //@ ensures \result.length === arr.length
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
  //@ ensures \result <= arr.length
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

// §4.4: implication flattening (A && B ==> C → A → B → C)
// §4.5: conjunction splitting (ensures A && B → two clauses)
// §5.2: done_with, break
function search(arr: number[], target: number): number {
  //@ type i nat
  //@ ensures \result >= -1 && \result < arr.length
  //@ ensures \result >= 0 ==> arr[\result] === target
  //@ ensures arr.length > 0 && \result === -1 ==> forall(k: nat, k < arr.length ==> arr[k] !== target)
  let result = -1;
  let i = 0;
  while (i < arr.length) {
    //@ invariant i <= arr.length
    //@ invariant result === -1 || (result >= 0 && result < arr.length && arr[result] === target)
    //@ invariant forall(k: nat, k < i ==> arr[k] !== target)
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
  //@ ensures \result === true ==> exists(k: nat, k < arr.length && arr[k] === target)
  let found = false;
  for (const x of arr) {
    //@ invariant found === false ==> forall(k: nat, k < _x_idx ==> arr[k] !== target)
    //@ invariant found === true ==> exists(k: nat, k < arr.length && arr[k] === target)
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
  //@ ensures \result.level === "high"
  let tmp = x;  // mutable → non-pure → full method body
  return { level: "high", value: clampTernary(tmp, 0, 100) };
}

// Nested method call: method result passed as arg to another method call
function clampedMidpoint(a: number, b: number): number {
  //@ requires a <= b
  //@ ensures \result >= a && \result <= b
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
  //@ ensures t.middle !== undefined && t.middle.leaf !== undefined ==> \result === t.middle.leaf.value
  //@ ensures t.middle === undefined ==> \result === 0
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
  return o?.inner;
}

// `?.field.field`: ?. then non-? continuation — short-circuit only at first ?
function ocChain(o: Outer | undefined): number | undefined {
  return o?.inner?.val;
}

// `?.foo()`: method call after ?. — peephole collapses set.has to `in`
function ocMethodCall(s: Set<string> | undefined, k: string): boolean | undefined {
  return s?.has(k);
}

// `?.[k]`: index access via ?.[ ] — Record indexes return Option<value>
function ocIndex(m: Record<string, string> | undefined, k: string): string | undefined {
  return m?.[k];
}

// ═══════════════════════════════════════════════════════════════
// Nullish coalescing `a ?? b` — single-eval; defaults if a is undefined
// ═══════════════════════════════════════════════════════════════

// Optional var with default
function nullishVar(o: Inner | undefined, fallback: number): number {
  return o?.val ?? fallback;
}

// Map.get + ?? — peephole collapses to `if k in m then m[k] else fallback`
function nullishMapGet(m: Map<string, number>, k: string, fallback: number): number {
  return m.get(k) ?? fallback;
}

// ═══════════════════════════════════════════════════════════════
// Negative truthiness `if (!x)` — equivalent to `x === undefined`
// ═══════════════════════════════════════════════════════════════

// Var early-return: !o narrows o to Inner after the if
function negVar(o: Inner | undefined, fallback: number): number {
  if (!o) return fallback;
  return o.val;
}

// Field-chain early-return: !o.inner narrows o.inner to Inner after the if
function negField(o: Outer, fallback: number): number {
  if (!o.inner) return fallback;
  return o.inner.val;
}

// Chained `&&` of optional checks in a ternary — both checks narrow.
// Tests that ruleConditionalAndOptional walks its inner conditional so
// nested optional checks become nested someMatches.
function nestedAndTernary(o: Outer | undefined, fallback: number): number {
  return o !== undefined && o.inner !== undefined ? o.inner.val : fallback;
}
