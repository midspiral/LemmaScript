/** A multiset (bag) represented as a map from elements to their multiplicities. */
export type Multiset<T> = Map<T, number>;

/** Create an empty multiset. */
export function empty<T>(): Multiset<T> {
  return new Map();
}

/** Create a multiset from an iterable of elements. */
export function from<T>(iter: Iterable<T>): Multiset<T> {
  const m: Multiset<T> = new Map();
  for (const x of iter) {
    m.set(x, (m.get(x) ?? 0) + 1);
  }
  return m;
}

/** Create a multiset from a string (elements are characters). */
export function fromString(s: string): Multiset<string> {
  return from(s);
}

/** Return the total number of elements (counting multiplicity). */
export function size<T>(m: Multiset<T>): number {
  let n = 0;
  for (const [, c] of m) n += c;
  return n;
}

/** Return the multiplicity of an element. */
export function count<T>(m: Multiset<T>, x: T): number {
  return m.get(x) ?? 0;
}

/** Add one instance of an element (returns a new multiset). */
export function add<T>(m: Multiset<T>, x: T): Multiset<T> {
  const r = new Map(m) as Multiset<T>;
  r.set(x, (r.get(x) ?? 0) + 1);
  return r;
}

/** Remove one instance of an element (returns a new multiset). */
export function remove<T>(m: Multiset<T>, x: T): Multiset<T> {
  const r = new Map(m) as Multiset<T>;
  const c = r.get(x) ?? 0;
  if (c <= 1) r.delete(x);
  else r.set(x, c - 1);
  return r;
}

/** Add *n* instances of an element (returns a new multiset). */
export function addN<T>(m: Multiset<T>, x: T, n: number): Multiset<T> {
  if (n <= 0) return new Map(m) as Multiset<T>;
  const r = new Map(m) as Multiset<T>;
  r.set(x, (r.get(x) ?? 0) + n);
  return r;
}

/** Remove up to *n* instances of an element (returns a new multiset). */
export function removeN<T>(m: Multiset<T>, x: T, n: number): Multiset<T> {
  const r = new Map(m) as Multiset<T>;
  const c = r.get(x) ?? 0;
  if (c <= n) r.delete(x);
  else r.set(x, c - n);
  return r;
}

/** Two multisets are equal when every element has the same multiplicity in both. */
export function equals<T>(a: Multiset<T>, b: Multiset<T>): boolean {
  if (size(a) !== size(b)) return false;
  for (const [k, v] of a) {
    if ((b.get(k) ?? 0) !== v) return false;
  }
  return true;
}

/** *a* is a sub-multiset of *b* when every multiplicity in *a* is <= that in *b*. */
export function subset<T>(a: Multiset<T>, b: Multiset<T>): boolean {
  for (const [k, v] of a) {
    if ((b.get(k) ?? 0) < v) return false;
  }
  return true;
}

/** Union — element-wise maximum multiplicity. */
export function union<T>(a: Multiset<T>, b: Multiset<T>): Multiset<T> {
  const r = new Map(a) as Multiset<T>;
  for (const [k, v] of b) {
    r.set(k, Math.max(r.get(k) ?? 0, v));
  }
  return r;
}

/** Intersection — element-wise minimum multiplicity. */
export function intersection<T>(a: Multiset<T>, b: Multiset<T>): Multiset<T> {
  const r: Multiset<T> = new Map();
  for (const [k, va] of a) {
    const vb = b.get(k) ?? 0;
    if (va > 0 && vb > 0) r.set(k, Math.min(va, vb));
  }
  return r;
}

/** Difference — remove multiplicities of *b* from *a* (clamped at zero). */
export function difference<T>(a: Multiset<T>, b: Multiset<T>): Multiset<T> {
  const r = new Map(a) as Multiset<T>;
  for (const [k, vb] of b) {
    const va = r.get(k) ?? 0;
    if (va <= vb) r.delete(k);
    else r.set(k, va - vb);
  }
  return r;
}

/** Sum — element-wise addition of multiplicities. */
export function sum<T>(a: Multiset<T>, b: Multiset<T>): Multiset<T> {
  const r = new Map(a) as Multiset<T>;
  for (const [k, v] of b) {
    r.set(k, (r.get(k) ?? 0) + v);
  }
  return r;
}

/** Convert a multiset to a flat array (each element repeated by its count). */
export function toArray<T>(m: Multiset<T>): T[] {
  const result: T[] = [];
  for (const [k, v] of m) {
    for (let i = 0; i < v; i++) result.push(k);
  }
  return result;
}

/** Convert a multiset to a string (elements joined). */
export function toString<T>(m: Multiset<T>, joiner = ""): string {
  return toArray(m).map(String).join(joiner);
}

/** Check whether two strings are anagrams. */
export function isAnagram(s: string, t: string): boolean {
  return equals(fromString(s), fromString(t));
}
