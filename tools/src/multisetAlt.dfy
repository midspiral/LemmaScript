/// Multiset (bag) operations as `function ... by method`.
///
/// Each operation here is the same as in multiset.dfy, but wrapped as a
/// Dafny `function` whose spec body uses the native multiset operator
/// directly (e.g. `a == b`, `a + b`, `multiset(s)`). The `by method`
/// block reproduces the verified imperative implementation, so the
/// function is callable from compiled code while remaining transparent
/// in verification contexts.
///
/// Why have this on top of multiset.dfy?
///   - `function`s can appear in `requires` / `ensures` / `invariant`
///     clauses and inside other `function` bodies; `method`s cannot.
///     Callers that want to spec against `Equals(a, b)` (instead of the
///     raw `a == b` operator) need the `function` form here.
///
/// Performance note
///   For run-time use, prefer the native Dafny operator directly:
///     `a == b`, `a + b`, `a - b`, `a * b`, `|m|`, `m[x]`, `multiset(s)`.
///   Dafny evaluates these primitively. The `by method` shims below are
///   element-by-element iterations that exist to mirror the TypeScript
///   counterpart in multiset.ts — they are O(|m|) where the operator is
///   O(1) (for the comparison/arithmetic forms) or a single VM call.
///   The `function` body is what verifiers see; the `by method` is only
///   reached when this code is actually compiled and executed.

module TSMultisetAlt {


// ============================================================================
// Constructors
// ============================================================================

function Empty<T>(): multiset<T>
{
  multiset{}
} by method {
  return multiset{};
}

lemma MultisetUpdateAdd<T>(m: multiset<T>, x: T)
  ensures m[x := m[x] + 1] == m + multiset{x}
{
}

function FromSeq<T>(s: seq<T>): multiset<T>
{
  multiset(s)
} by method {
  var m: multiset<T> := multiset{};
  for i := 0 to |s|
    invariant m == multiset(s[0..i])
  {
    assert s == s[0..i] + [s[i]] + s[(i+1)..];
    MultisetUpdateAdd(m, s[i]);
    m := m[s[i] := m[s[i]] + 1];
  }
  assert s[0..|s|] == s;
  return m;
}

function FromString(s: string): multiset<char>
{
  multiset(s)
} by method {
  var m: multiset<char> := multiset{};
  for i := 0 to |s|
    invariant m == multiset(s[0..i])
  {
    assert s == s[0..i] + [s[i]] + s[(i+1)..];
    MultisetUpdateAdd(m, s[i]);
    m := m[s[i] := m[s[i]] + 1];
  }
  assert s[0..|s|] == s;
  return m;
}

// ============================================================================
// Queries
// ============================================================================

function Size<T>(m: multiset<T>): nat
{
  |m|
} by method {
  var n: nat := 0;
  var remaining := m;
  while remaining != multiset{}
    invariant n + |remaining| == |m|
    decreases |remaining|
  {
    var k :| k in remaining;
    n := n + remaining[k];
    var d := multiset{}[k := remaining[k]];
    remaining := remaining - d;
  }
  return n;
}

function Count<T>(m: multiset<T>, x: T): nat
{
  m[x]
} by method {
  return m[x];
}

// ============================================================================
// Immutable updates
// ============================================================================

function Add<T>(m: multiset<T>, x: T): multiset<T>
{
  m + multiset{x}
} by method {
  return m + multiset{x};
}

function Remove<T>(m: multiset<T>, x: T): multiset<T>
{
  m - multiset{x}
} by method {
  return m - multiset{x};
}

function AddN<T>(m: multiset<T>, x: T, n: nat): multiset<T>
{
  m[x := m[x] + n]
} by method {
  return m[x := m[x] + n];
}

function RemoveN<T>(m: multiset<T>, x: T, n: nat): multiset<T>
{
  m[x := if m[x] >= n then m[x] - n else 0]
} by method {
  return m[x := if m[x] >= n then m[x] - n else 0];
}

// ============================================================================
// Relations
// ============================================================================

function Equals<T>(a: multiset<T>, b: multiset<T>): bool
{
  a == b
} by method {
  if |a| != |b| { return false; }
  ghost var processed: multiset<T> := multiset{};
  var remaining := a;
  while remaining != multiset{}
    invariant a == processed + remaining
    invariant processed !! remaining
    invariant forall x :: x in processed ==> a[x] == b[x]
    decreases |remaining|
  {
    var k :| k in remaining;
    if a[k] != b[k] { return false; }
    var d := multiset{}[k := remaining[k]];
    processed := processed + d;
    remaining := remaining - d;
  }
  assert processed == a;
  assert forall x :: x in a ==> a[x] == b[x];
  assert a <= b;
  // a <= b and |a| == |b| ==> a == b:
  // b - a + a == b (multiset identity when a <= b), so |b-a| + |a| == |b|, hence |b-a| == 0
  assert b - a + a == b;
  assert |b - a| + |a| == |b|;
  assert |b - a| == 0;
  assert b - a == multiset{};
  return true;
}

function Subset<T>(a: multiset<T>, b: multiset<T>): bool
{
  a <= b
} by method {
  ghost var processed: multiset<T> := multiset{};
  var remaining := a;
  while remaining != multiset{}
    invariant a == processed + remaining
    invariant processed !! remaining
    invariant forall x :: x in processed ==> a[x] <= b[x]
    decreases |remaining|
  {
    var k :| k in remaining;
    if b[k] < a[k] { return false; }
    var d := multiset{}[k := remaining[k]];
    processed := processed + d;
    remaining := remaining - d;
  }
  assert processed == a;
  assert forall x :: x in a ==> a[x] <= b[x];
  return true;
}

// ============================================================================
// Set-like operations
// ============================================================================

/// Union — element-wise maximum multiplicity.
function Union<T>(a: multiset<T>, b: multiset<T>): multiset<T>
{
  (a + b) - (a * b)
} by method {
  var r := a;
  ghost var processed: multiset<T> := multiset{};
  var remaining := b;
  while remaining != multiset{}
    invariant b == processed + remaining
    invariant processed !! remaining
    invariant r == (a + processed) - (a * processed)
    decreases |remaining|
  {
    var k :| k in remaining;
    if b[k] > r[k] {
      r := r[k := b[k]];
    }
    var d := multiset{}[k := remaining[k]];
    processed := processed + d;
    remaining := remaining - d;
  }
  assert processed == b;
  return r;
}

/// Intersection — element-wise minimum multiplicity.
function Intersection<T>(a: multiset<T>, b: multiset<T>): multiset<T>
{
  a * b
} by method {
  var r: multiset<T> := multiset{};
  ghost var processed: multiset<T> := multiset{};
  var remaining := a;
  while remaining != multiset{}
    invariant a == processed + remaining
    invariant processed !! remaining
    invariant r == processed * b
    decreases |remaining|
  {
    var k :| k in remaining;
    var mn := if a[k] <= b[k] then a[k] else b[k];
    if a[k] > 0 && b[k] > 0 {
      r := r[k := mn];
    }
    var d := multiset{}[k := remaining[k]];
    processed := processed + d;
    remaining := remaining - d;
  }
  assert processed == a;
  return r;
}

/// Difference — remove multiplicities of b from a (clamped at zero).
function Difference<T>(a: multiset<T>, b: multiset<T>): multiset<T>
{
  a - b
} by method {
  var r := a;
  ghost var processed: multiset<T> := multiset{};
  var remaining := b;
  while remaining != multiset{}
    invariant b == processed + remaining
    invariant processed !! remaining
    invariant r == a - processed
    decreases |remaining|
  {
    var k :| k in remaining;
    var va := r[k];
    var vb := b[k];
    if va <= vb {
      r := r[k := 0];
    } else {
      r := r[k := va - vb];
    }
    var d := multiset{}[k := remaining[k]];
    processed := processed + d;
    remaining := remaining - d;
  }
  assert processed == b;
  return r;
}

/// Sum — element-wise addition of multiplicities.
function Sum<T>(a: multiset<T>, b: multiset<T>): multiset<T>
{
  a + b
} by method {
  var r := a;
  ghost var processed: multiset<T> := multiset{};
  var remaining := b;
  while remaining != multiset{}
    invariant b == processed + remaining
    invariant processed !! remaining
    invariant r == a + processed
    decreases |remaining|
  {
    var k :| k in remaining;
    r := r[k := r[k] + remaining[k]];
    var d := multiset{}[k := remaining[k]];
    processed := processed + d;
    remaining := remaining - d;
  }
  assert processed == b;
  return r;
}

// ============================================================================
// Conversion
// ============================================================================

// ToSeq is intentionally omitted from this file: its spec
// `multiset(s) == m` doesn't determine s uniquely (any permutation
// of the elements satisfies it), so it cannot be expressed as a
// (deterministic) `function`. Callers that need a sequence form
// should use the `method` version in multiset.dfy.

// ============================================================================
// Convenience: anagram check
// ============================================================================

function IsAnagram(s: string, t: string): bool
{
  multiset(s) == multiset(t)
} by method {
  var smset := FromString(s);
  var tmset := FromString(t);
  return Equals(smset, tmset);
}

}
