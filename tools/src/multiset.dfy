/// Multiset (bag) operations verified in Dafny.
/// Each method mirrors an immutable TypeScript counterpart in multiset.ts.

module TSMultiset {


// ============================================================================
// Constructors
// ============================================================================

method Empty<T>() returns (m: multiset<T>)
  ensures m == multiset{}
{
  m := multiset{};
}

lemma MultisetUpdateAdd<T>(m: multiset<T>, x: T)
  ensures m[x := m[x] + 1] == m + multiset{x}
{
}

method FromSeq<T>(s: seq<T>) returns (m: multiset<T>)
  ensures m == multiset(s)
{
  m := multiset{};
  for i := 0 to |s|
    invariant m == multiset(s[0..i])
  {
    assert s == s[0..i] + [s[i]] + s[(i+1)..];
    MultisetUpdateAdd(m, s[i]);
    m := m[s[i] := m[s[i]] + 1];
  }
  assert s[0..|s|] == s;
}

method FromString(s: string) returns (m: multiset<char>)
  ensures m == multiset(s)
{
  m := multiset{};
  for i := 0 to |s|
    invariant m == multiset(s[0..i])
  {
    assert s == s[0..i] + [s[i]] + s[(i+1)..];
    MultisetUpdateAdd(m, s[i]);
    m := m[s[i] := m[s[i]] + 1];
  }
  assert s[0..|s|] == s;
}

// ============================================================================
// Queries
// ============================================================================

method Size<T>(m: multiset<T>) returns (n: nat)
  ensures n == |m|
{
  n := 0;
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
}

method Count<T>(m: multiset<T>, x: T) returns (c: nat)
  ensures c == m[x]
{
  c := m[x];
}

// ============================================================================
// Immutable updates
// ============================================================================

method Add<T>(m: multiset<T>, x: T) returns (r: multiset<T>)
  ensures r == m + multiset{x}
{
  r := m + multiset{x};
}

method Remove<T>(m: multiset<T>, x: T) returns (r: multiset<T>)
  ensures r == m - multiset{x}
{
  r := m - multiset{x};
}

method AddN<T>(m: multiset<T>, x: T, n: nat) returns (r: multiset<T>)
  ensures r[x] == m[x] + n
  ensures forall y:T :: y != x ==> r[y] == m[y]
{
  r := m[x := m[x] + n];
}

method RemoveN<T>(m: multiset<T>, x: T, n: nat) returns (r: multiset<T>)
  ensures r[x] == if m[x] >= n then m[x] - n else 0
  ensures forall y:T :: y != x ==> r[y] == m[y]
{
  r := m[x := if m[x] >= n then m[x] - n else 0];
}

// ============================================================================
// Relations
// ============================================================================

method Equals<T>(a: multiset<T>, b: multiset<T>) returns (eq: bool)
  ensures eq <==> a == b
{
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
  eq := true;
}

method Subset<T>(a: multiset<T>, b: multiset<T>) returns (isSub: bool)
  ensures isSub <==> a <= b
{
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
  isSub := true;
}

// ============================================================================
// Set-like operations
// ============================================================================

/// Union — element-wise maximum multiplicity.
method Union<T>(a: multiset<T>, b: multiset<T>) returns (r: multiset<T>)
  ensures r == (a + b) - (a * b)
{
  r := a;
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
}

/// Intersection — element-wise minimum multiplicity.
method Intersection<T>(a: multiset<T>, b: multiset<T>) returns (r: multiset<T>)
  ensures r == a * b
{
  r := multiset{};
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
}

/// Difference — remove multiplicities of b from a (clamped at zero).
method Difference<T>(a: multiset<T>, b: multiset<T>) returns (r: multiset<T>)
  ensures r == a - b
{
  r := a;
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
}

/// Sum — element-wise addition of multiplicities.
method Sum<T>(a: multiset<T>, b: multiset<T>) returns (r: multiset<T>)
  ensures r == a + b
{
  r := a;
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
}

// ============================================================================
// Conversion
// ============================================================================

method ToSeq<T>(m: multiset<T>) returns (s: seq<T>)
  ensures multiset(s) == m
{
  s := [];
  var remaining := m;
  while remaining != multiset{}
    invariant multiset(s) + remaining == m
    decreases |remaining|
  {
    var k :| k in remaining;
    var count := remaining[k];
    for j := 0 to count
      invariant multiset(s) + remaining - multiset{}[k := j] == m
    {
      s := s + [k];
    }
    remaining := remaining[k := 0];
  }
}

// ============================================================================
// Convenience: anagram check
// ============================================================================

method IsAnagram(s: string, t: string) returns (eq: bool)
  ensures eq <==> multiset(s) == multiset(t)
{
  var smset := FromString(s);
  var tmset := FromString(t);
  eq := Equals(smset, tmset);
}

}
