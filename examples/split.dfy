/// Verified `Split` for strings — adapted from
///   https://github.com/hath995/dafny-aoc-2024/blob/main/parser/split.dfy
///
/// `Split(s, separator)` returns a sequence of pieces whose join with
/// `separator` equals `s` and (when the separator is non-empty) contains
/// no piece in which the separator appears. The empty separator
/// degenerates to a one-character split.
///
/// The proof is broken into four bands inside the module:
///   - Joins: `Join`, `JoinWithTrailingSeparator`, `TotalLength`
///   - Containment: `Contains` + `NeedleSlice` / `UnderLength` / `NotNeedleSlice`
///   - Split state predicates: `IsNextStartingIndex`, `IsFinalIndex`,
///     `EndsWithSeparator`, `AllPartsNotPostfix(OrEnd)`
///   - Lemmas about containment, joins, and split (in that order)
/// followed by the split functions themselves and the `export provides`
/// declaration.

module Split {

  // ════════════════════════════ Joins ════════════════════════════

  /// Join a sequence of strings with `separator` between adjacent pieces
  /// (no trailing separator).
  function Join(ss: seq<string>, separator: string): string {
    if |ss| == 0 then ""
    else if |ss| == 1 then ss[0]
    else ss[0] + separator + Join(ss[1..], separator)
  }

  /// Join with a separator emitted *after* every piece (used as the
  /// "what has already been consumed" measure inside `SplitFrom`).
  function JoinWithTrailingSeparator(ss: seq<string>, separator: string): string {
    if |ss| == 0 then ""
    else ss[0] + separator + JoinWithTrailingSeparator(ss[1..], separator)
  }

  /// Sum of the element lengths of `xs`.
  function TotalLength(xs: seq<string>): nat {
    if |xs| == 0 then 0
    else |xs[|xs|-1]| + TotalLength(xs[..|xs|-1])
  }

  /// Wrapper around `*` so Z3 treats the multiplication in the
  /// `IsNextStartingIndex` / `IsFinalIndex` predicates opaquely.
  /// Inlining the `*` slows `SplitFrom` verification by ~25× — see
  /// the original split.dfy and the standard Dafny perf advice.
  function Prod(x: int, y: int): int { x * y }

  // ═════════════════════════ Containment ═════════════════════════

  predicate Contains(haystack: string, needle: string)
    ensures Contains(haystack, needle) <==>
      exists k :: 0 <= k <= |haystack| && needle <= haystack[k..]
    ensures !Contains(haystack, needle) <==>
      forall i :: 0 <= i <= |haystack| ==> !(needle <= haystack[i..])
  {
    if needle <= haystack then
      assert haystack[0..] == haystack;
      true
    else if |haystack| > 0 then
      assert forall i :: 1 <= i <= |haystack| ==> haystack[i..] == haystack[1..][(i-1)..];
      Contains(haystack[1..], needle)
    else
      false
  }

  /// The separator-sized slice of `s` starting at `k`.
  function NeedleSlice(s: string, separator: string, k: nat): string
    requires |separator| > 0
    requires UnderLength(s, separator, k)
  {
    s[k..k+|separator|]
  }

  /// There is room for a full separator starting at `k`.
  predicate UnderLength(s: string, separator: string, k: nat)
    requires |separator| > 0
  {
    k + |separator| <= |s|
  }

  /// The separator-sized slice at `k` differs from `separator`.
  predicate NotNeedleSlice(s: string, separator: string, k: nat)
    requires |separator| > 0
    requires UnderLength(s, separator, k)
  {
    NeedleSlice(s, separator, k) != separator
  }

  // ═══════════════════ Split state predicates ═══════════════════

  /// Total characters consumed after `|results|` pieces plus their
  /// joining separators equals `sindex`.
  predicate IsNextStartingIndex(sindex: nat, separator: string, results: seq<string>) {
    Prod(|results|, |separator|) + TotalLength(results) == sindex
  }

  predicate IsFinalIndex(s: string, separator: string, results: seq<string>) {
    Prod(|results| - 1, |separator|) + TotalLength(results) == |s|
  }

  /// `s` extended with one separator has a separator at some position
  /// other than the trivial tail.
  predicate EndsWithSeparator(s: string, separator: string)
    requires |separator| > 0
  {
    Contains((s + separator)[..|s| + |separator| - 1], separator)
  }

  predicate AllPartsNotPostfix(results: seq<string>, separator: string)
    requires |separator| > 0
    requires |results| > 0
  {
    forall i :: 0 <= i < |results| ==> !EndsWithSeparator(results[i], separator)
  }

  predicate AllPartsNotPostfixOrEnd(results: seq<string>, separator: string)
    requires |separator| > 0
    requires |results| > 0
  {
    forall i :: 0 <= i < |results| - 1 ==> !EndsWithSeparator(results[i], separator)
  }

  // ═══════════════════ Containment lemmas ═══════════════════════

  lemma OversizedSeparatorNotContained(s: string, separator: string)
    requires |separator| > |s|
    ensures !Contains(s, separator)
  {
  }

  lemma ContainedMeansFits(s: string, separator: string)
    requires Contains(s, separator)
    ensures |s| >= |separator|
  {
  }

  /// Witness for the existential in `Contains` — an index where the
  /// separator starts.
  lemma ContainsImpliesIndex(s: string, separator: string) returns (j: nat)
    requires |separator| > 0
    requires Contains(s, separator)
    ensures 0 <= j < |s| && j + |separator| <= |s| && separator == s[j..j+|separator|]
  {
    var k :| 0 <= k < |s| && separator <= s[k..];
    assert s[k..] == separator + s[k+|separator|..];
    assert s[k..] == s[k..k+|separator|] + s[k+|separator|..];
    assert separator <= s[k..k+|separator|];
    return k;
  }

  /// Converse of `ContainsImpliesIndex` — a concrete witness suffices.
  lemma IndexImpliesContains(s: string, separator: string, j: nat)
    requires |separator| > 0
    requires j < |s|
    requires j + |separator| <= |s|
    requires separator == s[j..j+|separator|]
    ensures Contains(s, separator)
  {
    assert separator <= s[j..];
  }

  /// If no needle-sized slice in `[si, i)` matches and the tail past `i`
  /// is too short to fit one, no match starts anywhere in `[si, |haystack|)`.
  /// (forall form — extends the no-match property to the suffix.)
  lemma RemainderHasNoMatchAtLeast(haystack: string, needle: string, i: nat, si: nat)
    requires i < |haystack|
    requires si <= i < |haystack|
    requires |needle| > 0
    requires i + |needle| > |haystack|
    requires forall k :: si <= k < i ==> UnderLength(haystack, needle, k) ==> NotNeedleSlice(haystack, needle, k)
    ensures forall k :: si <= k < |haystack| ==> UnderLength(haystack, needle, k) ==> NotNeedleSlice(haystack, needle, k)
  {
    RemainderHasNoMatch(haystack, needle, i, si);
  }

  /// Same hypothesis as `RemainderHasNoMatchAtLeast`, conclusion as
  /// `!Contains(haystack[si..], needle)`.
  lemma RemainderHasNoMatch(haystack: string, needle: string, i: nat, si: nat)
    requires i < |haystack|
    requires si <= i < |haystack|
    requires |needle| > 0
    requires i + |needle| > |haystack|
    requires forall k :: si <= k < i ==> UnderLength(haystack, needle, k) ==> NotNeedleSlice(haystack, needle, k)
    ensures !Contains(haystack[si..], needle)
  {
    if |haystack| - |needle| >= si {
      if Contains(haystack[si..], needle) {
        var j := ContainsImpliesIndex(haystack[si..], needle);
        if si + j < i {
          var k := si + j;
          assert si <= k < i;
          if UnderLength(haystack, needle, k) {
            assert k + |needle| < |haystack|;
            assert haystack[si..] == haystack[si..k] + haystack[k..k+|needle|] + haystack[k+|needle|..];
            assert needle <= haystack[k..];
            assert !NotNeedleSlice(haystack, needle, k);
            assert haystack[k..k+|needle|] == needle;
            assert false;
          } else {
            assert k + |needle| >= |haystack|;
            assert |haystack[k..]| <= |needle|;
            assert Contains(haystack[k..], needle);
            assert false;
          }
        } else {
          OversizedSeparatorNotContained(haystack[si+j..], needle);
          assert false;
        }
        assert false;
      }
    }
  }

  // ════════════════════════ Join lemmas ═════════════════════════

  /// `Join(ss) == JoinWithTrailingSeparator(init) + last`.
  lemma JoinUnfoldLast(ss: seq<string>, separator: string)
    requires |ss| > 0
    ensures Join(ss, separator) ==
      JoinWithTrailingSeparator(ss[..|ss|-1], separator) + ss[|ss|-1]
  {
    if |ss| == 1 {
    } else {
      assert |ss| > 1;
      JoinUnfoldLast(ss[1..], separator);
      assert Join(ss[1..], separator) ==
        JoinWithTrailingSeparator(ss[1..][..|ss[1..]|-1], separator) + ss[1..][|ss[1..]|-1];
      assert ss[|ss|-1] == ss[1..][|ss[1..]|-1];
      assert ss[1..][..|ss[1..]|-1] == ss[1..|ss|-1];
    }
  }

  /// `JoinWithTrailingSeparator` distributes over `+` on the input.
  lemma JoinTrailingConcat(ss: seq<string>, xx: seq<string>, separator: string)
    ensures JoinWithTrailingSeparator(ss + xx, separator) ==
      JoinWithTrailingSeparator(ss, separator) + JoinWithTrailingSeparator(xx, separator)
  {
    if |ss| == 0 {
      calc { ss + xx; [] + xx; xx; }
    } else if |xx| == 0 {
      calc { ss + []; ss + []; ss; }
    } else {
      JoinTrailingConcat(ss[1..], xx, separator);
      calc {
        JoinWithTrailingSeparator(ss + xx, separator);
        (ss + xx)[0] + separator + JoinWithTrailingSeparator((ss + xx)[1..], separator);
        {
          assert (ss + xx)[0] == ss[0];
          assert (ss + xx)[1..] == ss[1..] + xx;
        }
        ss[0] + separator + JoinWithTrailingSeparator(ss[1..] + xx, separator);
        ss[0] + separator + JoinWithTrailingSeparator(ss[1..], separator) + JoinWithTrailingSeparator(xx, separator);
      }
    }
  }

  // ══════════════════════ Split lemmas ══════════════════════════

  lemma NoNeedleSlicesImpliesNoSeparatorSlice(
      s: string, separator: string, index: nat, sindex: nat,
      results: seq<string>, k: nat)
    requires index <= |s|
    requires sindex <= |s|
    requires sindex <= index
    requires |separator| > 0
    requires index + |separator| <= |s|
    requires k < index - sindex
    requires !Contains(s[sindex..index], separator)
    requires |results| > 0 ==> AllPartsNotPostfix(results, separator)
    requires forall k :: sindex <= k < index ==> UnderLength(s, separator, k) ==> NotNeedleSlice(s, separator, k)
    ensures exists d :: (0 < d <= |separator| ==> s[sindex+k..sindex+k+d] != separator[..d])
  {
    if forall d :: 0 < d <= |separator| ==> s[sindex+k..sindex+k+d] == separator[..d] {
      assert UnderLength(s, separator, sindex+k);
      assert separator[..|separator|] == separator;
      assert s[sindex+k..sindex+k+|separator|] == separator;
      assert !NotNeedleSlice(s, separator, sindex+k);
      assert sindex <= sindex+k < index;
      assert false;
    }
  }

  /// At a confirmed separator boundary at `index`, the current piece
  /// `s[sindex..index]` cannot itself end in a separator postfix.
  lemma {:isolate_assertions} NotSepIsPostfix(
      s: string, separator: string, index: nat, sindex: nat, results: seq<string>)
    requires index < |s|
    requires sindex <= |s|
    requires sindex <= index
    requires |separator| > 0
    requires |results| > 0 ==> AllPartsNotPostfix(results, separator)
    requires index + |separator| <= |s|
    requires !Contains(s[sindex..index], separator)
    requires forall k :: sindex <= k < index ==> UnderLength(s, separator, k) ==> NotNeedleSlice(s, separator, k)
    requires s[index..index+|separator|] == separator
    ensures !EndsWithSeparator(s[sindex..index], separator)
  {
    var piece := s[sindex..index];
    if EndsWithSeparator(piece, separator) {
      var t_prefix := (piece + separator)[..|piece| + |separator| - 1];
      assert Contains(t_prefix, separator);

      var k := ContainsImpliesIndex(t_prefix, separator);

      if k + |separator| <= |piece| {
        // Case 1: match fully contained within `piece`.
        assert t_prefix[k..k+|separator|] == piece[k..k+|separator|];
        assert separator == t_prefix[k..k+|separator|];
        assert separator == piece[k..k+|separator|];
        IndexImpliesContains(piece, separator, k);
        assert Contains(piece, separator);
        assert false;
      } else {
        // Case 2: match straddles the boundary between `piece` and
        // `separator[..|separator|-1]`. The straddling match reaches
        // forward into the genuine separator that begins at `index`.
        var k_prime := sindex + k;

        assert sindex <= k_prime < index by {
          assert k + |separator| <= |t_prefix|;
          assert k + |separator| <= |piece| + |separator| - 1;
          assert k <= |piece| - 1;
          assert k_prime == sindex + k < sindex + |piece| == index;
        }

        assert UnderLength(s, separator, k_prime) by {
          assert index + |separator| <= |s|;
          assert k_prime + |separator| < index + |separator| <= |s|;
        }

        assert s[k_prime..k_prime+|separator|] == separator by {
          var part1 := s[k_prime..index];
          var len1 := |part1|;
          var part2 := s[index..k_prime+|separator|];
          var len2 := |part2|;

          assert separator == t_prefix[k..k+|separator|];

          var match_part1 := piece[k..];
          var match_part2 := separator[..len2];
          assert |match_part1| == len1;
          assert separator == match_part1 + match_part2;

          // Border-of-`separator` decomposition.
          assert match_part1 == separator[..len1];
          assert match_part2 == separator[len1..];

          assert part1 == piece[k..] == match_part1;
          assert part1 == separator[..len1];

          assert part2 == s[index..index+len2];
          assert s[index..index+len2] == separator[..len2];
          assert separator[..len2] == match_part2;
          assert part2 == separator[len1..];

          assert s[k_prime..k_prime+|separator|] == part1 + part2;
          assert s[k_prime..k_prime+|separator|] == separator[..len1] + separator[len1..];
          assert s[k_prime..k_prime+|separator|] == separator;
        }

        assert NotNeedleSlice(s, separator, k_prime);
        assert !NotNeedleSlice(s, separator, k_prime);
        assert false;
      }
    }
  }

  /// Closing the accumulator: when `index == |s|`, the final piece
  /// appended to `results` contains no separator.
  lemma LastPartContainsNoSeparator(
      s: string, separator: string, index: nat, sindex: nat,
      results: seq<string>, next: seq<string>)
    requires index == |s|
    requires sindex <= |s|
    requires sindex <= index
    requires |separator| > 0
    requires forall res :: res in results ==> !Contains(res, separator)
    requires next == results + [s[sindex..index]]
    requires forall k :: sindex <= k < index ==> UnderLength(s, separator, k) ==> NotNeedleSlice(s, separator, k)
    ensures forall res :: res in next ==> !Contains(res, separator)
  {
    assert s[sindex..index] == s[sindex..];
    if Contains(s[sindex..], separator) {
      var j := ContainsImpliesIndex(s[sindex..], separator);
      var k := sindex + j;
      assert sindex <= k < index;
      assert UnderLength(s, separator, k);
      assert NotNeedleSlice(s, separator, k);
      assert s[sindex..k+|separator|] == s[sindex..][..j+|separator|];
      assert NeedleSlice(s, separator, j) == separator;
      assert !NotNeedleSlice(s[sindex..index], separator, j);
      assert false;
    }
  }

  /// At a confirmed separator boundary, the appended piece
  /// `s[sindex..index]` contains no separator.
  lemma PartsBeforeMatchContainNoSeparator(
      s: string, separator: string, index: nat, sindex: nat, results: seq<string>)
    requires index <= |s|
    requires sindex <= |s|
    requires sindex <= index
    requires |separator| > 0
    requires forall res :: res in results ==> !Contains(res, separator)
    requires forall k :: sindex <= k < index ==> UnderLength(s, separator, k) ==> NotNeedleSlice(s, separator, k)
    requires index + |separator| <= |s|
    requires s[index..index+|separator|] == separator
    ensures forall res :: res in results + [s[sindex..index]] ==> !Contains(res, separator)
  {
    if Contains(s[sindex..index], separator) {
      var j := ContainsImpliesIndex(s[sindex..index], separator);
      var k := sindex + j;
      assert sindex <= k < index;
      assert UnderLength(s, separator, k);
      assert k + |separator| <= index;
      assert s[sindex..k+|separator|] == s[sindex..index][..j+|separator|];
      assert NotNeedleSlice(s, separator, k);
      assert !NotNeedleSlice(s[sindex..index], separator, j);
      assert false;
    }
  }

  lemma {:induction} SplitToCharsTail(s: string, i: int)
    requires 0 <= i < |s|
    ensures Join(SplitToChars(s, 0, [])[i..], "") == s[i..]
    decreases |s| - i
  {
  }

  lemma SplitToCharsRoundTrip(s: string)
    ensures Join(SplitToChars(s, 0, []), "") == s
  {
    if |s| == 0 {
      assert s == "";
      assert SplitToChars(s, 0, []) == [];
      assert Join([], "") == "";
    } else if |s| == 1 {
      assert SplitToChars(s, 0, []) == [s[0..1]];
    } else {
      assert s == s[0..];
      SplitToCharsTail(s, 0);
      assert |SplitToChars(s, 0, [])| == |s|;
      assert 0 <= 1 < |SplitToChars(s, 0, [])|;
      assert SplitToChars(s, 0, [])[0] == s[0..1];
    }
  }

  // ══════════════════════ Split functions ════════════════════════

  /// Char-by-char "split" — each character becomes a one-char string.
  function SplitToChars(s: string, index: int, results: seq<string>): seq<string>
    requires 0 <= index <= |s|
    requires forall i :: 0 <= i < index <= |results| ==> s[i..i+1] == results[i]
    requires |results| == index
    ensures forall i :: 0 <= i < |s| <= |SplitToChars(s, index, results)| ==> s[i..i+1] == SplitToChars(s, index, results)[i]
    ensures |SplitToChars(s, index, results)| == |s|
    decreases |s| - index
  {
    if index < |s| then
      SplitToChars(s, index+1, results + [s[index..index+1]])
    else
      results
  }

  /// Recursive split-with-accumulator: scans `s` from `index`, with the
  /// current piece starting at `sindex` and finalised pieces in `results`.
  function SplitFrom(s: string, separator: string, index: nat, sindex: nat, results: seq<string>): seq<seq<char>>
    requires index <= |s|
    requires sindex <= |s|
    requires sindex <= index
    requires |separator| > 0
    requires |results| <= index
    requires |results| == 0 ==> sindex == 0
    requires |results| > 0 ==> IsNextStartingIndex(sindex, separator, results) && AllPartsNotPostfix(results, separator)
    requires forall k :: sindex <= k < index ==> UnderLength(s, separator, k) ==> NotNeedleSlice(s, separator, k)
    requires JoinWithTrailingSeparator(results, separator) == s[..sindex]
    requires forall res :: res in results ==> !Contains(res, separator)
    ensures results <= SplitFrom(s, separator, index, sindex, results)
    ensures forall res :: res in SplitFrom(s, separator, index, sindex, results) ==> !Contains(res, separator)
    ensures 1 <= |SplitFrom(s, separator, index, sindex, results)| <= |s| + 1
    ensures Join(SplitFrom(s, separator, index, sindex, results), separator) == s
    ensures AllPartsNotPostfixOrEnd(SplitFrom(s, separator, index, sindex, results), separator)
    decreases |s| - index
  {
    if index == |s| then
      var next := results + [s[sindex..index]];
      JoinUnfoldLast(next, separator);
      LastPartContainsNoSeparator(s, separator, index, sindex, results, next);
      next
    else if index + |separator| > |s| then
      RemainderHasNoMatchAtLeast(s, separator, index, sindex);
      SplitFrom(s, separator, |s|, sindex, results)
    else if s[index..index+|separator|] == separator then
      assert s[..index+|separator|] == s[..sindex] + s[sindex..index+|separator|];
      JoinTrailingConcat(results, [s[sindex..index]], separator);
      PartsBeforeMatchContainNoSeparator(s, separator, index, sindex, results);
      NotSepIsPostfix(s, separator, index, sindex, results);
      assert !EndsWithSeparator(s[sindex..index], separator);
      SplitFrom(s, separator, index+|separator|, index+|separator|, results + [s[sindex..index]])
    else
      SplitFrom(s, separator, index+1, sindex, results)
  }

  /// Public API: split `s` on `separator`. Empty separator → split to chars.
  function Split(s: string, separator: string): seq<string>
    ensures Join(Split(s, separator), separator) == s
    ensures |separator| > 0 ==>
      forall piece :: piece in Split(s, separator) ==> !Contains(piece, separator)
    ensures |separator| > 0 && |s| > 0 && |Split(s, separator)| > 0 ==> AllPartsNotPostfixOrEnd(Split(s, separator), separator)
  {
    if |separator| == 0 then
      SplitToCharsRoundTrip(s);
      SplitToChars(s, 0, [])
    else
      SplitFrom(s, separator, 0, 0, [])
  }

  function SplitLines(s: string): seq<string> {
    if Contains(s, "\r\n") then Split(s, "\r\n") else Split(s, "\n")
  }

  function SplitParagraphs(s: string): seq<string> {
    if Contains(s, "\r\n") then Split(s, "\r\n\r\n") else Split(s, "\n\n")
  }

  export provides Split, Contains, SplitLines, SplitParagraphs, Join, AllPartsNotPostfixOrEnd 
}
