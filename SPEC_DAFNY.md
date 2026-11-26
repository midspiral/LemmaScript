# LemmaScript — Dafny Backend Specification

This document covers what is unique to the Dafny backend. See [SPEC.md](SPEC.md) for the shared annotation language, translation rules, type mapping, and pipeline.

---

## 1. Project Structure

For each verified TS function `foo.ts`, there are two Dafny files:

| File | Who writes it | Purpose |
|------|--------------|---------|
| `foo.dfy.gen` | `lsc gen` | Generated from TS. Always regeneratable. Merge base. |
| `foo.dfy` | LLM / User | Starts as copy of gen. Proof annotations added here. Source of truth. |

The `.dfy.gen` extension prevents Dafny tooling from auto-verifying it.

The diff between gen and dfy must be **additions only** — the LLM may insert helper lemmas, ghost predicates, assert statements, and loop invariants, but may not modify generated lines.

Added lines may not contain `assume`, `expect`, `decreases *`, `{:axiom}`, `@Axiom`, `{:verify ...}` (other than `{:verify true}`), `{:only}`, `@VerifyOnly`, or `{:extern}`; occurrences inside comments, strings, and character literals are ignored. Inside a generated declaration header, added lines may introduce complete `ensures`, `modifies`, `reads`, or `decreases` clauses (other than `decreases *`), but may not add `requires` clauses or extend or split a generated signature or header clause; auxiliary declarations added in the proof may declare their own clauses freely. Added lines also may not introduce an `// lsc options:` line, since verifier options are read from that header.

`"proof-dir": "proofs"` in `lemmascript.json` relocates the complete Dafny
artifact set while preserving the pair: a source `src/search/foo.ts` under that
config uses `proofs/src/search/foo.dfy.gen` and `proofs/src/search/foo.dfy`.
Regen state (`.dfy.base` and `.dfy.merged`) lives there too. The path is relative
to the config file, and source subdirectories are mirrored to prevent basename
collisions. The source must be below the config directory. When enabling the
option, move the hand-written `.dfy`; `.dfy.gen` can be regenerated. If `lsc`
finds an existing beside-source proof but no mapped proof, it fails instead of
silently seeding a new `.dfy`. Lean artifacts are not affected by this option.

---

## 2. Pure Functions

Pure TS functions become Dafny `function` declarations (no wrapper, no namespace). `requires` and `ensures` are emitted directly. If the function has `ensures`, a companion `lemma` is generated as a proof target for the LLM:

```dafny
function clamp(v: int, lo: int, hi: int): int
  requires lo <= hi
{
  if v < lo then lo
  else if v > hi then hi
  else v
}

lemma clamp_ensures(v: int, lo: int, hi: int)
  requires lo <= hi
  ensures clamp(v, lo, hi) >= lo
  ensures clamp(v, lo, hi) <= hi
{
}
```

Non-pure functions become Dafny `method` declarations.

---

## 3. Regeneration Workflow

`lsc regen --backend=dafny foo.ts`:

1. Read old `foo.dfy.gen` before overwriting
2. Regenerate `foo.dfy.gen`
3. If `foo.dfy` doesn't exist → create from gen, verify unless `--no-verify`, done
4. Choose the existing `.dfy.base`, or otherwise the old gen, as the anchor; merge (`git merge-file`) when the new gen differs
5. Check additions-only invariant
6. Verify merged `foo.dfy` unless `--no-verify`; if verification fails, advance `.dfy.base` to the new gen before exiting with failure
7. On success, delete `.dfy.base` (gen is now the anchor), including when verification was explicitly skipped

On merge conflict, `foo.dfy` is left unchanged and the merged result is saved as `foo.dfy.merged` for manual inspection. Conflicts and additions-only failures retain the old anchor. `lsc gen`, `lsc gen-check`, and `lsc check` also seed `.dfy.base` with the previous `.dfy.gen` before overwriting a changed generation beside an existing `.dfy` when no `.dfy.base` exists yet, so a later `lsc regen` still merges from the generation the proof derives from; `check` and `gen-check` remove `.dfy.base` once the additions-only check passes. A verifier failure after a clean additions-only merge instead retains the new anchor, because the proof already contains that generation; the next retry must not merge it a second time.

Merges use `--diff-algorithm=minimal`, matching the additions-only check so large proof additions do not cause spurious generated-line deletions in the diff. Git versions before 2.44 fall back to the default algorithm with a warning; upgrading avoids the resulting false conflicts. Git execution errors leave the proof unchanged and retain the old anchor, but do not create `.dfy.merged` or record a verification conflict.

---

## 4. Helper Preambles

The Dafny emitter auto-injects helper functions when needed. Each is emitted at most once, only when a construct that requires it appears (registry: `PREAMBLE_CODE` in `dafny-emit.ts`).

**Core:**

| Helper | When | Purpose |
|--------|------|---------|
| `Option<T>` | `Map.get`, single-sentinel optional types (`T \| undefined` or `T \| null`) | `datatype Option<T> = None \| Some(value: T)` |
| `Nullish<T>` | Three-state nullable types (`T \| null \| undefined`, `x?: T \| null`) | `datatype Nullish<T> = Undefined \| Null \| Value(value: T)` |
| `SetToSeq` | `for (x of set)`, map/record iteration | Convert set to sequence for iteration |
| `SetFromSeq` | `new Set(arr)` | Build a deduplicated set from a sequence (`set x \| x in s`) |

`Nullish` exposes `.Undefined?`, `.Null?`, and `.Value?` discriminators; accessing `.value` requires the `Value` case. See [SPEC.md §3.9](SPEC.md#39-map-set-and-optional-narrowing) for comparison and narrowing semantics.

**Numeric:**

| Helper | When | Purpose |
|--------|------|---------|
| `JSFloorDiv` | `Math.floor(a/b)` (int args) | JS-compatible floor division |
| `FloorReal` / `CeilReal` | `Math.floor(x)` / `Math.ceil(x)` (real arg); `Math.round(x)` as `FloorReal(x + 0.5)` | `real → int` via `.Floor` |
| `JSTruncDiv` | `Math.trunc(a/b)` (int/nat args), `bigint /` | JS-compatible truncated division |
| `TruncReal` | `Math.trunc(x)` (real arg) | `real → int` toward zero |
| `MathAbs` / `MathMin` / `MathMax` | `Math.abs/min/max` (int args) | Scalar integer abs/min/max |
| `MathAbsReal` / `MathMinReal` / `MathMaxReal` | `Math.abs/min/max` (any real arg) | Scalar real abs/min/max; int/nat operands coerced with `as real` |
| `MaxOfSeq` / `MinOfSeq` | `Math.max(...s)` / `Math.min(...s)` | Aggregate over a sequence (requires `\|s\| > 0`) |
| `MaxOfSeqReal` / `MinOfSeqReal` | `Math.max/min` with a real spread or mixed real/integer segments | Real extrema over a nonempty sequence; `Concat` lemmas transfer bounds through concatenation |
| `SeqIntToReal` | Integer spread mixed with real operands | Convert elements to real, preserving length and each indexed value |
| `Pow2` / `BitAnd` | `<<` / `>>` / `&` on `bigint` | Bitwise ops as arithmetic |
| `NatToString` / `IntToString` | `` `${n}` `` template literal (nat / signed int) | Number-to-digit-string for interpolation (`IntToString` prefixes `-`) |

`Math.trunc` and `Math.round` are the identity on `int`/`nat` arguments. `Math.round` rounds halfway ties toward `+Infinity` (`Math.round(-2.5) == -2`). These lowerings use exact reals, so there is no `-0`, `NaN`, or `Infinity`. JS `Math.round` returns the nearest integer without rounding `x + 0.5`, so it agrees with `FloorReal(x + 0.5)` on every finite double (`Math.round(0.49999999999999994)` is `0` in both). A `bigint` argument is a compile error.

**Sequence:**

| Helper | When | Purpose |
|--------|------|---------|
| `SeqIndexOf` | `arr.indexOf(x)` | First-index search (`-1` if absent) |
| `CallbackIndices` | Array callbacks (other than `map`) that use index or source-array arguments | Ordered positions `[0, ..., n-1]`, with proved length, indexing, and membership contracts |
| `SeqFilter` / `SeqAll` / `SeqFoldLeft` | `filter` / `every` / `reduce` with `dafny-library: local` | Local recursive collection helpers (no Dafny standard-library dependency) |
| `SeqFindIndex` | `arr.findIndex(f)` | Predicate first-index search |
| `SeqFind` | `arr.find(f)` | Predicate first-match search |
| `SeqFindLast` | `arr.findLast(f)` | Predicate last-match search |
| `SeqFilterSome` | filterMap pattern (§3.7) | Drop `None`s and unwrap to `seq<T>` |
| `SeqFlatten` | `arr.flat()` | Flatten one level |
| `SeqJoin` | `arr.join(sep)` | Join into a string |
| `SafeSlice` | `arr.slice(lo, hi)` with effective `safe-slice: true` | Bounds-clamping slice |
| `Perm` | `perm(a, b)` (spec-only) | `predicate Perm<T(==)>(a, b) { multiset(a) == multiset(b) }` |

**String:**

| Helper | When | Purpose |
|--------|------|---------|
| `StringIndexOf` | `s.indexOf(sub)`, `s.indexOf(sub, from)`, `s.includes(sub)` | Recursive string search (also provides `StringIndexOfFrom`) |
| `StringSearchPosition` | Explicit positions in `indexOf`, `includes`, `startsWith`, `endsWith` | Clamp integer positions to the string length |
| `StringStartsWithAt` / `StringEndsWithAt` | Explicit positions in `startsWith` / `endsWith`, respectively | Test a prefix or suffix at the clamped position |
| `StringSplit` | `s.split(d)` | Axiomatic split (`1 <= \|res\| <= \|s\| + 1`) |
| `StringTrim` | `s.trim()` / `s.trimEnd()` / `s.trimStart()` | Trim (also provides `StringTrimRight` / `StringTrimLeft`); strips the full ECMAScript whitespace set via `IsJSWhitespace`, not just `' '` |
| `StringToLower` / `StringToUpper` | `s.toLowerCase()` / `s.toUpperCase()` | Axiomatic case conversion: equals `AsciiToLower(s)` / `AsciiToUpper(s)` when `StringIsAscii(s)`, otherwise unconstrained |

**String semantics.** Set `string-semantics` in `lemmascript.json` or a file's
`//@ option` directive (SPEC.md §7.6). Proofs depend on the selected model:

| Setting | Meaning |
|---|---|
| `"unicode-scalar"` (default) | Strings are Unicode scalar sequences. `.length`, indexing, `slice`, `charCodeAt`, and `indexOf` can differ from JavaScript for characters such as emoji. Unpaired surrogates are unsupported. |
| `"javascript-utf16"` | Strings are UTF-16 code-unit sequences. `.length`, indexing, `slice`, and `charCodeAt` use JavaScript code-unit positions and values; indexing and slicing retain the fragment's bounds obligations. Requires `"dafny-library": "local"`. |

In both profiles, case conversion is specified only for ASCII input. `String.fromCharCode` requires
a Unicode scalar in the default profile, or `0 <= n < 0x10000` in UTF-16 mode.
Generated files record every UTF-16 selection in their header;
the default profile adds no `string-semantics` setting.

**Collection helpers.** `dafny-library` selects standard-library helpers (`stdlib`,
the default) or generated helpers (`local`) for `filter`, `every`, and `reduce`.
Unicode-scalar mode supports either; UTF-16 mode requires an explicit `local` setting.

This choice does not change string semantics or control handwritten proof imports.
Those imports must still be compatible with the selected string model (see §5).
Both settings support file directives; see [examples/utf16.ts](examples/utf16.ts).

**Indexed callbacks.** In either library mode, `CallbackIndices(n)` constructs `[0, ..., n-1]` as a `seq<int>`:

```dafny
function CallbackIndices(n: nat): (r: seq<int>)
  ensures |r| == n
  ensures forall i :: 0 <= i < n ==> r[i] == i
  ensures forall i :: i in r <==> 0 <= i < n
{
  if n == 0 then [] else CallbackIndices(n - 1) + [n - 1]
}
```

Callers get the length, order, and membership facts without unfolding it. The adapter binds the receiver once and iterates these positions, passing `(source[i], i, source)` (after the accumulator for `reduce`); `filter` and `find` map selected positions back to elements, and `map` skips the helper, since its `seq` comprehension already has the position in hand. An existential `some` proof may need a witness such as `assert 1 in CallbackIndices(2);` — see [examples/callbackArguments.dfy](examples/callbackArguments.dfy).

---

## 5. Verification

`lsc check --backend=dafny foo.ts`:

1. Generate `foo.dfy.gen` + seed `foo.dfy`
2. Check additions-only invariant
3. Run `dafny verify foo.dfy`

Standard libraries are auto-detected: if `foo.dfy` contains `import Std.`, the `--standard-libraries` flag is added.

`lsc` verifies each `.dfy` using the string semantics recorded in its generated
header, even if the project configuration has changed. A file without a
`string-semantics` header uses `unicode-scalar`.

Proof additions must preserve the generated file's string model. Conflicting or
duplicate model settings are errors, including when verification is skipped.

Proofs using `javascript-utf16` cannot import Dafny's precompiled standard library
(`Std.*`); verification reports an error if they do. Proofs using `unicode-scalar`
can use that library.

The shared `--time-limit=<seconds>` flag (SPEC.md §7) maps to Dafny's `--verification-time-limit`; `--extra-flags=<string>` is forwarded verbatim to `dafny verify`.
