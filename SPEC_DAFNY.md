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

On merge conflict, the original `foo.dfy` is restored and the merged result is saved as `foo.dfy.merged` for manual inspection. Conflicts and additions-only failures retain the old anchor. A verifier failure after a clean additions-only merge instead retains the new anchor, because the proof already contains that generation; the next retry must not merge it a second time.

---

## 4. Helper Preambles

The Dafny emitter auto-injects helper functions when needed. Each is emitted at most once, only when a construct that requires it appears (registry: `PREAMBLE_CODE` in `dafny-emit.ts`).

**Core:**

| Helper | When | Purpose |
|--------|------|---------|
| `Option<T>` | `Map.get`, optional types | `datatype Option<T> = None \| Some(value: T)` |
| `SetToSeq` | `for (x of set)`, map/record iteration | Convert set to sequence for iteration |
| `SetFromSeq` | `new Set(arr)` | Build a deduplicated set from a sequence (`set x \| x in s`) |

**Numeric:**

| Helper | When | Purpose |
|--------|------|---------|
| `JSFloorDiv` | `Math.floor(a/b)` (int args) | JS-compatible floor division |
| `FloorReal` / `CeilReal` | `Math.floor(x)` / `Math.ceil(x)` (real arg) | `real → int` via `.Floor` |
| `MathAbs` / `MathMin` / `MathMax` | `Math.abs/min/max(a, b)` | Scalar abs/min/max |
| `MaxOfSeq` / `MinOfSeq` | `Math.max(...s)` / `Math.min(...s)` | Aggregate over a sequence (requires `\|s\| > 0`) |
| `Pow2` / `BitAnd` | `<<` / `>>` / `&` on `bigint` | Bitwise ops as arithmetic |
| `NatToString` / `IntToString` | `` `${n}` `` template literal (nat / signed int) | Number-to-digit-string for interpolation (`IntToString` prefixes `-`) |

**Sequence:**

| Helper | When | Purpose |
|--------|------|---------|
| `SeqIndexOf` | `arr.indexOf(x)` | First-index search (`-1` if absent) |
| `SeqFilter` / `SeqAll` / `SeqFoldLeft` | `filter` / `every` / `reduce` | Local recursive collection helpers (no Dafny standard-library dependency) |
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
| `StringSplit` | `s.split(d)` | Axiomatic split (`1 <= \|res\| <= \|s\| + 1`) |
| `StringTrim` | `s.trim()` / `s.trimEnd()` / `s.trimStart()` | Trim (also provides `StringTrimRight` / `StringTrimLeft`); strips the full ECMAScript whitespace set via `IsJSWhitespace`, not just `' '` |
| `StringToLower` / `StringToUpper` | `s.toLowerCase()` / `s.toUpperCase()` | Case folding |

**String profile.** `string-semantics` in `lemmascript.json` (SPEC.md §7.6) selects which model of JavaScript strings a proof is made under; each is a named identity the proof's claims are relative to (DESIGN_STRINGS.md):

| Identity | `lemmascript.json` | Claim |
|---|---|---|
| `unicode-scalar-1` | `"unicode-scalar"` (default) | Dafny `string` under `--unicode-char:true`: strings are Unicode scalar sequences. `.length`, indexing, `slice`, `charCodeAt`, and `indexOf` are over scalars and differ from JavaScript for astral text; unpaired surrogates are outside the domain (refused in literals; `String.fromCharCode` requires a scalar); case mapping is ASCII-only. No header token. |
| `javascript-utf16-1` | `"javascript-utf16"` | Dafny `string` under `--unicode-char:false`: strings are UTF-16 code-unit sequences. `.length`, indexing, `slice`, `charCodeAt`, and `String.fromCharCode` (`0 <= n < 0x10000`) are exact; `filter`/`every`/`reduce` use local `SeqFilter`/`SeqAll`/`SeqFoldLeft` helpers because the Dafny standard library cannot load in this mode; case mapping is ASCII-only. Generated files carry `// lsc options: string-semantics=javascript-utf16`. |

---

## 5. Verification

`lsc check --backend=dafny foo.ts`:

1. Generate `foo.dfy.gen` + seed `foo.dfy`
2. Check additions-only invariant
3. Run `dafny verify foo.dfy`

Standard libraries are auto-detected: if `foo.dfy` contains `import Std.`, the `--standard-libraries` flag is added.

The char mode is read from the artifact, not the config, so a standalone `.dfy`
verifies under the model it was generated for: `dafnyVerify` pins
`--unicode-char:true` unless the header carries
`// lsc options: string-semantics=javascript-utf16`, in which case it passes
`--unicode-char:false --allow-deprecation` (only the `:false` value is deprecated
in Dafny 4.11; `--allow-deprecation` waives exactly that warning, whereas
`--allow-warnings` would also un-fatal vacuity and missing-`{:axiom}` warnings).
Dafny's precompiled standard library cannot load under `--unicode-char:false`, so
a `javascript-utf16` proof whose additions import `Std.*` fails closed with an
error naming `string-semantics`; a `unicode-scalar` proof may use it freely.

The shared `--time-limit=<seconds>` flag (SPEC.md §7) maps to Dafny's `--verification-time-limit`; `--extra-flags=<string>` is forwarded verbatim to `dafny verify`.

