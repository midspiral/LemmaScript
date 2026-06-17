# LemmaScript — Dafny Backend Specification

**Version:** 0.5.7
**Date:** June 2026

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
3. If `foo.dfy` doesn't exist → create from gen, verify, done
4. If gen changed → three-way merge (`git merge-file`) using old gen as base
5. Check additions-only invariant
6. Verify merged `foo.dfy`
7. On success, delete `.dfy.base` (gen is now the anchor)

On merge conflict, the original `foo.dfy` is restored and the merged result is saved as `foo.dfy.merged` for manual inspection.

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
| `SeqFindIndex` | `arr.findIndex(f)` | Predicate first-index search |
| `SeqFindLast` | `arr.findLast(f)` | Predicate last-match search |
| `SeqFilterSome` | filterMap pattern (§3.7) | Drop `None`s and unwrap to `seq<T>` |
| `SeqFlatten` | `arr.flat()` | Flatten one level |
| `SeqJoin` | `arr.join(sep)` | Join into a string |
| `SafeSlice` | `arr.slice(lo, hi)` under `//@ safe-slice` | Bounds-clamping slice |
| `Perm` | `perm(a, b)` (spec-only) | `predicate Perm<T(==)>(a, b) { multiset(a) == multiset(b) }` |

**String:**

| Helper | When | Purpose |
|--------|------|---------|
| `StringIndexOf` | `s.indexOf(sub)`, `s.indexOf(sub, from)`, `s.includes(sub)` | Recursive string search (also provides `StringIndexOfFrom`) |
| `StringSplit` | `s.split(d)` | Axiomatic split (`1 <= \|res\| <= \|s\| + 1`) |
| `StringTrim` | `s.trim()` / `s.trimEnd()` / `s.trimStart()` | Trim (also provides `StringTrimRight` / `StringTrimLeft`) |
| `StringToLower` / `StringToUpper` | `s.toLowerCase()` / `s.toUpperCase()` | Case folding |

---

## 5. Verification

`lsc check --backend=dafny foo.ts`:

1. Generate `foo.dfy.gen` + seed `foo.dfy`
2. Check additions-only invariant
3. Run `dafny verify foo.dfy`

Standard libraries are auto-detected: if `foo.dfy` contains `import Std.`, the `--standard-libraries` flag is added.

The shared `--time-limit=<seconds>` flag (SPEC.md §7) maps to Dafny's `--verification-time-limit`; `--extra-flags=<string>` is forwarded verbatim to `dafny verify`.


