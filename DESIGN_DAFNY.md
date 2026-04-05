# LemmaScript — Dafny Backend

**Date:** April 2026

## Overview

The Dafny backend shares the same TypeScript sources, `//@ ` annotations, and pipeline (extract → resolve → transform) as the Lean backend. It differs only in the final two stages: the shared transform is configured with Dafny-specific options, and a Dafny emitter translates the Lean IR to Dafny syntax.

## Architecture

```
TypeScript + //@ annotations
    ↓
extract.ts → resolve.ts → transform.ts (shared, with TransformOptions)
    ↓                           ↓
emit.ts (Lean syntax)    dafny-emit.ts (Dafny syntax from Lean IR)
```

No separate Dafny IR or Dafny transform. The Lean IR is the shared IR. `TransformOptions` configures:
- `backend`: `"lean"` or `"dafny"` — controls `Math.floor` handling and namespace prefixing
- `monadic`: whether to lift method calls into monadic binds (Lean) or regular variables (Dafny)
- `dotMethods` / `methodTable`: backend-specific mappings for array/string operations

The Dafny emitter (`dafny-emit.ts`) translates Lean IR to Dafny by mapping operators (`=` → `==`, `∧` → `&&`), types (`Int` → `int`, `Array Int` → `seq<int>`), and syntax (`.size` → `|s|`, `.toNat` → elided, constructors → qualified).

## Two Files Per Source

| File | Purpose |
|------|---------|
| `foo.dfy.gen` | Generated from TS. Always regeneratable. Merge base. |
| `foo.dfy` | Starts as copy of gen. LLM/user adds proof annotations. Source of truth. |

The `.dfy.gen` extension prevents Dafny tooling from auto-verifying it.

The diff between gen and dfy must be **additions only** — the LLM may insert helper lemmas, ghost predicates, assert statements, and loop invariants, but may not modify generated lines.

## Regeneration

`lsc regen --backend=dafny foo.ts`:
1. Captures patch from current `foo.dfy.gen` → `foo.dfy`
2. Regenerates `foo.dfy.gen`
3. If `foo.dfy` still verifies → done
4. Otherwise, applies captured patch to new gen → new `foo.dfy`
5. If that verifies → done
6. Otherwise → LLM re-adapts

## Key Differences from Lean

| | Lean | Dafny |
|---|---|---|
| Generated files | `.types.lean`, `.def.lean` | `.dfy.gen` |
| User/LLM files | `.spec.lean`, `.proof.lean` | `.dfy` (annotated gen) |
| Proof mechanism | `prove_correct` (external) | Proof lemmas + inline asserts |
| Automation | `loom_solve` (WP + SMT) | Z3/Boogie (direct SMT) |
| Regeneration | Overwrite `.def.lean` | Regenerate `.dfy.gen`, patch-merge into `.dfy` |
| Integer division | `Math.floor` erased (Lean `/` floors) | `Math.floor(a/b)` → `JSFloorDiv(a, b)` (inlined) |
| Arrays | `Array T` (value semantics) | `seq<T>` (immutable) |
| String ops | `JSString.indexOf`, `JSString.slice` | `StringIndexOf` (inlined), `s[lo..hi]` |
| Pure functions | `def` in `Pure` namespace + `method` wrapper | `function` (no wrapper, no namespace) |
| Requires on Pure defs | Dropped — Pure defs are total; Velvet `method` enforces requires | Emitted as `requires` preconditions on `function` |
| Array access | `arr[i]!` (unchecked, default on OOB) | `arr[i]` (Dafny verifier checks bounds via requires) |
| Soundness | Lean kernel | Dafny verifier, no `{:verify false}` |

## Status

Verified case studies:
- **cal.com** `hasOverlap` — 2 verified
- **casbin** `arrayEquals`, `effectorPure`, `keyMatch`, `keyGet`, `getFilteredPolicy` — 18 verified
- **clear-split** `logic` — 7 verified
- **colorwheel** `colorwheel` — 22 verified
