# LemmaScript — Development Notes

Status as of 2026-03-29. Read this before working on the codebase.

## What exists

### End-to-end pipeline (working)

The full loop is closed for binary search:

```
examples/binarySearch.ts          (TypeScript + //@ annotations)
    ↓  tools/src/extract.ts       (ts-morph → JSON IR)
    ↓  tools/src/codegen.ts       (IR → Lean source)
LemmaScript/BinarySearch.lean     (generated Velvet method + prove_correct)
    +  LemmaScript/BinarySearchSpec.lean  (hand-written ghost defs)
    ↓  lake build                 (Loom/Velvet/Z3)
    ✔  Verified (4.5s, fully automated by loom_solve)
```

Run it:
```sh
cd tools && npx tsx src/lsc.ts check ../examples/binarySearch.ts
```

### Files

**Lean side:**
- `LemmaScript/BinarySearch.lean` — Generated from binarySearch.ts. Velvet `method` + `prove_correct by loom_solve`. All VCs discharged automatically.
- `LemmaScript/BinarySearchSpec.lean` — Ghost `sorted` predicate. Tagged `@[grind, loomAbstractionSimp]`. This is what the user writes.
- `lakefile.lean` — Depends on Velvet (local `../velvet`) → Loom (git). Z3/cvc5 download targets.
- Lean toolchain: **v4.24.0** (must match Loom and Velvet).

**Node.js toolchain (`tools/`):**
- `src/extract.ts` — ts-morph extractor. Parses TS, extracts `//@ ` annotations, outputs structured IR.
- `src/specparser.ts` — Recursive descent parser for the `//@ ` expression language. Tokenizer → AST → Lean emitter. Handles `forall`, `==>`, `===`, `arr.length`, `arr[i]`, `Math.floor`, quantifiers, etc.
- `src/codegen.ts` — IR → Lean/Velvet source. Return-in-loop transformation, type mapping, invariant/decreases/done_with emission.
- `src/lsc.ts` — CLI entry point. `lsc check <file.ts>` runs the full pipeline.

**Examples:**
- `examples/binarySearch.ts` — The motivating example. TypeScript with `//@ ` annotations.

**Design:**
- `DESIGN.md` — v0.2. Architecture: TS + `//@ ` comments + `.spec.lean` files, no custom language.

## Hard-won constraints (read before changing anything)

### 1. Use Int everywhere, never Nat in specs

Velvet wraps values in `WithName` (transparent abbrev). If invariants quantify over `k : Int` but postconditions quantify over `k : Nat`, `loom_solve` fails and manual proof is painful (fighting WithName wrappers + struct tuple equalities).

**Rule:** All quantifiers in generated Lean use `Int`. Array access uses `arr[k.toNat]!`.

### 2. Use `arr.size` not `↑arr.size`

Let Lean coerce Nat→Int automatically. Explicit `↑` coercion disrupts `loom_solve`'s ability to discharge array bounds VCs. The specparser emits `arr.size` (not `↑arr.size`) for `arr.length`.

### 3. Normalize `>=` to `≤` (flip operands)

`loom_solve` handles `≤` and `<` but not `≥` and `>`. The specparser flips: `result >= -1` → `-1 ≤ result`. This is non-obvious and easy to regress on.

### 4. Return-inside-loop needs explicit result invariant from user

TypeScript `return mid` inside a `while` is transformed to:
- `let mut result := <sentinel>` (from the final `return` after the loop)
- `result := mid; break` (replaces the in-loop `return`)
- `done_with result ≠ <sentinel> ∨ ¬(<condition>)`

The code generator handles this transformation. BUT: the user must write an invariant about the result variable, because `loom_solve` needs it and the right invariant can't be auto-derived from postconditions.

For binary search, the user writes:
```
//@ invariant result === -1 || (result >= 0 && result < arr.length && arr[result] === target)
```

The weaker bound `-1 ≤ result` (derived from ensures) is NOT sufficient — `loom_solve` needs `0 ≤ result` to reason about array index bounds. Only the user knows that `result` comes from a non-negative index.

### 5. `(A && B) ==> C` curries to `A → B → C`

The specparser flattens the LHS of implications: `forall(k, 0 <= k && k < lo ==> arr[k] !== target)` becomes `∀ k : Int, 0 ≤ k → k < lo → arr[k.toNat]! ≠ target`. This is more idiomatic Lean and matches what `loom_solve` expects. Top-level `&&` in ensures/requires/invariants is split into separate clauses.

### 6. Spec file must be importable by Lake

Ghost definitions live in `.spec.lean` files. Currently placed at `LemmaScript/BinarySearchSpec.lean` so Lake can import them. The codegen doesn't yet handle spec file discovery — the import is added manually. This needs fixing.

## What's next

### Immediate (close gaps in the pipeline)
1. **Spec file discovery** — codegen should find `<name>.spec.lean` next to the TS file and generate the correct import
2. **More examples** — array sum, linear search, insertion sort. Each exercises different patterns (no loop return, nested loops, array mutation)
3. **Error reporting** — surface Lean verification errors back to TS source locations (line mapping from generated Lean back to TS)

### Phase 2 (tooling)
4. **VS Code extension** — `//@ ` annotation autocomplete, inline verification status
5. **`lsc check --watch`** — re-verify on file changes
6. **`lsc init`** — scaffold `.spec.lean` for a TS file
7. **LLM proof filling** — when `loom_solve` fails, extract goals and use lean-lsp-mcp

### Phase 3 (language expansion)
8. **For-of loops** — `for (const x of arr)` → Lean `for` with ForIn
9. **Object types** — `{ field: T }` → Lean structures
10. **Higher-order functions** — `arr.map(f)` with contracts on callbacks
11. **Multiple functions per file** — inter-function specs and calls

## Dependencies

- **Lean 4**: v4.24.0 (via elan)
- **Loom**: git master (fetched by Lake via Velvet dependency)
- **Velvet**: local at `../velvet` (must be present, toolchain must match)
- **Node.js**: for ts-morph tools
- **ts-morph**: ^25.0.0, **tsx**: ^4.0.0 (in `tools/`)
