# LemmaScript — Development Notes

Status as of 2026-03-29. Read this before working on the codebase.

## What exists

### Lean side (verified, builds clean)

- **`LemmaScript/BinarySearch.lean`** — Binary search verified via Velvet's `method` macro on Loom. Ghost `sorted` predicate, 7 loop invariants, `break` for early return, total correctness with termination. `loom_solve` discharges all VCs automatically in ~5s.
- **`lakefile.lean`** — Depends on Velvet (local path `../velvet`), which depends on Loom (git). Includes Z3/cvc5 download targets copied from Velvet's lakefile.
- Lean toolchain: **v4.24.0** (must match Loom and Velvet).

### Node.js side (working prototype)

- **`tools/src/extract.ts`** — ts-morph-based extractor. Parses a `.ts` file, extracts `//@ ` annotations, associates them with AST nodes, outputs structured JSON IR. Run with `cd tools && npx tsx src/extract.ts ../examples/binarySearch.ts`.
- **`examples/binarySearch.ts`** — The motivating example. TypeScript with `//@ requires`, `//@ ensures`, `//@ invariant`, `//@ decreases` annotations.

### Design

- **`DESIGN.md`** — v0.2. The architecture: TS + `//@ ` comments + `.spec.lean` files. No custom language.

## What we learned (Phase 0 findings)

### 1. Use Int everywhere in the Loom embedding

Velvet wraps values in `WithName` (a transparent abbrev), but this interacts badly with Lean's `simp`/`dsimp` when types don't match syntactically. If loop invariants quantify over `k : Int` but postconditions quantify over `k : Nat`, `loom_solve` fails and manual proof requires fighting `WithName` wrappers + struct tuple equalities.

**Rule: the code generator must emit Int-typed quantifiers throughout.** Nat-indexed array access uses `arr[k.toNat]!`. This is a hard constraint.

### 2. Return-inside-loop requires transformation

TypeScript `return mid` from inside a `while` loop doesn't map directly to Velvet/Loom. The code generator must transform it to:
- Introduce a `result` mutable variable (init to sentinel, e.g., -1)
- Replace `return x` with `result := x; break`
- Add `done_with` clause capturing exit conditions
- Use `result` in the final `return`

The binary search example demonstrates this pattern.

### 3. loom_solve handles binary search fully automatically

No manual lemmas, no helper functions, no SMT hints. The `sorted` ghost function tagged `@[grind, loomAbstractionSimp]` plus well-written invariants is enough. Z3/cvc5 + Lean's `grind` handle the arithmetic and array reasoning.

### 4. Velvet's method syntax works well as a target

The code generator could emit Velvet `method` declarations directly rather than raw Loom monadic code. This gives us `require`/`ensures`/`invariant`/`done_with`/`decreasing`/`break` for free, plus `prove_correct` and `loom_solve`. No need to build LemmaScript-specific Lean macros in Phase 1.

### 5. ts-morph extraction is clean

The extractor correctly handles:
- `//@ ` annotations on functions (requires, ensures) and loops (invariant, decreases)
- Full control flow IR: let, while, if/else chains, return, assignment
- Mutable vs const detection
- Module-level `//@ import` annotations

Annotations are placed as comments before the first statement of the function body (for requires/ensures) or before the first statement inside the loop body (for invariant/decreases). The extractor checks both leading comments on the node and on the first child.

## Architecture for the code generator (not yet built)

```
binarySearch.ts          →  ts-morph extract  →  IR (JSON)
                                                    ↓
binarySearch.spec.lean   →                    →  .lsc/binarySearch.lean
                                                 (Velvet method + prove_correct)
                                                    ↓
                                                 lake build → verified / errors
```

The code generator (Phase 1) needs to:

1. **Parse the IR** from the extractor
2. **Emit a Velvet `method`** declaration:
   - Map TS params → Lean params (number → Int, number[] → Array Int, etc.)
   - Map `//@ requires` → `require`
   - Map `//@ ensures` → `ensures`
   - Map let/const → `let` / `let mut`
   - Map while + `//@ invariant` → `while ... invariant ... decreasing ... do`
   - Transform return-inside-loop to break + result variable
   - Map if/else → `if ... then ... else ...`
   - Map array access `arr[i]` → `arr[i.toNat]!`
   - Map `Math.floor((a + b) / 2)` → `(a + b) / 2` (Int division in Lean)
3. **Emit `prove_correct`** with `loom_solve`
4. **Import the `.spec.lean`** file for ghost definitions
5. **Translate the `//@ ` expression language** to Lean terms:
   - `forall(k, P)` → `∀ k : Int, P`
   - `==>` → `→`
   - `===` → `=`
   - `!==` → `≠`
   - `&&` → `∧`
   - `||` → `∨`
   - `arr.length` → `↑arr.size`
   - Ghost function calls by name

## What's next (Phase 1)

1. **Build the code generator** (`tools/src/codegen.ts`): IR → Lean source emission
2. **Build the `//@ ` expression parser** (`tools/src/specparser.ts`): TS-flavored spec expressions → Lean syntax
3. **Wire it into `lsc check`** (`tools/src/cli.ts`): parse TS → generate .lean → invoke `lake build` → report results
4. **More examples**: array sum, insertion sort, linear search — validate the code generator on different patterns
5. **Error reporting**: surface Lean verification errors back to TS source locations

## Dependencies

- **Lean 4**: v4.24.0 (via elan)
- **Loom**: git master (fetched by Lake via Velvet dependency)
- **Velvet**: local at `../velvet` (must be present and its toolchain must match)
- **Node.js**: for ts-morph tools
- **ts-morph**: ^25.0.0
- **tsx**: ^4.0.0 (dev runner)
