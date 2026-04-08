# DESIGN2 — Dafny-Primary Refactor

**Date:** April 2026

## Motivation

We are making Dafny the primary backend, because it is currently easier for LLMs to verify programs in Dafny than in Lean/Loom/Velvet. This is true, despite a mismatch in tooling where Dafny has a generated stub that needs to be completed to a full verified program.

Beyond swapping the default, the current architecture has accumulated several design debts that a refactoring pass should address:

1. **The shared IR is named after one backend.** Every type is `LeanExpr`, `LeanStmt`, `LeanFile` — even though both backends consume it.
2. **Types are converted to strings too early.** The transform calls `tyToLean()` and embeds Lean type syntax (`"Array Int"`, `"Std.HashMap K V"`) into the IR. The Dafny emitter then regex-parses these strings back into types. This is a lossy round-trip.
3. **Backend-specific concerns leak into the shared transform.** Monadic lifting (Lean-only), `Pure.` namespace prefixes (Lean-only), and `set!` method names (Lean-only) are interleaved with genuinely shared logic.
4. **Global mutable state.** `_opts`, `_liftCounter`, `_forofCounters`, `usedImports` are module-level mutables, set-then-read across function boundaries.
5. **No backend interface.** Each backend's responsibilities are scattered: method mappings in `transform.ts`, type mappings in `types.ts` and `dafny-emit.ts`, file generation in `lsc.ts`.

---

## What Stays the Same

- **Four-phase pipeline**: extract -> resolve -> transform -> emit. This is sound.
- **Three IRs** (Raw, Typed, Backend): three separate representations prevent halfway states.
- **Spec annotations** (`//@ `): unchanged syntax, unchanged parser.
- **Dafny regen workflow**: three-way merge, additions-only invariant — all good.
- **Extract and resolve** are entirely backend-agnostic. No changes needed.

---

## Proposed Changes

### 1. Rename the shared IR to be backend-neutral

**`ir.ts`**: Rename all types.

| Current | Proposed |
|---------|----------|
| `LeanExpr` | `Expr` |
| `LeanStmt` | `Stmt` |
| `LeanDecl` | `Decl` |
| `LeanFile` | `Module` |
| `LeanDef` | `FnDef` |
| `LeanMethod` | `FnMethod` |
| `LeanInductive` | `Inductive` |
| `LeanStructure` | `Structure` |
| `LeanNamespace` | `Namespace` |
| `LeanMatchArm` | `MatchArm` |
| `LeanStmtMatchArm` | `StmtMatchArm` |

This is mechanical. Every import site updates. No semantic change.

### 2. Preserve `Ty` through the IR

Currently the IR stores types as strings (`type: string`). This means the transform must call `tyToLean()` at every type site, and the Dafny emitter must regex-parse those strings back.

**Change**: IR param/field/decl types become `Ty` objects (from `typedir.ts`). Each emitter converts `Ty` to its own syntax at emission time.

```typescript
// Before (ir.ts)
export interface FnDef {
  params: { name: string; type: string }[];
  returnType: string;
  ...
}

// After (ir.ts)
export interface FnDef {
  params: { name: string; type: Ty }[];
  returnType: Ty;
  ...
}
```

Benefits:
- `dafny-emit.ts` gets a clean `Ty` to translate. No regex.
- `types.ts` loses `tyToLean()` — each emitter has its own `tyToString()`.
- The IR is a faithful semantic representation, not a Lean-encoded one.

### 3. Make method names semantic in the IR

Currently the transform chooses backend-specific method names (`"set!"` for Lean, `"with"` for Dafny) via `TransformOptions.dotMethods`. The IR stores these names, and each emitter must know what to do with them.

**Change**: Use semantic method names in the IR, and let each emitter translate.

```typescript
// IR method names (semantic)
"arraySet"    // arr.with(idx, val) in TS
"arrayMap"    // arr.map(fn)
"arrayFilter" // arr.filter(fn)
"mapGet"      // m.get(k)
"mapSet"      // m.set(k, v)
"setHas"      // s.has(x)
// etc.
```

Each emitter maps these to its syntax:
- Lean: `"arraySet"` -> `obj.set! idx val`
- Dafny: `"arraySet"` -> `obj[idx := val]`

This eliminates `TransformOptions.dotMethods` and `TransformOptions.methodTable`. The transform no longer needs to know about backends.

### 4. Method-call lifting: leave as-is for now

Dafny also needs lifting for method calls in expression position (methods are statements in both target languages). The current `binds`-threading approach in `lowerExpr` is shared, but the details differ between backends: Lean has monadic variants (`mapM` vs `map`), HOF body classification, and `bind` vs `let-bind` semantics tied to Velvet. Dafny needs lifting too, but with different rules around what counts as a method vs a function.

Refactoring this correctly requires more care than a rename. Leave the lifting logic and `TransformOptions.monadic` as-is in this pass.

### 5. Move `Pure.` namespacing to the Lean emitter

The `Pure.` namespace prefix for spec-pure calls is a Lean convention (needed because Velvet methods can't appear in spec expressions). Dafny doesn't use it.

Currently: the transform emits `Pure.fnName` calls based on `_opts.backend`. After: the transform emits bare `fnName` calls. The Lean emitter adds the `Pure.` prefix when emitting spec-pure calls.

Similarly, the `Pure` namespace wrapping of pure defs in the types file is Lean-specific and should live in the Lean emitter.

### 6. CLI: support explicit `--backend=lean` and `--backend=dafny`

Currently only `--backend=dafny` is recognized; Lean is the implicit default. Support both flags explicitly, keeping Lean as the default for now.

```typescript
// Before
const backendIdx = args.indexOf("--backend=dafny");
const backend = backendIdx >= 0 ? "dafny" : "lean";

// After: parse --backend=<lean|dafny>
```

```
Usage: lsc <gen|check|regen|extract> [--backend=lean|dafny] <file.ts>
```

### 7. Global mutable state: leave as-is

The transform's module-level mutables (`_opts`, `_liftCounter`, `_forofCounters`, `usedImports`) are all reset at the top of `transformModule` and scoped to a single call. Threading a context object through every function in a 932-line file would add noise without fixing a real bug. Same for the Dafny emitter's `needsX` flags. Not worth the churn.

### 8. Unify file output strategy

Lean's four-file scheme enables generated files to not be edited:
```
foo.types.lean  (generated)
foo.def.lean    (generated)
foo.spec.lean   (user)
foo.proof.lean  (user)
```

Dafny has a two-file scheme:
```
foo.dfy.gen     (generated)
foo.dfy         (user = annotated gen)
```

**No change proposed** to either scheme — they reflect genuine differences in how each prover works. But the Lean-side commands (`gen`, `check`) should be factored into a `lean-commands.ts` parallel to `dafny-commands.ts`, instead of being inline in `lsc.ts`.

### 9. Factor SPEC.md into shared + per-backend docs

SPEC.md is currently Lean-only. It documents the annotation language and pipeline (shared) alongside Lean file layout, import chain, and Velvet/Loom specifics (Lean-only). With Dafny as primary backend, this needs to be restructured.

**Change**: Split into three documents:
- **SPEC.md** — shared: annotation syntax, spec expression grammar, extract/resolve/transform pipeline, IR descriptions
- **SPEC_DAFNY.md** — Dafny-specific: two-file scheme, regen workflow, `dafny verify`, method vs function distinction, helper preambles
- **SPEC_LEAN.md** — Lean-specific: four-file scheme, import chain, Velvet/Loom, monadic lifting, `Pure` namespace, `lake build`

This parallels the code architecture (shared transform + per-backend emitter) and avoids SPEC.md becoming a maze of "if Dafny... if Lean..." toggles.

---

## File Organization After Refactor

```
tools/src/
  lsc.ts              CLI entry point (thin dispatcher)
  extract.ts          Phase 1: TS -> Raw IR (unchanged)
  resolve.ts          Phase 2: Raw IR -> Typed IR (unchanged)
  specparser.ts       Spec annotation parser (unchanged)
  rawir.ts            Raw IR types (unchanged)
  typedir.ts          Typed IR types (unchanged)
  types.ts            TypeDeclInfo, parseTsType (remove tyToLean)
  ir.ts               Backend-neutral IR (renamed types, Ty preserved)
  transform.ts        Phase 3: Typed IR -> IR (backend config for lifting/methods)
  emit-dafny.ts       Phase 4a: IR -> Dafny text (primary)
  emit-lean.ts        Phase 4b: IR -> Lean text
  dafny-commands.ts   Dafny gen/check/regen operations
  lean-commands.ts    Lean gen/check operations (new, extracted from lsc.ts)
```

---

## Migration Plan

Ordered by dependency. Each step is independently testable.

### Step 1: Rename IR types
Mechanical find-and-replace. All tests pass with no semantic change. This is the cheapest change and immediately makes the codebase more honest.

### Step 2: Support explicit `--backend=lean|dafny`
Parse `--backend=` flag properly in `lsc.ts`. Both values accepted, Lean remains default for now. Update help text.

### Step 3: Preserve Ty in the IR
Change IR type fields from `string` to `Ty`. Update transform to stop calling `tyToLean()`. Add `tyToLean(ty: Ty): string` to `emit-lean.ts` and `tyToDafny(ty: Ty): string` to `emit-dafny.ts`. Remove the regex type parsing from `dafny-emit.ts`.

### Step 4: Semantic method names
Replace `TransformOptions.dotMethods`/`methodTable` with a semantic method vocabulary. Update each emitter to map semantic names to syntax.

### Step 5: Extract lean-commands.ts
Move Lean gen/check logic from `lsc.ts` into `lean-commands.ts`. Make `lsc.ts` a thin dispatcher.

### Step 6: Factor SPEC.md
Split SPEC.md into SPEC.md (shared), SPEC_DAFNY.md, SPEC_LEAN.md. Can be done at any point — no code dependency.

---

## What This Does NOT Propose

- **No new IR.** The existing three-level IR (Raw, Typed, Backend) is the right number. Adding a fourth "Dafny IR" would be overengineering — the semantic distance between the shared IR and Dafny syntax is small enough for direct emission.
- **No plugin system.** Two backends don't need a plugin architecture. If a third backend appears, then maybe.
- **No changes to extract or resolve.** These phases are clean and backend-agnostic.
- **No changes to the spec annotation syntax.** `//@ ` works fine.
- **No changes to the Dafny regen workflow.** Three-way merge + additions-only invariant is well-designed.

---

## Risk Assessment

**Low risk:** Steps 1-2 (rename, flip default) are mechanical.

**Medium risk:** Step 3 (Ty preservation) touches every type site in the transform and both emitters. Regression test by regenerating all examples and verifying both backends.

**Higher risk:** Step 4 (semantic methods) restructures the transform's core method dispatch. Regen + verify after.

**Validation**: After each step, run `regen.sh` and `regen-dafny.sh`. All generated files must be identical (or semantically equivalent for the rename step). Both `lake build` and `dafny verify` must pass on all examples.
