# LemmaScript Tools — Internal Architecture

The `lsc` toolchain translates annotated TypeScript to formal verification artifacts (Lean or Dafny), using [ts-morph](https://ts-morph.com/).

## Pipeline

```
TS source (.ts)
  → extract    (ts-morph → Raw IR)
  → resolve    (Raw IR → Typed IR; types, callback bindings, type narrowing)
  → narrow     (Typed IR → Typed IR; structural narrowing — `someMatch` rewrites)
  → transform  (Typed IR → IR; includes shared callback lowering)
  → peephole   (IR → IR, local rewrites that eliminate Some/None ceremony)
  → emit       (IR → Lean text or Dafny text)
```

## Three IRs

### Raw IR (`rawir.ts`)

Structured AST from ts-morph. Expressions are nodes, not strings. Has declared type references (`tsType: "Packet"`) but no resolved types. Close to TS syntax.

Lambda parameters keep their `rest` marker and `defaultValue` for resolve to bind against the call's argument list.

- `RawExpr`: var, num, str, bool, binop, unop, call, index, field, record, arrayLiteral, lambda, conditional, optChain (`obj?.…`), nullish (`a ?? b`), emptyCollection (`new Map`/`new Set`), nonNull (`e!`); spec-only: result (`\result`), forall, exists, havoc
- `RawStmt`: let, assign, return, break, continue, expr, if, while, switch, forof, throw; spec-only: ghostLet, ghostAssign, assert
- `//@ ` annotations remain as strings (parsed by specparser in the resolve pass)

### Typed IR (`typedir.ts`)

Raw IR annotated with resolved types and classifications. Produced by a resolve pass that runs once. Still TS-shaped, not backend-shaped.

Each expression carries:
- `ty: Ty` — resolved LemmaScript type (nat, int, bool, array, user, etc.)
- Calls carry `callKind` (pure, method, spec-pure, unknown)
- Discriminant fields identified

Each statement carries type information for variables. Unsupported patterns (data-carrying variant equality, return in loop) are rejected here with source locations.

### IR (`ir.ts`)

Backend-neutral intermediate representation. Produced by the transform from Typed IR. Consumed by either emitter. Types are preserved as `Ty` objects (not converted to strings) — each emitter converts to its own type syntax.

Type names: `Expr`, `Stmt`, `Module`, `MatchArm`, `StmtMatchArm`, and `Decl` = `Inductive` | `Structure` | `FnDef` | `FnDefByMethod` | `FnMethod` | `Namespace` | `ClassDecl` | `ConstDecl` | `TypeAlias` | `ExternDecl`. (`FnDefByMethod` is a `//@ pure` function whose body can't be a pure expression — emitted as a Dafny function-by-method.)

## Phases

**Extract** (`extract.ts`): ts-morph → Raw IR. Walks the TS AST, produces structured expression nodes. Only string outputs are `//@ ` annotation text. Two backend-neutral CLI commands stop here. `lsc extract foo.ts` dumps the Raw IR as JSON — external tools can consume it instead of re-parsing TS, e.g. [lemmascript-claimcheck](https://github.com/midspiral/lemmascript-claimcheck) reads each function's `//@ contract`, `requires`, and `ensures` to check the prose against the spec. `lsc info foo.ts` writes `foo.ts.json`, a per-function spec summary (`{ name: { sig, requires, ensures, decreases } }`, class methods keyed `Class.method`) — see `info-command.ts`. `lsc info --typed foo.ts` goes further — through resolve/narrow/autohavoc — and prints the machine-readable Typed IR contract (typed signatures, spec ASTs, flags, body-kind census, emitted-Dafny-name map) to stdout for satellites like [lemmascript-crosscheck](https://github.com/midspiral/lemmascript-crosscheck); see SPEC.md §7.5.

**Resolve** (`resolve.ts`): Raw IR → Typed IR. Resolves storage types, classifies calls, parses annotations, and inserts checked `coerce` reads where an operation needs an optional payload. Assignments convert to the unchanged storage type. Union-variant facts remain in `narrowedPaths`. Resolve also binds inline callbacks to their actual arguments; see [Callback binding and lowering](#callback-binding-and-lowering).

**Narrow** (`narrow.ts`): Typed IR → Typed IR. Rewrites union checks into `tagMatch`, optional chaining and coalescing into expression-only `someMatch`, and optional array-index bindings into bounds-guarded expressions. Ordinary optional guards and loops remain control flow. See [Narrow rules](#narrow-rules).

**Transform** (`transform.ts`): Typed IR → IR. Lowers optional `coerce` reads to Dafny destructors or Lean checked operations, preserving calls within their selected branches. Explicit snapshot matches lower without optional path substitution; union matches retain variant substitution with fresh binders. Supported mutations write updated values back through their optional and record wrappers.

For array callbacks, transform invokes `lowerIndexedCallback` from `callback-lowering.ts` after lowering the receiver and arguments. This shared adapter constructs ordinary IR inside transform; it does not run as a separate module-wide phase.

**Peephole** (`peephole.ts`): IR → IR. Local rewrite rules applied bottom-up to fixed point. Eliminates wrap-then-unwrap ceremony around partial-access expressions like `m.get(k)` (which is internally lowered to `methodCall(map, "get", [k])` and emits as `(if k in m then Some(m[k]) else None)`). See [Peephole rules](#peephole-rules) below.

**Emit** (`lean-emit.ts` / `dafny-emit.ts`): IR → text. Each emitter maps `Ty` objects to backend type syntax and method calls to backend-specific syntax.

## Options

`config.ts` owns the `OPTION_SPECS` registry, nearest-ancestor
`lemmascript.json` discovery, JSON and `//@ option` validation, defaults, and
cross-option checks. `lsc.ts` merges explicit project values with eligible
top-of-file overrides and resolves once per source file, then passes options to
extraction and emission. Those phases do not read config files.

Before copying cross-file contracts, the CLI checks that dependencies share the
root's string model, following imports, re-exports, and selected callees.
`string-semantics` controls literal validation, Dafny character helpers, and the
saved model header. Verification reads that header and the additions-only gate
checks it against the generated companion. `dafny-library` independently selects
collection helpers; the shared compatibility check requires `local` for UTF-16.
See [DESIGN_STRINGS.md](DESIGN_STRINGS.md) for the model boundaries.

`proof-dir` is consumed only by `lsc.ts`, which maps the complete Dafny companion
set before calling the command helpers. `TransformOptions` remains separate
backend-intrinsic pipeline configuration.

## Method Calls

All TS `receiver.method(args)` calls produce `methodCall` IR nodes carrying the receiver, its type, the TS method name, the args, and a `monadic` flag. No renaming — the IR stores the TS name (`"map"`, `"indexOf"`, `"with"`, `"get"`, etc.) and the receiver type disambiguates.

Each emitter dispatches on `(receiverTy, method)` to decide syntax. For example, `(array, "filter")` → Lean: `arr.filter f`, Dafny: `Std.Collections.Seq.Filter(f, arr)` by default (`SeqFilter(f, arr)` with `dafny-library: local`). Unsupported `(type, method)` pairs error at emit time.

`app` is reserved for receiver-less calls: user-defined functions, `Pure.fnName(...)`, `JSFloorDiv(a, b)`, `SetToSeq(s)`.

## Callback Binding and Lowering

| Stage | Responsibility |
|---|---|
| [Extract](tools/src/extract.ts) | Keep each lambda parameter's rest marker and default initializer in Raw IR. |
| [Resolve](tools/src/resolve.ts) | `resolveCallback` binds the lambda to JavaScript's argument list (`callbackArgumentTypes` in [builtins](tools/src/builtins.ts)). Env lookups record which slots are read; unused trailing slots are dropped. Rest is a symbolic pack (`.length`, constant index). Defaults resolve with every parameter in scope; a literal default closure is emitted after the parameters it captures, other initializers keep source order. |
| [Callback lowering](tools/src/callback-lowering.ts), inside transform | `lowerIndexedCallback` rewrites a callback that reads the index or source into an operation over `arrayRange(source.size)`, binding the receiver once. `filter`/`find` map positions back to elements; predicates guard out-of-range indices so backend helpers stay total. Returns `null` when no extra slot is read, leaving unary output unchanged. |
| Emit | `arrayRange` is Dafny's `CallbackIndices(n)` (except under `map`, which becomes a plain `seq(n, i => ...)` comprehension) or Lean's `(Array.range n).map Int.ofNat`. |

```text
xs.map((value, ...rest) => value + rest[0])
  resolve   → xs.map((value, index) => value + index)
  transform → let source = xs;
              arrayRange(source.size).map(i => source[i] + i)
```

## Externs

When a call resolves to a function declared in a *different* `.ts` file, extract records it as a `RawExtern` (resolved to `TExtern`, lowered to `ExternDecl`). The Dafny emitter renders it as a top-of-file `function {:axiom} Name(...): R` by default, or as a body-less `method {:axiom}` when selected by `extern-default: impure` or `//@ impure`; the latter gives every call an independent result. A source `//@ pure` overrides an impure project default. In both cases the source `requires`/`ensures` are lifted along. Externs are emitted before all other declarations so they're in scope everywhere.

## Spec Expression Parser

The specparser (`specparser.ts`) parses `//@ ` annotation expressions into `RawExpr` nodes during resolve. Extraction also calls `renameSpecVariables` in this module to rename free annotation references while preserving strings, field names, record keys, quantified variables, and formatting.

## Adding a New Feature

1. **Extract**: add the TS construct to Raw IR.
2. **Resolve**: add type resolution and classification for the new construct.
3. **Narrow** (only if it introduces a narrowing pattern): add a rule that detects the pattern and rewrites to `someMatch`.
4. **Transform**: add an IR lowering rule that pattern-matches on the typed node.
5. **Emit**: add backend-specific rendering in each emitter if the new IR node needs special syntax.

## Scoping

See [DESIGN_LEXICAL.md](DESIGN_LEXICAL.md) for the rationale, worked examples,
and the division of responsibility between extraction's names and resolve's environments.

Extraction's [LexicalNames](tools/src/lexical-names.ts) assigns names by TypeScript symbol identity before extracting a function or method. It renames conflicting locals when bare blocks are flattened, for-loop counters are hoisted, or branches absorb a continuation. It also renames any local, loop variable, or callback parameter that shadows an enclosing binding of the function (or a declaration of the same file), so no binding shadows another after extraction and later passes can identify a variable by name. A quantified variable in an annotation that reuses a name in scope is freshened in resolve for the same reason. For example, `{ const p = 5; } return p` inside a function with parameter `p` gives the inner binding a distinct name such as `p_2`; the return still reads `p`. The source AST stays unchanged, and sibling bindings whose scopes remain separate keep their names.

When extending extraction:

- Use `sourceName(node)` for local binding names and runtime references, including assignment-target roots and shorthand-property values. Keep field names and record keys unchanged.
- Route scope-sensitive annotations through `LexicalNames.spec` / `specName` with their original AST location and comment position when available. `withScope` and `ghost` track specification-only bindings; `typeNames` carries local type overrides to renamed bindings. Keep annotation renaming in this shared path.
- Keep decisions about lost or extended scopes in `scopeOf` / `loweredScope`. Update those rules when adding a construct whose lowering changes a binding's scope.
- Use `freshName` for compiler-generated names. `LexicalNames` registers source and ghost renames with `reserveName` so later passes avoid them; preserve this reservation when adding a renaming path.

`rejectForwardLocalCaptures` checks arrow bodies before extraction: a closure over a local `let`/`const` declared later cannot be constructed in the current backend model. Callback parameter defaults use their separate initialization rules in resolve.

The resolve pass uses linked environments (Scheme-style). Each binding is a frame with one name, one type, and a pointer to the parent:

```ts
interface Env { name: string; ty: Ty; parent: Env | null }
```

`let` extends the chain. Lookup walks it; extending a scope does not mutate or copy existing frames. `resolveStmt` returns `[TStmt, Env]` so bindings thread through a block. Block-creating constructs (`if`, `while`, `forof`, `switch`) call `resolveBlock`; inner bindings don't leak out. `let x = init` resolves init before adding x to the env. [Callback](#callback-binding-and-lowering) frames add an `onRead` hook, a replacement value, or a symbolic rest pack; shadowing is unchanged.

## Known Limitations

- **Data-carrying variant equality**: `//@ requires m.tag === "b"` where `b` carries data throws an error. Use `switch` to destructure instead.
- **Impure builtin in a narrowing ternary guard**: `opt !== undefined && x?.someHof(...) ? a : b` leaves `opt` un-unwrapped, and the backend rejects the output. Narrow's ternary rule declines on calls transform would hoist out of the arm (where the arm's binder is out of scope), and nothing else unwraps. Affects HOFs and mutators; registry-`pure` builtins are fine (`examples/pureGuard.ts`).
- **For-of desugaring leaks index variable**: `_x_idx` is visible in `//@ invariant` and `//@ done_with` annotations.
- **Spec annotations are strings**: `//@ ` expressions are parsed by the specparser, not extracted from ts-morph. They don't benefit from the structured raw IR.

## Lean Backend

### Pipeline

```
TS source (.ts)
  → extract    (ts-morph → Raw IR)
  → resolve    (Raw IR → Typed IR)
  → narrow     (Typed IR → Typed IR)
  → transform  (Typed IR → IR, with LEAN_OPTIONS)
  → peephole   (IR → IR)
  → emit       (IR → Lean text)
```

### Commands (`lean-commands.ts`)

- `lsc gen --backend=lean foo.ts` — generate `.types.lean` + `.def.lean`
- `lsc check --backend=lean foo.ts` — gen + `lake build`

The Lean workspace uses Velvet 2 from the sibling `../velvet` checkout on the
`lemma2` branch and the version in `lean-toolchain`. See [setup](README.md#setup).

## Dafny Backend

### Pipeline

```
TS source (.ts)
  → extract    (ts-morph → Raw IR)
  → resolve    (Raw IR → Typed IR)
  → narrow     (Typed IR → Typed IR)
  → transform  (Typed IR → IR, with DAFNY_OPTIONS)
  → peephole   (IR → IR)
  → dafny-emit (IR → Dafny text)
```

### Two-File System

Each TS source produces two Dafny files:

- **`foo.dfy.gen`** — always regeneratable from TS. The merge base.
- **`foo.dfy`** — source of truth. Starts as a copy of `.dfy.gen`, then accumulates user/LLM proof additions. The diff between `.dfy.gen` and `.dfy` must be additions-only.
- **`foo.dfy.base`** — transient three-way-merge anchor. A conflict or additions-only failure retains the old anchor; verification failure after a clean additions-only merge advances it to the new gen. Successful `regen` removes it, including with `--no-verify`. Do not discard it simply because a command failed.

With `proof-dir`, `lsc.ts` mirrors the source's config-relative directory under
the configured root and places `.dfy.gen`, `.dfy`, `.dfy.base`, and
`.dfy.merged` together there. The command helpers receive mapped paths and do
not implement routing themselves.

### Commands (`dafny-commands.ts`)

- `lsc gen --backend=dafny foo.ts` — generate `.dfy.gen` + seed `.dfy`
- `lsc gen-check --backend=dafny foo.ts` — gen + additions-only check (no `dafny verify`)
- `lsc regen --backend=dafny foo.ts` — regenerate `.dfy.gen`, three-way merge, verify
- `lsc check --backend=dafny foo.ts` — gen + additions-only check + `dafny verify`

`check` and `regen` pass an optional `RunLog` (`run-log.ts`) to these helpers, and each records the stage it detects: `dafnyCheckDiff` records `diff`, `dafnyVerify` records `ok`/`verify`/`resolve`, and `dafnyRegen` records `conflict` and `--no-verify` runs. Recording lives in the helpers only because they end runs with `process.exit`; if they ever return outcomes instead, it belongs in `lsc.ts`. Dafny keeps inherited stdio; member outcomes come from `--log-format text` written to a temp file.

`lsc runs` (`runs-command.ts`) reads those records back and derives catches. It relies on names the emitter and extractor own: `DAFNY_HELPER_NAMES` (every function, predicate, lemma and method in the Dafny preambles, which are not counted as user code) and `ENSURES_LEMMA_SUFFIX` from `dafny-emit.ts`, and `AnnotKind` from `extract.ts`, whose every keyword it must classify as spec or proof scaffolding (the typecheck fails otherwise).

## Narrow Rules

`narrow.ts` retains the structural rewrites that need explicit decomposition.
Optional payload reads are already `coerce` operations from resolve; optional
`if`, `&&`, `||`, early-return, and loop scopes need no substitution rule.

| Pattern | Typed IR result |
|---------|-----------------|
| `left ?? right` | `someMatch left { Some(v) => v, None => right }` |
| `obj?.<chain>` | `someMatch obj { Some(v) => apply(chain, v), None => undefined }` |
| `arr[i] ?? fallback`, `arr[i]?.<chain>`, optional index binding | bounds-guarded conditional |
| Discriminant `if` chain, negative early return, or unique-field `in` check | `tagMatch` with variant arms and fallthrough |
| `Array.isArray(x)` in `if`, `?:`, or spec implication | `tagMatch` on the synthesized array union |
| `typeof x === "string"` in `?:`, for `string \| T[]` | `tagMatch` selecting the non-array variant |

Conjunctions containing array-union checks split in source order so an earlier
optional guard stays before a later payload read. Implication fallthroughs are
vacuously true. Union binders are allocated once per arm; path substitutions
happen in Typed IR before payload reads acquire backend temporaries.

`someMatch` is expression-only. Its bodies refer directly to its fresh snapshot
binder, including for complex receivers. It never rebinds a source variable or
replaces subsequent reads of mutable storage. See
[ARCHITECTURE_NARROWING.md](ARCHITECTURE_NARROWING.md).

## Peephole Rules

Local IR-to-IR rewrites applied bottom-up to fixed point at each node, in `peephole.ts`. They eliminate Some/None ceremony that comes from `Map.get(k)` and `Record<K,V>` index access (both lowered to `methodCall(map, "get", [k])`, which `dafny-emit` renders as `(if k in m then Some(m[k]) else None)`).

Each rule is local and semantics-preserving. The pass takes a `backend` parameter — some rules are Dafny-only (see below).

### Map.get rules (both backends)

**Expression rules**

| Pattern | Rewrites to |
|---------|-------------|
| `match m.get(k) { Some(v) => sb, None => nb }` | `if k in m then (let v = m[k] in sb) else nb` |
| `let x = m.get(k) in match x { Some(v) => sb, None => nb }` (when `x` not used in arms) | `if k in m then (let v = m[k] in sb) else nb` |

**Statement rules**

| Pattern | Rewrites to |
|---------|-------------|
| `match m.get(k) { Some(v) => sb, None => nb }` (statement-level) | `if k in m { var v := m[k]; sb } else { nb }` |
| `let x = m.get(k); match x { Some(v) => sb, None => nb }` (when `x` not used in arms or after) | `if k in m { var v := m[k]; sb } else { nb }` |

The let-collapse rules require the bound variable to not be referenced in either match arm or, for the statement form, after the match (conservative reference check, no shadowing analysis). Otherwise the binding and match are preserved.

The bound value `m[k]` is captured once via `let` (expression form) or `var` (statement form). Substitution would re-evaluate `m[k]` at every use, which changes semantics if the body mutates `m`.

### Boolean simplification rules (Dafny only)

| Pattern | Rewrites to |
|---------|-------------|
| `if c then false else true` | `¬c` |
| `if c then true else false` | `c` |
| `if c then b else false` | `c && b` |
| `if c then true else b` | `c \|\| b` |

These apply only for the Dafny backend. They emit `∧`/`∨` in the IR, which:
- Dafny renders as `&&`/`||` — short-circuit Bool, sound for termination analysis when the right operand contains a recursive call.
- Lean renders as `∧`/`∨` — Prop conjunction/disjunction, which evaluate both arguments. For recursive functions like `if n = 0 then true else f(n - 1) ∧ ...`, the recursive call appears unconditionally in the term and Lean's structural-termination check fails.

For Lean we keep the original `if-then-else` form, which preserves the conditional structure and lets Lean see that the recursive branch is reachable only when the guard holds.

### Emitter precedence

The Dafny emitter wraps `if-then-else` and `let` (var-binding) expressions in parentheses (alongside `match`). Without the parens, an outer `arr[idx]` post-fix would parse into the else branch — e.g., `if c then a else []` followed by `[i]` becomes `... else [][i]` which type-checks against the `[]` rather than the whole if. Always wrapping is verbose but safe.

## Current State

| File | Phase | Role |
|------|-------|------|
| `rawir.ts` | Types | Raw IR type definitions |
| `extract.ts` | Extract | ts-morph → Raw IR |
| `lexical-names.ts` | Extract | Source and ghost binding names, annotation renaming, forward-capture checks |
| `specparser.ts` | (parser) | Parses `//@ ` annotations → RawExpr |
| `resolve.ts` | Resolve | Raw IR → Typed IR (storage types and checked reads) |
| `typedir.ts` | Types | Typed IR type definitions (incl. `coerce`, `someMatch`, `tagMatch`) |
| `narrow.ts` | Narrow | Typed IR → Typed IR (snapshots, bounds, union matches) |
| `condition-facts.ts` | (shared) | Union condition facts and optional-expression helpers |
| `ir.ts` | Types | Backend-neutral IR type definitions |
| `transform.ts` | Transform | Typed IR → IR |
| `peephole.ts` | Peephole | IR → IR (Some/None ceremony elimination) |
| `types.ts` | (shared) | TypeDeclInfo, parseTsType |
| `typedecls.ts` | (shared) | Declaration lookup (exact / dotted / generic-base-sliced) |
| `builtins.ts` | (shared) | Builtin classification table — one `BuiltinId` per operation, stamped by resolve |
| `names.ts` | (shared) | Fresh-name minting — collision-safe internal identifiers |
| `lean-emit.ts` | Emit | IR → Lean text |
| `dafny-emit.ts` | Emit | IR → Dafny text |
| `lean-commands.ts` | CLI | Lean gen/check commands |
| `dafny-commands.ts` | CLI | Dafny gen/gen-check/regen/check commands |
| `info-command.ts` | CLI | `lsc info` — per-function spec summary JSON; `--typed` — Typed IR contract for satellites |
| `config.ts` | CLI/shared | Option registry, config discovery/validation, file overrides, artifact path mapping |
| `run-log.ts` | CLI | Run log: `.lemmascript/` directory, source snapshots, one record per Dafny `check`/`regen`; reads records back |
| `runs-command.ts` | CLI | `lsc runs` — catches, open and dropped failures from the run log, with diff evidence and change hints |
| `lsc.ts` | CLI | Wires the pipeline, dispatches to backend |
