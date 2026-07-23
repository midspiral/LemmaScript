# LS-in-LS: Compiler Architecture and Self-Application

**Status:** Adopted — in progress; per-step status is annotated in §9
**Scope:** `lsc` compiler architecture, refactoring, verification, self-application

This document is standalone: it records the settled design, its consequences,
and the migration order.

## 1. Summary

The `lsc` pipeline is:

```text
extract → resolve → narrow → transform → dafny-emit / lean-emit
```

Two costs have accumulated. First, several compiler concerns are
re-implemented independently across passes: what a builtin method means, what
a condition establishes, how a generic type is taken apart, where fresh names
come from. Second, important phase invariants (no optional-chains after
narrow, no name capture, exhaustive matches) exist only as assumptions made
by later passes or enforced by crashes.

This design commits to six decisions:

1. **Builtin registry.** Each builtin operation has one stable `BuiltinId`
   and one registry entry holding its type rule and classification data.
   `resolve` assigns the identity once; `narrow` and `transform` stop
   re-recognizing `(receiver type, method name)`. The emitters are
   untouched: they dispatch on the backend IR, where `(objTy, method)` is
   the correct key (§3.2).
2. **Shared condition analyzer.** One module answers "what does this
   condition establish" as an ordered fact list plus residual. Both `resolve`
   (for typing branches) and `narrow` (for rewriting) consult it. Narrowing
   collapses to ~6 positional drivers over shared materializers.
3. **Structured types and `TypeDecls`.** Generic arguments become structured
   (`{ kind: "user"; name; args: Ty[] }`); declaration lookup goes through
   one helper API instead of repeated scans.
4. **Explicit state.** Module-level mutable state is replaced by threaded
   contexts. All generated binders come from one `NameSupply` with a
   provable freshness contract; backend identifiers come from an allocating
   environment with an injectivity guarantee.
5. **Structured rejection.** User-facing failure is a `Result` value with a
   structured error, not a `throw`. Rejection is a normal compiler outcome.
6. **Self-application with an honest trust story.** The portable compiler
   core stays inside the LemmaScript subset and is continuously self-run in
   CI, with structural contracts proven on both backends. Property strength
   and trust reduction are tracked as separate axes (§8), and claims are
   limited to what the axes support.

Every step pays for itself as an ordinary compiler improvement even if
self-application stalls. Migration is incremental and each step is testable
byte-for-byte against the `examples/` gauntlet.

## 2. Current problems

- **Builtins are smeared.** A single method (`includes`) appears in up to
  seven sites: return-type inference, narrowing allowlists, HOF
  classification, lambda-param inference, int-coercion special cases, purity
  sets, and one emit rule per backend. Every site keys on the same
  `(receiver kind, method name)` pair — the signature of a missing table.
  The cost is inconsistent support: a method works in one pass and not
  another because one list was never updated.
- **Narrowing is a hand-written matrix.** `narrow.ts` has ~20 rules that are
  a Cartesian product of *what the condition establishes* (optional
  presence, `Array.isArray`, `typeof`, discriminants, key membership,
  bounds) and *where it sits* (`if`, ternary, early return, implication,
  guard statement, `&&`-residual, `||`-chain). Each cell re-implements
  negation-swapping, binder minting, and residual threading. Coverage gaps
  exist exactly where a cell was never written.
- **`resolve` duplicates condition semantics.** It has parallel machinery
  (`detectOptionalCheck`, `collectAndChainNarrowings`, …) re-encoding the
  same TS semantics for type-environment purposes. New narrowing forms must
  be taught twice and can diverge.
- **Types are stringly.** `Foo<Bar>` is stored as a string, forcing
  `name.slice(0, name.indexOf("<"))` surgery ~10× across passes;
  `tyEqual` compares `JSON.stringify` output.
- **State hides in modules.** `_ocCounter`, `_typeDecls`, `_useSafeSlice`,
  `_needsJSString`, emitter preamble flags. Passes are non-reentrant and
  hard to unit-test, and no contract can be stated about state evolution.
- **Rejection is exceptional control flow.** The compiler `throw`s
  user-facing errors; LemmaScript models `throw` as unreachable, which
  misstates a compiler whose rejections are normal outcomes and blocks
  sound self-application at the API boundary.
- **Invariants are implicit.** "No optChain reaches transform", "generated
  names don't capture", "matches are exhaustive", "spec parsing consumes
  the whole input" are today enforced by downstream crashes or reviewer
  discipline.

## 3. Decision: the builtin registry

*Status: implemented (2026-07-21) — see §9 step 2. The §10.2 builtin
matrix is still outstanding.*

### 3.1 Shape

One stable identity per supported operation, and one classification entry
per identity. The registry holds recognition and classification only — no
lowerings:

```ts
interface BuiltinSpec {
  ret(objTy: Ty, args: TExpr[]): Ty;  // return-type rule
  pure: boolean;                      // under-approximate
  hof?: { lambdaParamTys(objTy: Ty, args: TExpr[]): Ty[] };
  intArgPositions?: number[];         // nat/int coercion sites
}

const BUILTINS = { /* one entry each, keyed `<RecvKind>.<method>` */ }
  satisfies Record<`${RecvKind}.${string}`, BuiltinSpec>;

type BuiltinId = keyof typeof BUILTINS;
```

The key *is* the identity, so recognition needs no separate index and the
receiver/method pair has no second spelling to drift from. `resolve`
performs recognition once and annotates the typed method-call node with its
`BuiltinId` (an optional field on the existing node — no new IR node kind).
Downstream:

- `narrow` drops its builtin-name allowlists and checks `spec.pure`;
- `transform` drops `HOF_METHODS` and the coercion special cases, reading
  `spec.hof` / `spec.intArgPositions`;
- the emitters are out of scope, deliberately and permanently — not as
  deferred work. See §3.2: identity dispatch is wrong on their side of
  the transform boundary.

Deriving `BuiltinId` from the table makes exhaustiveness structural rather
than checked: an id without a classification entry is unwritable, since the
ids *are* the entries.

### 3.2 Consequences accepted

- **A dedup, not a relocation.** What §3 deletes is the scattered
  re-derivations of the same classification facts across resolve, narrow,
  and transform. The lowering rules are not part of that duplication —
  one emit rule per backend is legitimate per-backend knowledge — and
  they stay in their emitters untouched. Backend-neutral IR rewrites for
  every builtin remain rejected: `sort`/`split`/`delete` genuinely differ
  per backend.
- **Emitter dispatch stays `(objTy, method)`, by design.** The `BuiltinId`
  stamp lives on the typed IR and does not cross the transform boundary.
  Transform legitimately *synthesizes* `methodCall` nodes during
  desugaring (`slice`, `set`, `has`, and internal ops like `getDirect`)
  that have no source-level identity; dispatching the emitters on
  `BuiltinId` would force transform to mint identities — defeating
  resolve-once — and would pollute the registry with internal ops that
  are not surface builtins. On the backend IR, `(objTy, method)` carried
  on the node is the honest dispatch key.
- **No cross-layer module.** The registry imports only mid-pipeline types
  (`Ty`, `TExpr`), never emitter types. Classification is data plus total
  functions over `BuiltinId`, which keeps the registry portable to the
  subset in principle.
- **Cross-backend agreement lives in the test matrix.** That both
  backends' lowerings for a builtin model the same JS semantics is not
  machine-checkable in any layout; the per-builtin matrix (§10.2), which
  exercises both backends, is where that agreement is validated.
- **Support asymmetry stays as it is.** Some builtins are Dafny-only today
  (`sort`, `split`, `trim`, `toLowerCase`, …). The registry classifies
  them like any other; an unsupported use keeps today's emit-time error,
  unchanged. Recording per-backend support in the registry — enabling
  earlier structured rejection or degradation — is deliberately deferred;
  it can be added later without reshaping anything.
- **`pure` stays one bit for now.** Purity, totality, and
  expression-lowerability are conceptually distinct, but every current
  consumer asks the same question. The bit splits into named capabilities
  only when a concrete builtin needs the distinction — no speculative
  effect system. The lambda-taking HOFs are the known imprecision:
  `array.map` is pure, but a monadic lambda body makes transform lift the
  call, so those entries are marked impure. Under-approximating costs only a
  missed narrowing.

### 3.3 Migration

One PR, not a staged sequence. Family-by-family staging was considered and
rejected: the existing lists are not partitioned by family (narrow's
purity set and resolve's return-type special cases mix array/map/set
receivers), so a partial migration would split each list into migrated and
unmigrated halves with precedence rules between the registry path and the
legacy path — transitional dual-path scaffolding that is itself the
several-sources-of-truth disease §3 cures. The byte-for-byte gate is
equally strong at any diff size, and at ~40 entries the whole change is
one sitting. (This does not generalize to §4: narrow's rule families
genuinely are partitioned by condition form, so its staged port stands.
Stage when the old code is partitioned along the migration's seams;
one-shot when staging would cut seams the code doesn't have.)

Sequence inside the PR, one commit per step with the gauntlet run after
each: validate the `BuiltinSpec` shape on a few representative builtins
(one HOF, one coercion case, one plain method); fill the table; then flip
each consumer wholesale — resolve's return-type chains, narrow's purity
list, transform's HOF/coercion sets — deleting each list in the commit
that flips its consumer. Verified byte-for-byte against the `examples/`
gauntlet with the case-study CI matrix as backstop. Nothing else rides
along: no emitter changes, no `Result` migration, no error-path changes,
no type restructuring. Done when neither `narrow` nor `transform`
identifies a builtin by receiver/name spelling and no duplicated
classification list remains.

## 4. Decision: shared condition analysis

*Status: implemented (2026-07-21) — see §9 step 6 for the as-built shape
and what deliberately differs from §4.1's sketch.*

### 4.1 Shape

One module (`condition-facts.ts`) owns condition semantics:

```ts
type Fact =
  | { kind: "present"; path: TExpr; binder: string; innerTy: Ty;
      falsyGuard: TExpr | null }
  | { kind: "variant"; path: TExpr; typeName: string; variant: string }
  | { kind: "primitiveType"; path: TExpr; primitive: PrimitiveTy }
  | { kind: "isArray"; path: TExpr; elemTy: Ty | null }
  | { kind: "keyIn"; map: TExpr; key: TExpr }
  | { kind: "inBounds"; arr: TExpr; idx: TExpr };

// Owns &&-splitting, ===/!==/!-negation, ||-De-Morgan:
function analyze(cond: TExpr, decls: TypeDecls):
  { facts: Fact[]; negFacts: Fact[]; residual: TExpr | null };
```

**The fact lists are ordered, and order carries dependency.** For
`x !== undefined && x.field !== undefined`, `analyze` returns
`[Present(x), Present(x.field)]`; the materializers fold over the list in
order, so the second check is reified inside the match introduced by the
first. No tree is needed for conjunctions.

Two materializers know how each fact reifies (someMatch / tagMatch /
bounds-conditional), in statement and expression form:

```ts
function wrapStmts(facts: Fact[], residual: TExpr | null,
  some: TStmt[], none: TStmt[], ctx: NarrowCtx): TStmt;
function wrapExpr(facts: Fact[], residual: TExpr | null,
  some: TExpr, none: TExpr, ty: Ty, ctx: NarrowCtx): TExpr;
```

`narrow`'s rule families collapse to ~6 positional drivers (if-statement,
early-return + rest consumption, ternary, implication, guard statement,
conditional initializer), each ~ten lines: analyze, fold wrap over the
facts, reinsert the residual as an inner conditional. A new fact kind gets
every position for free; a new position gets every fact kind for free — the
current coverage gaps (`typeof` only in ternaries, `'key' in x` only in
discriminant chains) close as a side effect.

`resolve` consults the same `analyze` for branch typing and drops its
parallel machinery. The passes stay separate — resolve genuinely needs
narrowing *during* typing — but the semantics live in one module, so a new
narrowing form is taught once.

### 4.2 Consequences accepted

- **Disjunctions are handled conservatively.** `||` narrows where De Morgan
  reduces both sides to facts (the existing `||`-chain early-return
  pattern); mixed disjunctions like `x === undefined || x.field === 0`
  fall into the residual and get no refinement. This matches current
  behavior and is sound.
- **Nothing is stored in the IR.** Facts are computed where needed and
  discarded; no condition wrapper node, no plan threading between passes.
  Analysis is cheap and determinism makes recomputation safe.
- **Key-membership facts need a variable key.** `exprEqual` — the structural
  equality that recognizes `m[k]` on both sides of `k in m ? m[k] : default`
  — compares vars, field chains, and indices, not literals, so a literal key
  (`"a" in m ? m["a"] : d`) doesn't narrow while a variable one does. Adding
  the literal cases is three lines; it is left undone because it is a
  behavior change owing an example (§9 step 6), not a migration artifact.
- **Named escalation path.** If a real program requires narrowing under a
  mixed disjunction, or ordered facts prove unsound for some composition,
  `analyze`'s *output* upgrades to a small and/or tree while `Fact`, the
  positional drivers, and the materializers survive unchanged. The trigger
  is a concrete failing example checked into the test suite, not
  anticipation. Until then the flat shape stays — it is simpler to port to
  the subset and simpler to prove things about.

### 4.3 Migration

Introduce `Fact`/`analyze`/`wrap`; port the optional-presence family first,
then isArray/discriminant/typeof/membership/bounds, keeping old rules as a
fallback chain until each family is ported, then delete them. This also
deletes both copies of the "restore `isDiscriminant` after `applyChain`"
fixup, because the fact carries that knowledge once. Every supported fact
kind gets a test in every supported position and polarity (§10.2).

## 5. Decision: structured types, `TypeDecls`, `Result`

### 5.1 Structured generic arguments

*Status: deferred (2026-07-21) — see §9 step 3. The ecosystem doctrine is
generic erasure to the constraint bound; structured args would add
parametricity the subset deliberately omits, and the slice-site hygiene
this section targeted is handled by `typedecls.ts`'s `tyBaseName`.*

```ts
{ kind: "user"; name: string; args: Ty[] }
```

`tyEqual` becomes structural (not `JSON.stringify`), base-name slicing
disappears, alias expansion receives explicit arguments, and contracts can
recurse over actual type structure. `parseTsType` stays on the extraction
side (it depends on ts-morph); `resolve` receives only portable `Ty`.

### 5.2 `TypeDecls`

*Status: implemented (2026-07-21) — see §9 step 3.*

One lookup abstraction over `typeDecls`, implemented as a datatype plus
plain helper functions (portable to the subset — no function-valued record
fields required). As built in `typedecls.ts`:

```ts
function tyBaseName(name: string): string;                    // Foo<Bar> → Foo
function declOf(decls: TypeDecls, name: string): TypeDeclInfo | undefined;
function declOfKind(decls: TypeDecls, name: string, ...kinds): TypeDeclInfo | undefined;
function declOfDotted(decls: TypeDecls, name: string): TypeDeclInfo | undefined;
function declOfTy(decls: TypeDecls, ty: Ty): TypeDeclInfo | undefined;
function unionDeclOfTy(decls: TypeDecls, ty: Ty): TypeDeclInfo | undefined;
function discriminantOf(decls: TypeDecls, ty: Ty): string | undefined;
function declWithVariant(decls: TypeDecls, ctorOrValue: string): TypeDeclInfo | undefined;
```

Replaces the `_typeDecls.find(...)` scans re-spelled at every use site. The
API makes the three name semantics explicit — exact, dotted, generic-base
sliced — because call sites deliberately differ, and silently "upgrading"
an exact site to a dotted or sliced one changes which declaration it finds.

### 5.3 Structured results and errors

```ts
type Result<T, E> = { tag: "ok"; value: T } | { tag: "err"; error: E };

type CompileError =
  | { kind: "unsupportedSyntax"; span: Span; syntax: string }
  | { kind: "typeError"; span: Span; expected: Ty; actual: Ty }
  | { kind: "unknownName"; span: Span; name: string }
  | { kind: "unsupportedBuiltin"; span: Span; receiver: Ty; method: string }
  | { kind: "invalidNarrowing"; span: Span; reason: string }
  | { kind: "internalInvariant"; span: Span | null; invariant: string };
```

All user-facing `throw` paths in portable modules migrate to `Result`. User
input must never reach `internalInvariant` — that case is a compiler bug.
Error rendering is a driver concern. The rewrite touches every error path,
so it rides along with the pass-by-pass migrations rather than landing as a
big bang.

## 6. Decision: explicit state and names

### 6.1 Contexts

Each pass receives what it uses and returns what it changes; no portable
module keeps mutable module-level state (`_ocCounter`, `_typeDecls`,
`_needsJSString`, `_useSafeSlice`, `_unionCtors`, the Dafny out-param name
all retire). This falls out mostly for free while doing §3–§4, since both
introduce a ctx anyway — and self-application makes it mandatory, because
threaded state is precisely what makes freshness provable.

### 6.2 Fresh names, with the contract that matters

```ts
type NameSupply = { used: StringSet; next: number };

function freshName(supply: NameSupply, scopeNames: StringSet, hint: string):
  { name: string; supply: NameSupply };
```

All binder-minting compiler code calls this function; no pass concatenates
its own suffixes. The useful theorem is **not** merely "the result is
absent from some set" — it is conditional on the caller's obligation:

> `scopeNames` contains every free and bound source-level name in the
> region the generated binder will wrap. Then `freshName` returns a name
> absent from `scopeNames` and from the supply's reserved names, and the
> returned supply reserves it permanently.

Every transformation that inserts a binder must establish that it passed
the complete relevant scope. This is the theorem form of the name-capture
bug class (PR #153): it replaces local-check discipline with a contract.

### 6.3 Backend name allocation

Per-name escaping is insufficient: two distinct source names can escape to
the same legal backend identifier. Each backend therefore allocates through
an environment:

```ts
type BackendNameEnv = { assigned: NameMap; reserved: StringSet };

function allocateBackendName(env: BackendNameEnv, sourceName: string):
  { emitted: string; env: BackendNameEnv };
```

Postconditions: every emitted identifier is legal and non-keyword; distinct
source binders receive distinct emitted identifiers; repeated requests for
the same binder are stable. Stable internal symbol IDs are *not* required
for this and are deferred until the allocator exposes remaining complexity.

## 7. Watch item: `transform.ts` staging

`transform.ts` (2.4k lines) is where TS-isms, backend workarounds, and
desugarings pile up. The IR split (TS-shaped `Expr` vs backend-shaped
`TExpr`) is principled and stays. Splitting transform into named stages
(control lowering, effect/ANF lifting, backend-independent normalization,
per-backend normalize modules) is **explicitly not scheduled**. It becomes
an action item when one of these triggers fires:

- a change needs an invariant like "no statement-lowering builtin remains
  in expression position" as a checkable boundary rather than a comment;
- Lean-only and Dafny-only rules start interleaving badly in the common
  pass;
- the self-application port reaches transform (§9 phase order), where
  porting stage-by-stage is the natural unit anyway.

A stage is justified only by a meaningful postcondition later stages can
assume and test — never by file size alone. Until a trigger fires, new
rewrites go on the existing `mapExpr`/`mapStmt` walkers.

## 8. Self-application and the trust story

### 8.1 Two independent axes

"Self-hosting" conflates two questions. They are tracked separately.

**Property strength:**

- **P0 — subset compatibility.** The module is valid LemmaScript; both
  generated backends typecheck. No specs yet.
- **P1 — structural verification.** The module carries and proves phase
  invariants (freshness, desugaring completeness, exhaustiveness, …).
- **P2 — semantic preservation.** A formal IR semantics exists and the pass
  provably preserves it. Research-scale; explicitly out of scope for now.

**Trust reduction:**

- **T0 — self-application.** The TypeScript `lsc` translates its own source
  and the generated artifact verifies. The translator stays trusted.
- **T1 — the generated verified implementation is executed** for the ported
  pass, so the proved properties apply to the code actually run.
- **T2 — the translation itself is validated or verified.**

A module can be P1/T0: valuable, but not a self-verifying compiler.

**Near-term target: P1/T0** for `names`, IR walkers, `typedir`, `peephole`,
`narrow`, and selected transform/emitter cores. **Medium-term: P1/T1** for
the most valuable passes. P2 and T2 are later research directions.

### 8.2 Trusted computing base at P1/T0

| Component | Role | Status |
|---|---|---|
| TypeScript parser, ts-morph | Parse source, expose types | Trusted dependency |
| `extract.ts` | TS syntax/types → `RawModule` | Trusted frontend |
| `lsc` translator | LS source → Dafny/Lean | Trusted at T0 |
| Dafny verifier / Lean kernel | Check obligations | Trusted kernel boundary |
| CLI, fs, process | Drive compilation | Unverified shell |

At T1, generated verified passes replace their TS counterparts in the
executed core; `extract.ts`, the driver, and kernel assumptions remain.

**Permitted claims.** At P1/T0: "selected compiler modules are written in
the LemmaScript subset and their generated Dafny and Lean representations
verify structural contracts." Not: "the compiler proves its own
correctness." At P1/T1: "the compiler executes a generated verified
implementation of selected passes, with the stated guarantees." Full
compiler correctness requires P2. Documentation must classify each module's
P- and T-level accurately.

### 8.3 Module portability

| Module | LOC | Target | Notes |
|---|---|---|---|
| `ir.ts` | 308 | Prime P0/P1 | Pure datatypes + query walkers; structural recursion sweet spot. |
| `rawir.ts` | 227 | Prime P0/P1 | Pure datatypes; the extract/specparser output surface. |
| `typedir.ts` | 203 | Prime P0/P1 | Structural `tyEqual` (an improvement anyway). |
| `typedecls.ts` | 71 | Prime P0/P1 | Total lookups over a declaration list; no state. |
| `names.ts` | 56 | Prime P1 | Tiny, real spec content (freshness, keywords). |
| `builtins.ts` | 175 | P1 after reshaping | Data table + total functions, but `ret` is a function-valued record field — the subset wants a `switch` on `BuiltinId` instead (§5.2). |
| `condition-facts.ts` | 408 | Prime P1 | Pure detection + materializers; state confined to `CondCtx`. Ports with `narrow`. |
| `peephole.ts` | 444 | Early pass target | Self-contained IR→IR rewrites. |
| `autohavoc.ts` | 372 | Early pass target | Typed IR → Typed IR; depends only on `typedir`. |
| `narrow.ts` | 738 | P1 after §4 | Was 1114; §4 moved condition semantics to `condition-facts.ts`. |
| `transform.ts` | 2388 | P1 by stages | Needs ctx work; port stage-by-stage (§7 trigger). |
| `resolve.ts` | 1702 | Mostly | Push `parseTsType` to extraction; core is pure Raw→Typed. |
| `specparser.ts` | 330 | P1 | Recursive-descent parser; classic verification fodder. |
| `types.ts` | 212 | Split | `TypeDeclInfo` is portable data; `parseTsType` imports ts-morph and stays with extraction (§5.1). |
| `dafny-emit.ts`/`lean-emit.ts` | 2292 | Partial | Untouched by §3; precedence logic is spec-worthy; regexes become string helpers. |
| `extract.ts` | 2479 | Trusted frontend | Wraps ts-morph; stays unverified; `RawModule` is the trusted input. |
| `lsc.ts`, commands | ~500 | Unverified driver | CLI, fs, process. |

Net: roughly 6.8k of 12.9k lines are pure IR-to-IR passes, all portable in
principle. Once a module is in-subset, it joins CI as an `lsc` self-run
target so it cannot drift back out — the compiler becomes a standing
regression gauntlet that grows with itself.

### 8.4 P1 property catalog (value-per-effort order)

1. **Freshness** (§6.2) — kills the name-capture bug class permanently.
2. **Desugaring completeness** — after `narrow`, no `optChain`/`nullish`
   nodes remain (an `anyExpr`-style predicate, provable by the structural
   induction the prover does for us). Today enforced by "transform would
   crash."
3. **Narrowing completeness** — if `resolve` narrowed a path for a branch,
   `narrow` introduced the binder that unwraps it. The one property here
   with a known violation: a rule may decline to fire and leave the branch
   referencing the optional, which transform lowers into ill-typed backend
   code (TOOLS.md, known limitations). Nothing catches it but the backend's
   type checker, and only if that shape is exercised.
4. **Backend name legality and injectivity** (§6.3).
5. **Arm purity** — after transform (Dafny mode), no impure call remains in
   a match-expression arm; a guard inside one rule becomes a postcondition
   of the pass.
6. **Match exhaustiveness** — every emitted `tagMatch` covers all variants
   or has a fallthrough, checked against its `TypeDeclInfo`.
7. **Parser sanity** — `specparser` consumes the whole input or errors.
8. **Typing boundary** — successful `resolve` leaves no `unknown` where
   later passes require a concrete type.

Notably absent: "the generated code means the same as the TS" — that is
P2. P1 proves the compiler doesn't produce malformed output and doesn't
capture names, which is where its actual bug history lives.

### 8.5 Required subset features

Each is a generally useful feature independent of self-application:

1. **Recursive and mutually recursive datatypes.** `Expr`/`Stmt` contain
   each other. *Spiked (2026-07-21); the prerequisite is priced and open.*
   Findings: extraction and both backends' generation already handle
   self-recursive, mutually recursive, and array-nested unions; Dafny
   verifies mutual functions natively, and Lean elaborates nested
   `Array`-field inductives with `deriving`. The remaining work is
   Lean-only emission: (a) wrap mutually recursive inductives/defs in
   `mutual … end` blocks (SCC analysis over type references and the def
   call graph, topologically ordered); (b) a termination strategy for
   array folds (`slice(1)`-style recursion is not structural — bridge
   through `toList` or emit `termination_by`). Dafny needs no change:
   `_ensures` lemmas over mutual functions stay empty by design — proof
   authorship belongs to the user/AI via the lemma-file pattern, and the
   regen merge preserves it. The proof shape is mechanical on both
   backends (structural induction with mutual lemma calls; on Lean,
   `match` + IHs + `simp`/`omega` in a `.proof.lean`).
2. **Structural recursion as default termination.** AST walkers must not
   need hand-written `//@ decreases` for structural recursion.
3. **Result ergonomics.** Matching `ok`/`err`, propagating and mapping
   without boilerplate; a small verified helper library over ad hoc
   patterns.
4. **Big-match ergonomics.** ~25-variant exhaustive switches, nested,
   with early returns in arms — at a scale no example has stressed.
5. **Library audit gaps.** No regexes (the emitters' escaping code becomes
   spec-carrying LS, pleasingly), no `JSON.stringify` equality, and check
   `flatMap`/`Object.entries` coverage against actual pass usage.

## 9. Roadmap

Ordered so the mechanical, immediately-paying work leads. The baseline for
every migration step is the existing `examples/` gauntlet compared
byte-for-byte (plus normalized-AST comparison where formatting is
incidental); regression tests for the known name-capture and narrowing
failures are added with the first PR that touches each area. No separate
process phase precedes the first win.

*Progress is annotated in place — `done` / `deferred`, with dates; a step
with no annotation is not started.*

1. **Mutual-recursion spike** — *done (2026-07-21); findings in §8.5.*
   The prerequisite reduces to two Lean-emitter items (`mutual` block
   grouping; array-fold termination); Dafny and extraction need nothing.
   *The emitter items are deferred (low priority) until step 8 approaches.*
   Blocks §9 steps 8+ only, not the architecture work.
2. **Builtin registry** (§3), one PR; consumers flip commit by commit,
   each list deleted in the commit that flips its consumer. — *done
   (2026-07-21): `builtins.ts` classification table; resolve stamps
   `BuiltinId` (call nodes and optChain steps); narrow/transform read the
   stamp; emitters untouched; gauntlet byte-for-byte on both backends;
   pinned by `examples/postTags.ts`. The §10.2 builtin matrix is still
   outstanding.*
3. **Structured user types, structural `tyEqual`, `TypeDecls`** (§5.1–5.2),
   small PRs. — *`TypeDecls` half done (2026-07-21): `typedecls.ts`
   centralizes declaration lookup (exact / dotted / generic-base-sliced
   semantics documented in its header); ~35 scan sites and all inline
   base-name slices in resolve/narrow/transform replaced; gauntlet
   byte-for-byte on both backends. §5.1 probed and deferred (2026-07-21):
   generic datatype *instantiation* emits raw TS spellings today
   (`Res<number>`, invalid on both backends), but the ecosystem's
   documented doctrine is **erasure**, not parametricity — generics erase
   to their constraint bound (xyflow-lemmascript README: `<EdgeType
   extends EdgeBase>` → `EdgeBase`), so verified signatures never carry
   instantiated generics and no case study hits the broken path.
   Structured `args: Ty[]` would add parametric capability the subset
   deliberately omits; the stripping-hygiene motivation is already
   satisfied by `tyBaseName` being the single slice site. Deferred with
   it: making today's partial erasure uniform (record decls erase, Dafny
   union decls stay parametric, Lean union decls leak a free `T` — the
   free `T` is a known bug) — pick up if a case study ever hits it.*
4. **`Result`/`CompileError`** (§5.3) on leaf modules first, then riding
   along with each pass migration.
5. **Ctx threading and `NameSupply`** (§6.1–6.2) — mostly falls out of 2–4.
   — *partial (2026-07-21): narrow is fully ctx-threaded (`CondCtx`, no
   module state). Still module-level: transform's `_typeDecls`/flags, both
   emitters' state, `names.ts`'s `_userNames`. `NameSupply` (§6.2) not
   started.*
6. **Condition analyzer and fact migration** (§4), family by family; delete
   old rule families; wire `resolve` to the shared analyzer. — *done
   (2026-07-21), byte-for-byte on both backends. As built:
   `condition-facts.ts` owns detection (presence, `&&`-leading-fact,
   `||`/De-Morgan None-detectors, discriminant/isArray/typeof variants,
   in-bounds, map membership), binder minting, and the someMatch
   materializers with the falsy gate; `narrow.ts` (1114 → 738 lines) is
   walkers plus positional drivers; `resolve` consults the shared
   `presentFact` on resolved conditions (`detectOptionalCheck` /
   `classifyOptExpr` deleted); the two "restore isDiscriminant" fixups are
   one `restoreDiscriminantFlag`. Deliberate divergences from §4.1's
   sketch: analysis yields one leading fact + residual, with nesting from
   drivers re-walking the residual (the ordered-fact list realized
   iteratively — recursion order carries the dependency); and the §4.1
   promise that "coverage gaps close as a side effect" was traded away for
   byte-for-byte output — the migration adds no new fact×position cells.
   New cells are now single-driver additions, but each is a behavior
   change wanting its own example, made deliberately, not en passant.
   Ride-along (§6.1): narrow's `_ocCounter`/`_typeDecls` module state is
   gone, replaced by an explicit `CondCtx` threaded through the walk.*
7. **Backend name allocator** (§6.3) with collision tests.
8. **Self-apply the leaves:** `names.ts`, portable type helpers/`typedir`,
   IR walkers; P1 contracts (freshness, keywords); CI self-run targets.
9. **`peephole`, then `narrow`** in-subset with completeness + freshness
   contracts.
10. **Portable `resolve` core, `specparser`, emitter cores** — transform
    ports stage-by-stage here, which is when §7's split naturally happens.
11. **First T1 experiment:** execute one generated verified pass.

Each PR states: the behavior retained, the invariant or single source of
truth introduced, the fallback still present, and the test that later
permits removing the old path.

## 10. Test strategy

### 10.1 Golden and differential

Byte-for-byte gauntlet comparison for mechanical migrations; normalized-AST
comparison where formatting is incidental; temporary old/new differential
execution during staged migrations (§4.3); every intentional output
difference documented.

### 10.2 Matrices

- **Builtin matrix**, per `BuiltinId`: valid/invalid receiver, arity, HOF
  param inference, coercions, both lowerings (cross-backend semantic
  agreement is validated here), preamble registration.
- **Fact matrix**, per fact kind: both polarities, `&&` composition
  (including dependent chains), `||`/De-Morgan handling, every supported
  position, falsy corner cases, evaluation order. Generated tests are
  appropriate — the architecture is explicitly fact × position × polarity.
- **Name tests:** hint collisions, repeated hints, nested scopes, backend
  keywords, two source names escaping to one candidate, allocation
  stability.
- **Error tests:** every user-facing rejection returns `err` with the right
  kind and span; unsupported input is never misreported as
  `internalInvariant`.

### 10.3 CI tiers

Fast TS unit tests → golden/differential → Dafny generation+verification →
Lean generation+verification → self-application targets. Verification time
is tracked as a regression metric; generated backend files live in CI
artifacts/caches unless reviewing them in-tree earns its churn.

## 11. Risks

- **Registry drifts from emitter coverage.** A builtin classified in the
  registry may lack a lowering in one emitter; that surfaces exactly as
  today (an emit-time error), and the builtin matrix (§10.2) pins the
  intended support per backend.
- **Refactor churn hides compiler bugs.** Byte-for-byte gauntlet;
  consumer-by-consumer flips where lists are unpartitioned (§3.3), staged
  rule families with temporary fallbacks where they are (§4.3); every
  deletion lands in the commit whose gauntlet run gates it.
- **Proof work blocks practical fixes.** Executable checks and phase
  predicates land first; P1 proofs accrete; P2 never enters the critical
  path.
- **Claims outrun trust.** The P/T classification and TCB table (§8) are
  normative; "verified" in docs must cite a P/T level.
- **Verification time grows.** Tiered CI, verify-changed-modules fast path,
  cached backend artifacts, tracked timings.

## 12. Acceptance criteria

- **Builtins:** neither `narrow` nor `transform` identifies a builtin by
  receiver/name spelling (emitter dispatch stays `(objTy, method)` by
  design, §3.2); no duplicated allowlists/HOF/purity sets remain; adding
  a builtin = one registry entry, its per-backend emit rules, and matrix
  tests.
- **Conditions:** condition semantics live in one module both passes
  consult; `narrow` is ~6 positional drivers; adding a fact kind = one
  analyzer case + (if needed) one materializer case + matrix tests, with
  every position inherited for free.
- **Structure and state:** structured generic args everywhere; declaration
  lookup via `TypeDecls`; no mutable module-level state in portable passes;
  user-facing failures are `Result`s; all binders and backend names flow
  through the two allocating APIs.
- **Self-application:** selected portable modules compile through `lsc` on
  both backends in CI; initial P1 contracts verify; docs state each
  module's P/T level; no self-verification claim is made from T0 alone.

---

## Appendix: departures from an earlier design

For the record, where this document deliberately differs from an earlier
reviewed draft of this program (the RFC), and why:

- **Kept from the RFC:** the P/T two-axis trust model, TCB table, and
  claims discipline (§8); backend-name injectivity via an allocating
  environment (§6.3); the sharpened freshness contract with the
  scope-completeness obligation (§6.2); the exhaustive-consumer principle;
  structured `CompileError`; the test matrices.
- **Builtins:** the RFC split each builtin across four modules
  (`builtin-id` / `builtin-semantics` / `dafny-builtins` /
  `lean-builtins`). This document keeps the `BuiltinId` identity and
  resolve-once principle but scopes the registry to classification only:
  lowerings stay inside the existing emitters with their `(objTy, method)`
  dispatch (no separate lowering modules, no registry-embedded lowering
  functions, no identity threading across the transform boundary — §3.2).
  An intermediate draft co-located both backend lowerings in each registry
  entry for side-by-side review; that was dropped as relocation without
  deduplication — cross-backend agreement is validated by the builtin test
  matrix instead. The `BuiltinCapabilities` record (five fields) is
  trimmed back to `pure` until a consumer needs the distinction; `ArgMode`
  roles are dropped in favor of the concrete `intArgPositions`/`hof`
  fields the compiler consumes today.
- **Conditions:** the RFC's branch-structured `GuardPlan` stored in a
  `TCondition` IR wrapper is replaced by the shared ordered-fact analyzer
  (§4). The RFC's dependent-conjunction objection does not defeat ordered
  facts — order carries the dependency. The tree remains the named
  escalation path, triggered by a concrete failing example, not adopted up
  front; nothing is threaded through the IR.
- **Transform split:** demoted from a scheduled phase back to a
  triggered watch item (§7), per the original design note.
- **Process:** the RFC's Phase 0 (baseline infrastructure program) is
  folded into "the existing gauntlet is the baseline"; the registry
  migration leads the roadmap instead of following process work.
