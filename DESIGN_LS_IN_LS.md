# LS-in-LS: Compiler Architecture and Self-Application

**Status:** Proposed
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
   and one registry entry holding its type rule, classification data, and
   both backend lowerings side by side. `resolve` assigns the identity once;
   no later pass re-recognizes `(receiver type, method name)`.
2. **Shared condition analyzer.** One module answers "what does this
   condition establish" as an ordered fact list plus residual. Both `resolve`
   (for typing branches) and `narrow` (for rewriting) consult it. Narrowing
   collapses to ~6 positional drivers over shared materializers.
3. **Structured types and `TypeEnv`.** Generic arguments become structured
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

### 3.1 Shape

One stable identity per supported operation, and one entry per identity:

```ts
type BuiltinId = "array.includes" | "array.map" | "string.trim"
  | "map.has" | /* every supported builtin */;

interface BuiltinSpec {
  recv: RecvKind;                     // recognition key: receiver type kind
  method: string;                     // recognition key: surface method name
  ret(objTy: Ty, args: TExpr[]): Ty;  // return-type rule
  pure: boolean;                      // safe in expression-only positions
  hof?: { lambdaParamTys(objTy: Ty, args: TExpr[]): Ty[] };
  intArgPositions?: number[];         // nat/int coercion sites
  needs?: PreambleId[];               // SeqIndexOf, StringTrim, …
  dafny(obj: string, args: string[], e: MethodCall, ctx: EmitCtx): string;
  lean(obj: string, args: string[], e: MethodCall, ctx: EmitCtx): string;
}

const BUILTINS: Record<BuiltinId, BuiltinSpec> = { /* one entry each */ };
```

The recognition index (`(recv, method) → BuiltinId`) is *derived* from
`BUILTINS`, so adding a builtin is literally one entry. `resolve` performs
recognition once and annotates the typed method-call node with its
`BuiltinId` (a field on the existing node — no new IR node kind). Downstream:

- `narrow` drops its builtin-name allowlists and checks `spec.pure`;
- `transform` drops `HOF_METHODS` and the coercion special cases, reading
  `spec.hof` / `spec.intArgPositions`;
- both emitters' method-call cases become a lookup and a call.

`Record<BuiltinId, BuiltinSpec>` makes exhaustiveness a type error: a new id
without an entry, or an entry without both lowerings, fails to compile.

### 3.2 Consequences accepted

- **One file, both lowerings side by side.** The Dafny and Lean emit rules
  for a method are reviewable together — this is a deliberate property, and
  the reason the registry is not split into per-backend modules.
- **Cross-layer types in one module.** The registry imports `Ty`, `TExpr`,
  and `EmitCtx` types. That is the honest common shape; the alternative
  (backend-neutral IR rewrites for every builtin) is rejected because
  `sort`/`split`/`delete` genuinely differ per backend.
- **`pure` stays one bit for now.** Purity, totality, and
  expression-lowerability are conceptually distinct, but every current
  consumer asks the same question. The bit splits into named capabilities
  only when a concrete builtin needs the distinction — no speculative
  effect system.
- **Entries may be long.** Genuinely structural cases (set-comprehension
  `filter`, `some` with inlined lambda) stay in their entries even at ten
  lines; they are not evicted to keep entries pretty.
- **The registry table itself stays outside the verified subset**
  (function-valued record fields). Verified code reaches registry-derived
  facts through `//@ extern` contracts if ever needed.

### 3.3 Migration

Family by family (array, string, map, set), deleting the corresponding
allowlist/HOF/purity entries as each family moves. Each step is verified
byte-for-byte against the `examples/` gauntlet output. Done when no pass
after `resolve` identifies a builtin by receiver/name spelling and no
duplicated classification list remains.

## 4. Decision: shared condition analysis

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
function analyze(cond: TExpr, env: TypeEnv):
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

## 5. Decision: structured types, `TypeEnv`, `Result`

### 5.1 Structured generic arguments

```ts
{ kind: "user"; name: string; args: Ty[] }
```

`tyEqual` becomes structural (not `JSON.stringify`), base-name slicing
disappears, alias expansion receives explicit arguments, and contracts can
recurse over actual type structure. `parseTsType` stays on the extraction
side (it depends on ts-morph); `resolve` receives only portable `Ty`.

### 5.2 `TypeEnv`

One lookup abstraction over `typeDecls`, implemented as a datatype plus
plain helper functions (portable to the subset — no function-valued record
fields required):

```ts
function declOf(env: TypeEnv, name: string): TypeDeclInfo | null;
function unionDecl(env: TypeEnv, ty: Ty): UnionDecl | null;
function discriminantOf(env: TypeEnv, ty: Ty): string | null;
function variantWithField(env: TypeEnv, ty: Ty, f: string): VariantInfo | null;
```

Replaces the `_typeDecls.find(...)` scans re-spelled at every use site.

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
| `typedir.ts` | 194 | Prime P0/P1 | Structural `tyEqual` (an improvement anyway). |
| `names.ts` | 56 | Prime P1 | Tiny, real spec content (freshness, keywords). |
| `peephole.ts` | 444 | Early pass target | Self-contained IR→IR rewrites. |
| `narrow.ts` | 1114 | P1 after §4 | Facts×positions roughly halves the surface to port. |
| `transform.ts` | 2396 | P1 by stages | Needs ctx work; port stage-by-stage (§7 trigger). |
| `resolve.ts` | 1778 | Mostly | Push `parseTsType` to extraction; core is pure Raw→Typed. |
| `specparser.ts` | 330 | P1 | Recursive-descent parser; classic verification fodder. |
| `dafny-emit.ts`/`lean-emit.ts` | 2292 | Partial | After §3 the residual emitters are smaller; precedence logic is spec-worthy; regexes become string helpers. |
| `extract.ts` | 2479 | Trusted frontend | Wraps ts-morph; stays unverified; `RawModule` is the trusted input. |
| `lsc.ts`, commands | ~500 | Unverified driver | CLI, fs, process. |

Net: roughly 6.5k of 12.7k lines are pure IR-to-IR passes, all portable in
principle. Once a module is in-subset, it joins CI as an `lsc` self-run
target so it cannot drift back out — the compiler becomes a standing
regression gauntlet that grows with itself.

### 8.4 P1 property catalog (value-per-effort order)

1. **Freshness** (§6.2) — kills the name-capture bug class permanently.
2. **Desugaring completeness** — after `narrow`, no `optChain`/`nullish`
   nodes remain (an `anyExpr`-style predicate, provable by the structural
   induction the prover does for us). Today enforced by "transform would
   crash."
3. **Backend name legality and injectivity** (§6.3).
4. **Arm purity** — after transform (Dafny mode), no impure call remains in
   a match-expression arm; a guard inside one rule becomes a postcondition
   of the pass.
5. **Match exhaustiveness** — every emitted `tagMatch` covers all variants
   or has a fallthrough, checked against its `TypeDeclInfo`.
6. **Parser sanity** — `specparser` consumes the whole input or errors.
7. **Typing boundary** — successful `resolve` leaves no `unknown` where
   later passes require a concrete type.

Notably absent: "the generated code means the same as the TS" — that is
P2. P1 proves the compiler doesn't produce malformed output and doesn't
capture names, which is where its actual bug history lives.

### 8.5 Required subset features

Each is a generally useful feature independent of self-application:

1. **Recursive and mutually recursive datatypes.** `Expr`/`Stmt` contain
   each other. Both backends support this natively; the work is extraction.
   *The single hard prerequisite — spike it first (§9).*
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

1. **Mutual-recursion spike** (parallel with 2). A toy `MiniExpr`/`MiniStmt`
   with a structural fold, one nested exhaustive match, one postcondition,
   verified on both backends. Prices the one hard prerequisite before any
   porting commitment. Blocks §9 steps 8+ only, not the architecture work.
2. **Builtin registry** (§3), family by family; delete old lists as each
   family moves.
3. **Structured user types, structural `tyEqual`, `TypeEnv`** (§5.1–5.2),
   small PRs.
4. **`Result`/`CompileError`** (§5.3) on leaf modules first, then riding
   along with each pass migration.
5. **Ctx threading and `NameSupply`** (§6.1–6.2) — mostly falls out of 2–4.
6. **Condition analyzer and fact migration** (§4), family by family; delete
   old rule families; wire `resolve` to the shared analyzer.
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
execution during family migrations; every intentional output difference
documented.

### 10.2 Matrices

- **Builtin matrix**, per `BuiltinId`: valid/invalid receiver, arity, HOF
  param inference, coercions, both lowerings, preamble registration.
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

- **Registry becomes a god module.** Accepted with eyes open (§3.2): one
  file importing cross-layer *types* is the cost of side-by-side review.
  If the file's imports grow beyond types into pass logic, that is the
  signal to revisit.
- **Refactor churn hides compiler bugs.** Byte-for-byte gauntlet, family
  migration, temporary fallback chains, no big-bang deletions.
- **Proof work blocks practical fixes.** Executable checks and phase
  predicates land first; P1 proofs accrete; P2 never enters the critical
  path.
- **Claims outrun trust.** The P/T classification and TCB table (§8) are
  normative; "verified" in docs must cite a P/T level.
- **Verification time grows.** Tiered CI, verify-changed-modules fast path,
  cached backend artifacts, tracked timings.

## 12. Acceptance criteria

- **Builtins:** no pass after `resolve` identifies a builtin by
  receiver/name spelling; no duplicated allowlists/HOF/purity sets remain;
  adding a builtin = one registry entry plus tests.
- **Conditions:** condition semantics live in one module both passes
  consult; `narrow` is ~6 positional drivers; adding a fact kind = one
  analyzer case + (if needed) one materializer case + matrix tests, with
  every position inherited for free.
- **Structure and state:** structured generic args everywhere; declaration
  lookup via `TypeEnv`; no mutable module-level state in portable passes;
  user-facing failures are `Result`s; all binders and backend names flow
  through the two allocating APIs.
- **Self-application:** selected portable modules compile through `lsc` on
  both backends in CI; initial P1 contracts verify; docs state each
  module's P/T level; no self-verification claim is made from T0 alone.

On finalization, `DESIGN_SUGGESTIONS.md`, `LS_IN_LS.md`, and
`LS_IN_LS_RFC.md` are deleted — this document is the single source of
truth.

---

## Appendix: departures from the reviewed RFC draft

For the record, where this document deliberately differs from
`LS_IN_LS_RFC.md` and why:

- **Kept from the RFC:** the P/T two-axis trust model, TCB table, and
  claims discipline (§8); backend-name injectivity via an allocating
  environment (§6.3); the sharpened freshness contract with the
  scope-completeness obligation (§6.2); the exhaustive-consumer principle;
  structured `CompileError`; the test matrices.
- **Builtins:** the RFC split each builtin across four modules
  (`builtin-id` / `builtin-semantics` / `dafny-builtins` /
  `lean-builtins`) and banned function-valued entries. This document keeps
  the `BuiltinId` identity and resolve-once principle but restores the
  single-entry registry with both lowerings side by side — the review
  property the split silently gave up. The `BuiltinCapabilities` record
  (five fields) is trimmed back to `pure` until a consumer needs the
  distinction; `ArgMode` roles are dropped in favor of the concrete
  `intArgPositions`/`hof` fields the compiler consumes today.
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
