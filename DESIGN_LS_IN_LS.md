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

### 8.6 Porting doctrine: extend the toolchain, don't contort the source

*Adopted 2026-07-22, out of the peephole port survey (§9 step 9).*

When a module port hits a subset gap, the default is to extend the
toolchain, not rewrite the module: if the blocked idiom is one a
reasonable LemmaScript user would write, the port has found a missing
feature, and the fix belongs in the compiler — each such extension is a
generally useful feature independent of self-application (§8.5's own
test). A source rewrite is justified only when:

- the design already condemns the idiom (module-level mutable state,
  §6.1; hand-rolling a walker `ir.ts` already exports);
- the idiom is genuine parametricity, which the ecosystem's erasure
  doctrine deliberately omits (§5.1); or
- verification irreducibly demands something no emitter strategy can
  waive (a termination argument for non-structural recursion).

This keeps §8.3 honest: the port grows the subset as a standing
gauntlet, rather than bending the codebase to fit today's subset.

Empirical anchors from the survey (minimal repros, 2026-07-22):

- **Imports-as-axioms is the P0 cross-module answer, and it already
  works.** Imported functions emit as body-less `{:axiom}` functions;
  imported union types re-synthesize as full datatypes. Each
  self-applied module stays an independently checkable artifact. Real
  linking (`include` of the already-generated `.dfy`) is the named
  escalation path, triggered by the first P1 lemma that must see
  through an import boundary.
- **Predicate-position HOFs verify because they lower to quantifiers**
  (`.some(a => anyExpr(a, pred))` → `exists a :: a in args && …`),
  whose termination Dafny discharges structurally — this is why
  `ir.dfy`'s walkers verify. Rebuild-position `.map` lowers to
  `Std.Collections.Seq.Map`, through which recursive calls do not
  termination-check; the semantically identical seq comprehension
  `seq(|s|, i requires 0 <= i < |s| => f(s[i]))` verifies.
- **Mutable-capture closures** (`let found = false` flipped inside a
  lambda) are a genuine deep gap — effectful closures have no model in
  the pure fragment. Not scheduled: every current use in the portable
  core is a hand-rolled walker that `ir.ts` queries replace (R2 below).

**Extension ledger** (each lands with a gauntlet run; E2 is a
deliberate output change, documented per §10.1):

| # | Extension | Status |
|---|---|---|
| E1 | Imported named record types expand to structures (previously they synthesized opaque, so rebuilding an imported record — `{ ...a, body }` on a `MatchArm` — failed as a datatype update on an opaque type) | done (2026-07-22): the semantic import resolver stopped at anonymous union variants (`__type` symbols), so variant fields were never walked; it now recurses into them, with a compiler-`Type`-keyed visited set since recursive unions become reachable. Gauntlet byte-for-byte on both backends; one deliberate self-run artifact change: `ir.dfy`'s imported `Ty` upgraded from opaque to the full datatype, re-verified |
| E2 | Array `.map` lowers to a seq comprehension so recursive rebuild walkers termination-check (mirrors the `.some`/`.every` quantifier lowering); also drops the `Std` dependency for map | done (2026-07-22), Dafny only: one uniform lowering — `seq(\|s\|, i requires 0 <= i < \|s\| => …)` with a literal lambda beta-reduced through a `var` binding (an applied closure defeats the termination checker; verified empirically) and any other argument applied to `s[i]` directly; `Seq.Map` is gone. Index freshness is an IR-level `usesName` check (no string scanning), a local check until §6.3. Deliberate output change (§10.1): 7 gauntlet examples + `ir.dfy` re-lowered, all re-verified. Lean's `.map` is untouched — revisit with the deferred mutual-block work if Lean termination needs it |
| E3 | `const`-bound lambda aliases (`const r = (x) => walk(x, f)`) work when called from inside a nested lambda — direct calls and direct-position uses already work; only this composition breaks | done (2026-07-23), in two general halves: calls through fn-typed values (locals, parameters) classify pure — the fragment has no effectful closures, so lifting them to statement binds (which forced lambdas multi-statement) was never needed; and lambdas always take their return type from the checker, so unannotated lambdas carry a real fn type. Gauntlet byte-for-byte on both backends |
| E4 | `find` builtin: registry entry, both lowerings, matrix row (§10.2) | open — no longer on peephole's path (R3's monomorphic split uses direct two-arm checks); still generally useful |
| E5 | Structured rejection instead of garbage output for function-valued consts and anonymous-record generic bounds (today: `type { pattern: MatchPattern; body: any }(==)` — invalid Dafny) | open — peephole's instance dissolved with R3; the general rejection is still owed. Related fixed en route (2026-07-24): a call through an indexed function value (`rules[i](e)`) crashed transform outright rather than rejecting |

**Rewrite ledger** for `peephole.ts`, each justified by doctrine, not
subset-appeasement:

| # | Rewrite | Justification | Status |
|---|---|---|---|
| R1 | `EXPR_RULES` mutable module global with per-backend reassignment → direct rule chain with a threaded backend flag | §6.1, already adopted | done (2026-07-23) — exactly as prescribed; a rules-array attempt confirmed the fragment has no function-valued collections (`rules[i](e)` is out), so the direct chain is what remains |
| R2 | private `mapExpr` + `containsVarRef*` → ir.ts `usesName`/`usesNameInStmts` (~100 lines deleted) | reuse-walkers agreement; also removes peephole's only mutable-capture closures | done (2026-07-23); also closed a latent hole — the private check didn't look inside lambda bodies before dropping a binding |
| R3 | `getSomeNoneArms<A>` → two monomorphic helpers (`MatchArm` / `StmtMatchArm` arms) | genuine parametricity — its `body` is `Expr` in one instantiation, `Stmt[]` in the other; erasure doctrine (§5.1) has no honest single bound | done (2026-07-23), with direct two-arm checks (decoupled from E4) and named result records |
| R4 | fixed-point rewrite loop gets an explicit fuel parameter (`//@ decreases fuel`) | irreducible verification price; the `guard < 100` counter is fuel already. The lexicographic (match-count, if-count) measure — rules 1/6 drop match-count, rules 2–5 preserve it and drop if-count — is shelved as future P1 content | done (2026-07-24), stronger than planned: fuel rejected; the loops became plain recursion and real termination is proven Dafny-side (see the order note below). The lexicographic-count measure itself turned out unsound under rule duplication (`k in m … m[k]` copies the receiver); the proof instead weighs only the non-normal part of the term, which is immune to duplicating already-rewritten subtrees |

Order: E1–E2 first (they gate every rebuild-style walker, not just
peephole), then E3, then E4–E5 as convenient; then R1–R4; then annotate
`peephole.ts` and add it to `LemmaScript-files.txt`. Done when peephole
is P0/T0 on Dafny in the self-run.

*Outcome (2026-07-24): exceeded — peephole is in the self-run at P1/T0.
`peephole.dfy` (555 generated lines + ~1,400 hand-authored, additions-only
under the regen merge) machine-checks, per its `LemmaScript-files.txt`
entry (extra per-file Dafny flags after the timeout; the proof needs a Z3
quantifier-instantiation throttle, `smt.qi.eager_threshold=30`):*

- *termination of the whole rewrite engine — no fuel, no rule guard: the
  measure weighs only the non-normal part of a term, so duplicated
  receivers (already normalized by the bottom-up engine) weigh zero;*
- *normalization — engine output provably contains no firable rule and no
  mergeable statement pair;*
- *idempotence — normal input provably passes through unchanged;*
- *per-rule strict decrease, and full normality of merged statements.*

*The proof forced three engine fixes, each landed in TS gauntlet-clean:
the pair scan now iterates to a fixed point (a merge can expose a new
adjacent pair; each merge shortens the list, bounding the passes);
constructor arguments and map-literal entries joined the rebuild walk
(they were silently skipped); and `while`'s `decreasing`/`doneWith` spec
fields are documented as deliberately un-peepholed rather than silently
assumed normal. En route, two general toolchain features landed (both
gauntlet byte-for-byte): variant narrowing in resolve — positive
discriminant checks in `&&`-chains and negated checks in early-return
guards now narrow, and union field reads resolve against the narrowed
variant — and variant-aware destructor naming, where reads and datatype
updates of collision-renamed fields (`value_bool`, `body_let`) translate
correctly via ctor pinning (by field type, or match-arm context) and
union-qualified rename keys.*

**Narrow port survey** (minimal repros, 2026-07-24; `narrow.ts` ports
together with `condition-facts.ts`, §8.3):

- **Confirmed already-supported**, beyond the peephole precedents (spread
  updates, `??` rule chains, mutual recursion, slice recursion): `Set`
  locals lower to Dafny `set` with `{}`/`in`/`+` and verify; C-style `for`
  loops in both directions, including non-null-asserted indexing (`xs[i]!`);
  template literals — including number interpolation, which synthesizes
  `NatToString`/`IntToString` (covers `freshOcBinder`'s `` `_oc${n}_val` ``).
- **Imported records with fn-valued fields synthesize opaque.** narrow reads
  one bit through such a record (`builtinSpec(id).pure` in
  `containsMethodCall`); the opaque `Spec(==)` synthesis makes the field
  read a resolution error. Fix on the builtins side: export a scalar
  accessor (`builtinPure(id): boolean`), which axiomatizes cleanly — a
  first, tiny step of §8.3's "builtins.ts P1 after reshaping".
- **Three new garbage-output shapes for E5**, all avoided by the rewrites
  below so none blocks the port: datatype-field assignment inside a match
  arm emits `e.isDiscriminant := true;` (invalid); a generic record decl
  leaks its free type var (`datatype Found = Found(check: C, …)`);
  `Extract<>`/indexed-access aliases emit `type Chain["steps"](==)`.
- **`array.find` has a registry entry but no Dafny lowering**
  ("Unsupported Dafny method call: .find()") — E4 returns to the critical
  path via `typeofStringFact`'s `decl.variants?.find(...)`.
- **`freshName` needs no rewrite for the port**: it is deterministic
  w.r.t. the module's seeded user-name set (same hint → same result), so
  at P0/T0 it axiomatizes as a pure imported function. The §6.2
  `NameSupply` refactor is what the P1 *freshness contract* needs, not the
  port.

**Rewrite ledger** for `narrow.ts`/`condition-facts.ts`, per doctrine:

| # | Rewrite | Justification | Status |
|---|---|---|---|
| N-R1 | `CondCtx.oc` mutable counter (`ctx.oc.n++` — extract rejects the expression outright) → thread it: `freshOcBinder` returns name + next ctx | §6.1/§6.2 already condemn mutation-through-reference; the first real NameSupply-shaped state | open |
| N-R2 | `restoreDiscriminantFlag`'s in-place `unwrapped.isDiscriminant = true` → return the rebuilt node | the pure fragment has no datatype mutation (today's emission for that shape is invalid Dafny) | open |
| N-R3 | `extractConjunct<C>` with fn-valued `parse` → two monomorphic extractors (presence, isArray) | genuine parametricity; mirrors peephole R3 | open |
| N-R4 | `binderHintForMapAccess`'s regex `.replace(/_val$/…)`/`(/^_/…)` → `endsWith`/`slice` string helpers | §8.5 named exactly this; `string.replace` is not a builtin at all | open |
| N-R5 | `ruleDiscriminantChain`'s nested `function collectElse` closing over mutable `cases` → top-level recursion returning values | mutable-capture closure, the known deep gap (§8.6 anchors); extract rejects nested fn decls anyway | open |
| N-R6 | no-init `residualLeaves.reduce((a, b) => a \|\| b)` → recursive or-fold helper | the no-init form has no lowering (and an empty-list hazard besides) | open |
| N-R7 | `Extract<TExpr, {kind:"optChain"}>` / `OptChain["chain"]` → use typedir's already-named `TChainStep[]` | type-level operators have no backend model; two-line change | open |
| N-R8 | narrow's `builtinSpec(id).pure` → `builtinPure(id)` scalar accessor in `builtins.ts` | fn-valued record fields don't cross the import boundary (repro above) | open |

**Proof outlook.** The engine re-walks freshly constructed terms (every
`&&`-driver re-walks its residual; `ruleEarlyReturnOrChain` duplicates the
terminating branch across None arms), so termination is again the
irreducible price, and peephole's active-weight architecture (§8.7) is the
template: weigh only un-narrowed condition material (presence checks,
`optChain`/`nullish` nodes, isArray conjuncts) — every rule strictly
consumes some of it, and duplicated already-walked branches weigh zero.
The flagship P1 property is catalog #2, desugaring completeness: engine
output provably contains no `optChain`/`nullish` node.

Order: N-R7, N-R2, N-R4, N-R6, N-R8 first (small; each is a pure refactor
gated byte-for-byte); then E4; then N-R3, N-R5, N-R1; then annotate and
add to `LemmaScript-files.txt` (P0); then the termination + completeness
proofs (P1).

### 8.7 Proof-carrying self-run modules: conventions

*Distilled from the peephole proof (2026-07-24); binding for later ports
(`narrow` next). `peephole.dfy` is the exemplar.*

**Layering.** A proof-carrying `.dfy` is the generated text plus hand
additions, nothing else — `dafnyCheckDiff` enforces additions-only and the
three-way regen merge preserves the additions. Hand lines may be inserted
*between* generated lines, including inside function bodies (assert and
lemma-call statement-expressions before a case's result expression) and
between a generated signature and its `{` (requires/ensures/decreases).
Never modify a generated line, and keep the generated case *order*: when a
source change reorders the emitted match arms, relocate the hand blocks to
follow. Prefer standalone lemmas over in-body scaffolding where possible —
they cannot conflict in the merge.

**Verifier flags.** `LemmaScript-files.txt` entries are
`filepath [timeout_seconds] [extra dafny flags…]`; a timeout above 60s
degrades the entry to gen-check in CI unless `--slow`. Peephole needs
`--boogie /proverOpt:O:smt.qi.eager_threshold=30`: the mutually recursive
predicate/measure families induce a Z3 quantifier-matching loop that makes
even trivial assertions diverge, and the threshold tames it. Expect the
same for future proof-carrying modules.

**Dafny idioms that recur** (each cost an iteration to discover):

- Seq-of-datatype recursion terminates only in single structural steps:
  the element hop (`ss[0]`) and the field hop (`.body`) must be separate
  functions — a combined `f(ss[0].body)` defeats the rank axioms.
- Definitional unfolding at a symbolic term often needs a
  constructor-reconstruction assert first:
  `assert e == Expr.match_(e.scrutinee, e.arms);`.
- A lemma invoked from inside a recursive group must keep function
  applications out of its `requires` (pass pointwise facts instead), or it
  joins the call graph and needs its own aligned `decreases`.
- Same-argument mutual definitions (a predicate and its kids-predicate)
  need explicit tier decreases: `decreases x, 1` / `decreases x, 0`.
- Elem-bound lemmas state forall-ensures and bridge slices with
  `assert forall j | 1 <= j < |es| :: es[j] == es[1..][j-1];`.

**Peephole's proof architecture**, for orientation: a normality-predicate
family mirrors exactly what the engine can fire on (per-node rules, list
pair-redexes matching the scan, and a deliberate exclusion — `while`'s
`decreasing`/`doneWith` spec fields are never rewritten, so normality does
not claim them). The termination measure is *active weight*: normal
subtrees weigh zero — which is what makes rule-duplicated receivers
harmless with no rule guard — with root charges ordering the rule chain
(match/let 3, if 2, other 1) and a padded list weight (`PSs`) dominating
elementwise-normalized lists. Engine decreases are 4-component nat tuples
(active weight, structural size, list length, tier). Rule lemmas prove
each fired rule strictly shrinks the weight; the engine's ensures give
normalization (output is normal) and idempotence (normal input is
returned unchanged).

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
   — *partial (2026-07-21): `typedir.ts` is the first self-compiled module —
   P0/T0 on Dafny (`lsc check` on the live source: generation + Dafny
   verification clean, including the mutually recursive `TExpr`/`TStmt`
   datatypes and the `tyEqual`/`tysEqual` mutual recursion, whose
   termination Dafny proves from default rank measures — explicit
   `decreases` pragmas are unnecessary and in fact break the joint
   measure). Enabling toolchain work, all gauntlet byte-for-byte: extract
   recovers declared type text where the semantic printer degrades
   self-referential aliases to `__type`; transform generates per-union
   discriminator functions (`Ty_kind`) for surviving `.kind`-as-value
   reads; both emitters sanitize constructor names from source strings
   (`"spec-pure"` → Dafny `spec_pure`, Lean `«spec-pure»`). Source-side:
   typedir's inline payload records are named (`TRecordField` etc. —
   anonymous record types have no backend model) and `tyEqual`'s
   indexed-`every` calls became recursive `tysEqual`/`stringsEqual`.
   Lean self-compilation stays blocked on the deferred mutual-block
   emission (step 1). Self-run wired (2026-07-22) via the ecosystem's own
   convention: a root `LemmaScript-files.txt` lists the self-applied
   modules (compiler only — the `examples/` gauntlet is fixtures with its
   own driver, not the repo's verified surface), sources carry
   `//@ backend dafny` until Lean un-defers, and `./tools/check.sh dafny`
   with no arguments is the self-run. The `.dfy` artifacts are checked in
   beside the sources, ready to host hand-authored P1 lemmas via the
   regen merge. CI: a dedicated `self-verify` job in `ci.yml` runs the
   same batch (`check.sh dafny`) with the checkout's own toolchain.
   Deliberately not the reusable `verify.yml`: that workflow means
   "verify against an external LemmaScript ref" (right for case studies,
   and its clone path collides with the compiler repo's own workspace);
   the self-run means "gate the change with its own code" — a real
   semantic difference, kept visible rather than special-cased. Also
   deliberately not a case-studies-matrix entry: an entry would verify
   main's sources/artifacts with the PR's toolchain, going red exactly on
   PRs that legitimately regenerate the self-run artifacts in-PR. This is
   T0 per §8.2: the translator is trusted — the proofs are about what
   this compiler generated from itself, not compiler correctness.
   First P1 content (2026-07-22), lifting `typedir` to P1(partial)/T0:
   **`tyEqual` is an equivalence relation** — reflexivity, symmetry, and
   transitivity, each with its `tysEqual`/`stringsEqual` companion — the
   property the compiler implicitly leans on wherever it dedupes or
   compares types. Convention (quorum-style): each lemma is *stated as a
   TypeScript function* in `typedir.ts` (`tyEqualTrans(a, b, c)` with
   `//@ requires`/`//@ ensures \result === true`), so what holds is
   readable without leaving TS; the inductive proof is hand-authored
   inside the generated `_ensures` lemma body in `typedir.dfy`, preserved
   by the regen merge, verified by the self-run (17 obligations, all
   discharged; `tysEqual` also carries an auto-proved length-preservation
   ensures). Note the mode rule this surfaced: once any function in a
   module carries `//@ verify`, generation is opt-in — every function of
   a self-applied module must be annotated.
   `ir.ts` (2026-07-22): P0 on Dafny — self-compiles and verifies (the
   full `Expr`/`Stmt`/decl datatype family, the mutually recursive
   walkers, fn-type aliases, rest params). The last blocker was
   `Match.scrutinee: string | Expr` (a bare string as shorthand for a var
   scrutinee); it is now `Expr` everywhere — *type the IR seams: a string
   standing in for a node at a layer boundary makes every consumer pay a
   `typeof` toll, and such unions are unmodelable in the subset*. The
   refactor was byte-for-byte (Dafny's scrutinee printer already escaped
   both forms identically) and deleted the string branch from every match
   consumer in transform, peephole, and both emitters.
   Toolchain gained along the way (all gauntlet byte-for-byte):
   undeclared user types synthesize opaque decls (imported types are
   opaque by default — the coarse first half of the cross-module story,
   matching the `_synthOpaque` doctrine); `CTOR_MAP` lookups are
   `Object.hasOwn`-guarded (a variant literally named `constructor` hit
   `Object.prototype.constructor`); collision-suffixed destructor names
   sanitize. Source-side IR cleanups: `constructor.args` is required
   (`Expr[]`, not optional — the shared-field-name/different-optionality
   clash misled variant-blind field typing); ir's inline payload records
   are named (`Param`, `RecordField`, `MapEntry`, `CtorInfo`,
   `EmitOption`). Still ahead: the scrutinee PR (completes ir P0),
   `names.ts` after its §6 refactor (first P1 freshness target), full
   cross-module imports (§8.5).*
9. **`peephole`, then `narrow`** in-subset with completeness + freshness
   contracts. — *peephole done (2026-07-24), at P1/T0 with proofs beyond
   the plan: machine-checked termination (fuel-free), normalization, and
   idempotence; ledger outcomes and the three proof-driven engine fixes
   are annotated in §8.6. `narrow` is next: port survey done
   (2026-07-24) — repro findings and the N-R1–N-R8 rewrite ledger are in
   §8.6; code not started.*
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
