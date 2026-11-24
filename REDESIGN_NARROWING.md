# REDESIGN_NARROWING — Checked reads of current storage

**Status:** steps 1–2 implemented on `redesign-narrowing`, November 23, 2026.
Baseline: `main` at
[`966272f`](https://github.com/midspiral/LemmaScript/commit/966272f70ea708ba8d84e95bafa610c3e2b8a1d3).
The prototype reviewed here is [PR #378](https://github.com/midspiral/LemmaScript/pull/378)
at `922bc4a`. This document records the staged replacement and remaining work;
the implemented read model is documented in
[ARCHITECTURE_NARROWING.md](ARCHITECTURE_NARROWING.md) and [TOOLS.md](TOOLS.md).

## Decision

Develop one implementation of optional narrowing through **checked reads**:
keep the declared storage type stable, read the current value, and require
the backend verifier to establish that an unwrap is valid at that use.
TypeScript's flow information can suggest an unwrap; it cannot discharge
its proof obligation.

Build this from current `main` in bounded steps. Preserve the lexical naming
work from [#377](https://github.com/midspiral/LemmaScript/pull/377) and the
assignment-expression boundary from [#372](https://github.com/midspiral/LemmaScript/pull/372).
Ordinary optionals come first. Distinguishing `null` from `undefined`, changing
union lowering, and supporting assignments used as values are separate steps.
The pending PRs supply implementation ideas and regression cases, rather than
a stack of overlapping narrowing implementations to merge wholesale.

## Why change the read model

The baseline pipeline rewrites guards into `someMatch` / `tagMatch` and
substitutes pattern binders for later reads of the narrowed path. Those
binders hold values from the earlier match. Reassignment can leave later
reads observing that earlier value; mutation can update the binder without
writing back to the source variable. Substitution also has to traverse every
expression and annotation while avoiding capture by other binders.

Consider:

```ts
export function replacePresent(input: number | undefined): number {
  let x = input;
  if (x !== undefined) {
    x = 5;
    return x;
  }
  return 0;
}
```

The relevant Dafny body should have this shape:

```dafny
var x := input;
if x.Some? {
  x := Some(5);
  return x.value;
}
return 0;
```

The assignment uses `x`'s storage type, `Option<int>`. The return reads that
storage after the assignment. Dafny checks that its `value` destructor is
defined. There is no old payload binder to invalidate or rebind.

Pattern matching remains useful for unions and explicit decomposition of
immutable values. The problem is substituting a captured value for future
reads of mutable storage. Source binding identity is still necessary:
[DESIGN_LEXICAL.md](DESIGN_LEXICAL.md) remains part of the foundation.

## Translation contract

1. **Storage types stay stable.** A local or field retains its declared
   representation throughout its scope. An inferred binding needs a stable
   representation covering its admitted assignments; the initializer's flow
   type alone may be too narrow. Require an annotation or report an unsupported
   form if that representation cannot be established. Assignment resolution
   uses the storage type, including wrapping a defined value for an optional.
2. **Narrowed reads carry an explicit coercion.** A typed expression records
   its storage operand and requested result type. Narrowing creates a proof
   obligation. A later write cannot leave a read referring to an earlier
   payload unless the TypeScript itself saved that payload in another binding.
3. **Flow information selects operations, not truths.** TypeScript hints and
   annotation condition facts may request a checked read. Neither changes the
   storage type, inserts an assumption, or justifies replacing a runtime test
   with a constant merely because flow analysis predicts its outcome.
4. **Evaluation is preserved.** Operands execute in source order and exactly
   as often as in the supported TypeScript fragment. `&&`, `||`, `?:`, `?.`,
   and `??` retain their conditional evaluation. This includes value-producing
   logical expressions, not only boolean connectives. Calls and their proof
   obligations must survive even when their result has a known type.
5. **Temporaries represent individual evaluations.** A temporary can preserve
   the single evaluation of an optional-chain receiver. It cannot replace
   later source reads across intervening writes. Separate call expressions
   are not the same storage location merely because their syntax matches.

Checked coercions are operations in the verification model, not new runtime
checks inserted into the production TypeScript. Their correctness depends on
preserving the source value and evaluation. A prover accepting the generated
program does not establish that the translation preserved TypeScript behavior.

## Responsibilities in the pipeline

**Extract** preserves source binding identity through `LexicalNames`. It may
attach a small TypeScript flow hint to a read when that information helps
select a coercion. This hint is optional metadata, not a second type system
or a proof. Type overrides and imported declarations still require the
existing model and trust boundaries.

**Resolve** keeps storage types separate from requested read types. It inserts
typed coercions for payload reads and conversions at assignments, arguments,
and returns. Condition facts remain useful for annotations, where there is no
TypeScript flow checker, and for configurations without usable TS hints.
Those facts request the same checked operations. Specification-only bindings
and quantified variables retain their lexical scopes.

**Narrow** stops manufacturing `someMatch` nodes for the optional behavior
covered by the replacement. Array-index bounds handling and existing union
lowering remain until their own changes are reviewed. The completed optional
step should have one read mechanism, with the corresponding old substitution
paths removed, rather than two permanent implementations selected by syntax.

**Transform and the emitters** lower the same checked operation according to
the backend's proof model. They preserve branch-local evaluation of lifted
calls and coercions. Supported direct mutations must update the source storage:
for example, an optional-array update must reconstruct the optional containing
the updated array. Updating only an extracted payload is insufficient.

**Peephole** may simplify representation conversions only when it preserves
their value, evaluation, and required checks. A shorter generated expression
is not evidence that a coercion or call can be discarded.

### Dafny and Lean obligations

For Dafny, a payload read can use `x.value`; its datatype destructor obligation
requires `x.Some?` at that point. Existing guards and loop invariants should
establish this through ordinary verification.

For Lean/Velvet methods, a checked operation such as `optionValue x` can expose
presence as a precondition and `x = some result` as its postcondition. Its spec
must be proved. VC generation then checks the operation against the current
state. [#367](https://github.com/midspiral/LemmaScript/pull/367) contains a small
implementation to evaluate as a foundation.

Pure Lean definitions and annotations need an actual proof of presence in
their elaboration context. A dependent `if` or a proven helper can provide it.
A method precondition is not automatically available inside a separate pure
definition. A pure companion must not erase a checked read, supply a default
for absence, or introduce an axiom to make elaboration succeed.

Loop invariants, termination measures, and `done_with` expressions must refer
to the appropriate current state. They need explicit coverage on both
backends. In particular, visiting `forof.doneWith` in a walker does not fix the
existing loss of that annotation during lowering to `forin`.

## Implementation sequence

### 1. Repair the remaining generated-binder collision

Port the focused collision fix and regression from
[#358](https://github.com/midspiral/LemmaScript/pull/358). An outer narrowing of
`u` and an inner narrowing of `m.u` can both introduce `i_u_arr`, turning
`m.u.length - u.length` into a value minus itself. The baseline can prove the
false result `0` even though `u = [1]` and `m.u = []` give `-1`.

Keep this fix independent of the redesign. #377 already covers source
shadowing; the old scope-aware substitution machinery in #358 need not all
be carried forward. Additional callback support is lower priority than
eliminating a demonstrated false proof.

### 2. Establish checked reads for ordinary optionals

Start a focused implementation from `main`, using #367 and the optional
portion of #378 as references. Keep the current datatype representation and
the existing discriminated-union and synthesized array-union lowering.

The optional milestone should cover variable and existing field-path reads,
assignments, early returns, loop guards, boolean chains, callbacks within the
supported capture model, and annotations. Preserve evaluation in optional
comparisons and value-producing logical expressions. Include direct mutations
only where the update to source storage is modeled correctly; give an explicit
diagnostic for an unsupported form encountered by the new path.

First establish correct generation and proofs on both backends, then migrate
representative case studies. Evaluate one with optional state or collection
updates and one with Lean loops and handwritten proof lemmas. Compiler line
count alone is not the success criterion: proof effort and generated-code
clarity also matter.

This stage does not resolve the existing conflation of `null` and `undefined`.
Keep [#304](https://github.com/midspiral/LemmaScript/issues/304) open until the
representation step is complete.

### 3. Separate the nullish representations

Adapt the datatype, conversion, collection, and comparison work from
[#371](https://github.com/midspiral/LemmaScript/pull/371), which includes
[#359](https://github.com/midspiral/LemmaScript/pull/359), to the established read
model. Avoid importing its old narrowing implementation wholesale.

Test the whole representation boundary: `T`, `T | undefined`, `T | null`,
`T | null | undefined`, and standalone `null`, `undefined`, and
`null | undefined`. Cover arguments, returns, assignments, collections,
comparisons, optional chaining, coalescing, and callback defaults. In
particular, converting a dynamically chosen sentinel must inspect or preserve
the value; its union type does not identify which sentinel occurred.

### 4. Reassess union lowering

Evaluate checked variant projections separately. Keep native pattern matching
where it gives clear code and useful Lean reduction behavior. A change to
optional reads does not require every union `switch` to become a chain of
constructor tests and projections.

The remaining union-callback case in
[#353](https://github.com/midspiral/LemmaScript/issues/353) belongs here unless
addressed by an earlier focused fix. Currently `lsc gen` emits invalid Dafny
and `lsc check` rejects it. That is a valid program failing verification, not
a successful false proof, and not evidence that the case has been fixed.

## What the prototype established

At `922bc4a`, #378's core tests, generated examples, and main Lean build pass.
Its [CI run](https://github.com/midspiral/LemmaScript/actions/runs/45294901928)
has 24 failing Dafny case-study jobs that stop at generated-file drift and
three failing Lean case-study jobs with proof-script errors. The Dafny jobs
have not established whether the changed proofs verify after regeneration.
The Lean failures demonstrate a migration cost that must be measured.

Local comparison also confirmed that the prototype handles the union-callback
example and rejects the generated-binder false proof described above. However,
this valid TypeScript produces a new false proof:

```ts
export function f(x: null | undefined): number | null | undefined {
  //@ ensures \result === undefined
  return x;
}
```

JavaScript returns `null` for `f(null)`. The prototype emits a body returning
constant `Undefined`, and `lsc check --backend=dafny` succeeds with
`1 verified, 0 errors`. The corresponding reproduction is rejected by Dafny
on the baseline `main`. Preserve this as a negative regression for the
representation step, paired with a correct identity contract.

This is why the prototype is evidence for a promising read model, rather than
a merge candidate or a general soundness argument. Coercion lowering itself
can change the program incorrectly.

## Pending PRs

These roles describe the proposal at the baseline above, not instructions to
close or merge PRs automatically.

| PR | Role |
|---|---|
| [#358](https://github.com/midspiral/LemmaScript/pull/358) | Extract the remaining generated-binder safety fix and tests. |
| [#367](https://github.com/midspiral/LemmaScript/pull/367) | Evaluate its checked optional-read machinery as the small foundation. |
| [#242](https://github.com/midspiral/LemmaScript/pull/242), [#345](https://github.com/midspiral/LemmaScript/pull/345), [#346](https://github.com/midspiral/LemmaScript/pull/346), [#347](https://github.com/midspiral/LemmaScript/pull/347) | Carry forward boolean-chain, loose/negated-check, loop, and reassignment regressions and required behavior into the chosen optional implementation. |
| [#378](https://github.com/midspiral/LemmaScript/pull/378) | Keep as the broad prototype; extract bounded changes and retain its counterexamples. |
| [#359](https://github.com/midspiral/LemmaScript/pull/359), [#371](https://github.com/midspiral/LemmaScript/pull/371) | Consolidate into the separate nullish representation step; #371 already contains #359. |
| [#370](https://github.com/midspiral/LemmaScript/pull/370) | Park the effect-invalidation redesign; retain useful behavioral tests. |
| [#363](https://github.com/midspiral/LemmaScript/pull/363) | Keep assignment-expression sequencing separate. #372's explicit rejection remains the baseline boundary. |

## Validation and migration

Steps 1–2 now use fresh union binders and a typed `coerce` for checked optional
reads. Optional scope substitution and statement-level `someMatch` have been
removed. Expression snapshots remain for `?.`, `??`, and spread merging;
union lowering retains its existing representation. Direct mutations through
optional storage reconstruct the enclosing value; unsupported mutation results
and optional `pop`/`shift` produce diagnostics. Both backends check non-null
assertions, including assertions on map lookups.

Local validation passes the 646 unit tests, fixture checks, compiler and
example typechecks, all 91 Dafny examples, and the full Lean build. The focused
regressions include false postconditions, reads after clearing storage, absent
map lookups, optional comparisons whose other operand must execute, skipped
calls in short-circuit expressions, and iteration after clearing the iterable's
source variable. These checks cover both successful proofs and expected proof
failures; they do not establish general translation soundness.

Generated examples were regenerated through the compiler. Dafny proof additions
were preserved; topological sort needed two merge conflicts reconciled. On Lean,
six proofs in `spec.proof.lean` now use method contracts instead of removed pure
mirrors. Topological sort uses the existing invariant lemmas with the proved
map-lookup bridge; its contracts are unchanged. The migration no longer needs
the old tactic macro and reduces its heartbeat limit from 16 million to 2 million.

Dedicated staging branches are prepared for 20 affected case-study pins, with
proof additions preserved. The ordinary Dafny verification checks pass locally;
the slow balanced-match and workflow proofs exceeded their 500s/600s limits.
Their generation and additions-only checks pass, which is also their existing
CI coverage; full proof validation remains outstanding. Pi and colorwheel's Lean
builds pass. Colorwheel retains its pre-existing `sorry` in `adjustColorCommutes`.
Case-study validation also exposed optional-chain discriminator metadata and
backend-only specification helper typing bugs, now covered by regressions. The
full CI matrix will consume the `<pinned>-redesign-narrowing` staging branches.

Each claimed fix needs a positive program with runtime results and a correct
contract that verifies, plus a false contract or invalid read that is rejected
for the expected reason. A backend syntax error, an unrelated type error, or
a timeout does not establish that a supported program was translated correctly.
An intentional source-level rejection of unsupported behavior should be tested
and documented as such.

| Area | Required evidence |
|---|---|
| Current reads and writes | Reads after local reassignment, parent replacement, and supported direct mutation observe the new value. Old-value claims fail. |
| Evaluation | Absent values do not erase other operands or their preconditions. Unselected branches do not execute lifted calls. Receivers are evaluated once. |
| Lexical scope | Existing local, loop, callback, quantifier, and generated-binder regressions remain covered. |
| Loops and specs | Presence facts, invariants, termination measures, and emitted `done_with` clauses are checked in their actual backend contexts. |
| Representations | Every admitted value survives each supported widening; narrowing has a real proof obligation. Include dynamic standalone sentinels. |
| Both backends | Run Dafny verification and Lean elaboration plus Velvet proofs. Inspecting emitted text alone is insufficient. |

After the focused tests and representative migrations pass, run the repository
checks and complete case-study CI. Classify failures as generation errors,
generated-file drift, proof failures, or deliberate unsupported-case diagnostics.
Do not infer that a red case-study job is just drift, or that drift will merge
and verify cleanly.

Prepare dedicated case-study staging branches against a fixed compiler commit.
Use `[skip ci]` in their commit messages. Regenerate Dafny through `lsc regen`,
preserve handwritten additions and recovery anchors, and verify the merged
proofs. Regenerate Lean definitions through the compiler and adapt handwritten
proofs without weakening their claims. Update the current architecture and
specification documents as each implementation step lands.

## Boundaries

Checked reads do not repair an incorrect model of shared mutable storage.
Aliasing, mutations through calls, and closures that capture changing variables
still need their own modeling or explicit rejection; see
[#267](https://github.com/midspiral/LemmaScript/issues/267). A projection from a
copied value can verify while JavaScript observes a later mutation. Keeping
source names distinct and checking presence does not establish capture semantics.

This proposal does not introduce a general heap model, whole-program effect
analysis, or assignment-expression sequencing. Keep the associated issues open
until their own reproductions are covered. Close a narrowing issue only when
the merged change covers its stated scope, or explicitly track any remaining
cases separately.
