# Architecture: Narrowing

Ordinary optionals keep one storage type throughout their scope. A read that
needs the payload becomes a checked operation on the current value. Guards,
assignments, and loops retain their ordinary control flow. Union narrowing
continues to use variant matches.

See [TOOLS.md](TOOLS.md) for the pipeline and
[REDESIGN_NARROWING.md](REDESIGN_NARROWING.md) for the staged redesign and its
remaining representation and union work.

## Storage and reads

For `let x: number | undefined`, the environment always records `Option<int>`.
Assigning `5` writes `Some(5)`; assigning `undefined` writes `None`. A return or
arithmetic operation requiring a number requests a `coerce` expression:

```ts
{ kind: "coerce", expr: storageRead, ty: payloadType }
```

This operation reads storage when it executes. For example:

```ts
if (x !== undefined) {
  x = 5;
  return x;
}
```

becomes the following Dafny body:

```dafny
if x.Some? {
  x := Some(5);
  return x.value;
}
```

Dafny checks that the destructor is defined. Lean methods bind the result of
`LemmaScript.optionValue x`, whose proved Velvet specification requires
`x.isSome = true` and establishes `x = some result`. A guard before a write
does not justify a read after the write: verification uses the current state.
A non-null assertion requests the same checked read; it supplies no assumption.

Resolve selects these reads from the consuming operation's type: arithmetic,
field/index access, collection receivers, arguments, assignments, and returns.
This also works in annotations, which have no TypeScript flow checker. Lookup
initializers retain the model's optional result even when TypeScript reports a
non-optional type. Evolving locals whose storage type cannot be established
require an explicit annotation.

## Responsibilities

- **Extract** preserves source binding identity with `LexicalNames`. It retains
  explicit optional chains and coalescing, including their evaluation boundaries.
- **Resolve** preserves storage types, inserts checked payload reads, and
  converts values written into typed slots. Its `narrowedPaths` tracks union
  variants; it no longer changes optional storage types after a guard.
- **Narrow** handles union matches, array-index bounds, and the snapshots needed
  by `?.` and `??`. It does not rewrite optional `if`, early-return, or loop
  scopes into payload binders.
- **Transform** lowers checked reads and preserves conditional evaluation.
  Supported direct collection mutations reconstruct optional and record wrappers
  back to the source variable. Unsupported optional mutation forms produce a
  diagnostic instead of silently updating a temporary.
- **Emit** expresses the backend's checks. Lean annotations use `Option.get`
  with a real presence proof; dependent conditionals make guard facts available
  during elaboration. A Lean pure mirror containing checked reads, or depending
  on one, is omitted so calls run through the verified method instead.
- **Peephole** simplifies local backend expressions while preserving evaluation
  and proof obligations.

The lexical naming rules still apply to callbacks and annotations. Fresh union
pattern binders are allocated once per arm and passed to both pattern emission
and substitution; two paths with the same name hint cannot capture each other.

## Evaluation and snapshots

`&&`, `||`, `?:`, `?.`, and `??` keep lifted calls inside the selected branch.
Value-producing logical expressions preserve JavaScript falsey payloads such as
`0`, `false`, and `""`; presence alone is sufficient only for always-truthy
payload types. Discarded logical expressions become guarded statements so their
mutations still write back to storage.

An optional comparison evaluates both operands before inspecting presence. An
absent left operand cannot erase a right-hand call or its precondition.

The expression-only `someMatch` node remains for a single evaluation:

```text
x ?? y       → someMatch x { Some(v) => v, None => y }
x?.field     → someMatch x { Some(v) => v.field, None => undefined }
```

Its bodies name the snapshot explicitly. Transform never substitutes that
snapshot into later source reads. Object-spread merging also uses explicit
snapshots. There is no statement-level optional `someMatch`.

A complex expression repeated in source is evaluated repeatedly. Checking one
call result does not establish presence for a later independent call; binding
the result explicitly is the way to reuse the same evaluation.

## Union narrowing and boundaries

Discriminated unions and synthesized array unions still use `tagMatch` and
pattern-binder substitution. Conjunctions containing `Array.isArray` retain
source order, including an optional guard before the union receiver is read.
This does not replace union narrowing with checked variant projections or
resolve the separate union-reassignment and callback limitations.

The current datatype still conflates `null` and `undefined`. Aliasing, shared
mutable state, and callbacks capturing changing variables retain the existing
model's limitations. Checked optional reads are not a heap model or an effect
analysis. Assignment expressions used as values remain unsupported.

Regression tests pair runtime results and successful backend proofs with false
postconditions, absent payload reads, and calls whose preconditions must fail.
Loop invariants, decreasing clauses, and explicit `done_with` annotations are
checked against the current optional state on both relevant backend paths.
