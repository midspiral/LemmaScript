# DESIGN_LEXICAL — Preserving lexical bindings through lowering

Implemented in [PR #364](https://github.com/midspiral/LemmaScript/pull/364);
extended in [PR #377](https://github.com/midspiral/LemmaScript/pull/377)
from lost scopes to every shadowing binding afterwards.

Lowering changes block boundaries. Extraction must preserve which declaration
each reference denotes before the IR loses TypeScript's symbol information.

## The problem

```ts
//@ ensures \result === p
export function bareBlock(p: number): number {
  { const p = 5; }
  return p;
}
```

`bareBlock(3)` returns 3. Extraction flattens the bare block; keeping both names
as `p` would make the return read 5. A verifier could then prove a false contract
about the source program. The correct flattened form is `let p_2 = 5; return p;`.

Branches have the same risk when lowering moves subsequent statements into
each arm. Counting `for` loops also lose a scope when their initializer moves
before the generated `while`.

Scopes that survive lowering have a second risk. Later passes identify a
variable by its name: narrowing replaces reads of a tested path with the
branch's binder, and a union match replaces field reads with pattern binders.

```ts
if (p !== undefined) {
  for (const x of xs) { const p = x + 1; total += p; }
  return total + p;
}
```

The loop keeps its own scope in both backends, so the emitted code would be
well scoped with two `p`s. But the substitution for the narrowed outer `p`
would also rewrite the inner read, and a false contract could verify.

## The scheme

Before extracting a function or method, [LexicalNames](tools/src/lexical-names.ts)
assigns names by **TypeScript symbol identity**, without modifying the AST.
The invariant it establishes: **after extraction, no binding in a function
shadows another.** A name then denotes one variable wherever it is visible,
and later passes may match on it without tracking scopes.

A local, loop variable, or callback parameter is renamed when its name is
already bound by

- an enclosing local, or a local whose scope lowering merges with its own;
- a parameter of an enclosing function or callback;
- a declaration of the same file; or, for a scope that lowering flattens or
  extends, any name visible from outside the function, since only such a scope
  can capture a library global.

The function's own parameters are public and keep their spelling, as do
unambiguous locals. Sibling scopes that stay separate, such as two loops that
each declare `x`, do not shadow each other and are left alone.

Enclosing declarations get first choice of names. Renames use `_2`, `_3`, …,
skipping names found in source or annotations, and reserve the result against
later compiler-generated names. References follow their declaration's mapping,
including assignment targets and shorthand-property values: `{ p }` becomes
`{ p: p_2 }`, preserving the field key.

Raw IR carries these names as strings. Resolve looks them up in a linked chain
of `{ name, ty, parent }` bindings, taking the nearest match. With shadowing
gone, the nearest match is the only match among a function's bindings; the
chain still orders declarations, so a name is not visible before its binding.

The alternative is to keep source spellings and give each read the identity of
its binding, compared wherever a pass substitutes. That leaves the output
unchanged but adds a field every later pass must carry and copy onto the reads
it synthesizes. Renaming is paid once, in extraction, and only by code that
shadows: `single(n).some(n => n % 2 === 1)` emits the callback parameter as
`n_2`.

## Annotations and captures

Annotation references are resolved at their original source location. The
[spec parser](tools/src/specparser.ts) rewrites only free variable references,
preserving strings, field names, record keys, and quantifier-bound variables.
The position name `_x_idx` of a for-of variable follows a rename of `x`.

A quantified variable is not a TypeScript symbol, so extraction cannot rename
it. Resolve does: `exists(p: int, …)` where `p` is already in scope binds a
fresh name (`p'`), keeping the invariant for annotations too.
Ghost bindings have a separate scoped environment: a ghost can shadow a name
in annotations without changing runtime reads.

Arrow closures capturing a later local `let` or `const` are rejected, even if
JavaScript would initialize it before invocation. The current backend model
cannot construct a closure before its captured local exists; binding to an
outer namesake would change the program. Callback parameter defaults have a
[separate initialization model](TOOLS.md#callback-binding-and-lowering).

See [TOOLS.md](TOOLS.md#scoping) for extension rules and
[SPEC.md §4.1](SPEC.md#41-basic-statements) for the language contract.
[Regression tests](tools/tests/lexical-scopes.test.ts) check runtime results,
Dafny proofs and rejection of false contracts, and distinct emitted bindings
in both backends.
