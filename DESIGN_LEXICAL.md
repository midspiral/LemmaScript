# DESIGN_LEXICAL — Preserving lexical bindings through lowering

Implemented in [PR #364](https://github.com/midspiral/LemmaScript/pull/364).

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

## The scheme

Before extracting a function or method, [LexicalNames](tools/src/lexical-names.ts)
assigns names by **TypeScript symbol identity**, without modifying the AST.
Only conflicting locals whose scopes may overlap after lowering are renamed;
parameters and unambiguous locals keep their spelling.

Enclosing declarations get first choice of names. Renames use `_2`, `_3`, …,
skipping names found in source or annotations, and reserve the result against
later compiler-generated names. References follow their declaration's mapping,
including assignment targets and shorthand-property values: `{ p }` becomes
`{ p: p_2 }`, preserving the field key.

Raw IR carries these names as strings. Resolve looks them up in a linked chain
of `{ name, ty, parent }` bindings, taking the nearest match. These environments
handle scopes that remain in the IR; extraction's renaming protects bindings
whose scopes are removed or extended. Neither mechanism replaces the other.

## Annotations and captures

Annotation references are resolved at their original source location. The
[spec parser](tools/src/specparser.ts) rewrites only free variable references,
preserving strings, field names, record keys, and quantifier-bound variables.
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
