# Hybrid Spec Parser

LemmaScript specification clauses are a small language embedded in `//@`
comments. Their expression syntax is deliberately close to TypeScript, but it
is not exactly TypeScript:

```typescript
//@ ensures n >= 0 ==> $result >= 0
//@ ensures forall((k: nat) => k < n ==> xs[k] > 0)
//@ ensures empty <==> xs.length === 0
```

TypeScript supplies the expression parser. LemmaScript adds the logical infix
operators `==>` and `<==>`, recognizes quantifiers, and converts the supported
TypeScript AST into `RawExpr`. The implementation is in
[`tools/src/specparser.ts`](tools/src/specparser.ts), and it runs during
resolution rather than extraction or backend emission.

This document describes that hybrid boundary. [`SPEC.md`](SPEC.md) remains the
user-facing definition of the annotation language.

## Why the parser is hybrid

Using TypeScript's parser gives specifications the same handling of literals,
parentheses, calls, property and element access, conditionals, and ordinary
operator precedence as program expressions. In particular, fixes and edge
cases such as decimal literals, numeric separators, escaped strings, and nested
expressions do not need a second lexer and expression grammar.

Two useful logical operators are not legal TypeScript:

- `P ==> Q` means implication.
- `P <==> Q` means equivalence.

An earlier pure-TypeScript prototype represented these as calls. That removed
the lexical extension, but expressions such as `implies(P, Q)` were noticeably
harder to read, especially when nested. The current design keeps the infix
notation while delegating the rest of expression parsing to TypeScript.

This is therefore not a general-purpose custom parser, but neither is it a
promise that every TypeScript expression is a valid specification. The AST
converter is an explicit allowlist for LemmaScript's pure expression subset.

## Surface syntax and precedence

Quantifiers use TypeScript arrow syntax so the binder and its scope are
visible:

```typescript
forall(k => predicate)
forall((k: nat) => predicate)
exists(k => predicate)
exists((k: nat) => predicate)
```

The untyped form is inferred later by the resolver and otherwise defaults to
`int`. `$result` is recognized as the reserved return-value expression.

The low-precedence operators are, from loosest to tightest:

| Precedence | Syntax | Associativity |
| --- | --- | --- |
| 1 | `<==>` | right |
| 2 | `==>` | right |
| 3 | `condition ? then : else` | TypeScript conditional structure |
| 4 | `||` | left |

All other supported TypeScript operators bind more tightly and retain the
grouping assigned by TypeScript. For example:

```text
a && b ==> c || d       means (a && b) ==> (c || d)
a ==> b ==> c           means a ==> (b ==> c)
a ==> b <==> c          means (a ==> b) <==> c
a <==> b ==> c          means a <==> (b ==> c)
a ==> b ? c : d         means a ==> (b ? c : d)
```

Conditional branches behave like TypeScript assignment-expression positions,
so a logical operator may occur inside either branch:

```text
a ? b ==> c : d         means a ? (b ==> c) : d
a ? b : c ==> d         means a ? b : (c ==> d)
(a ? b : c) ==> d       means (a ? b : c) ==> d
```

Parentheses are always hard grouping boundaries. Use them when a mixture of a
conditional and a logical operator could be read more than one way.

## Parsing pipeline

`parseExpr` performs five steps:

1. Scan the original annotation with TypeScript's scanner and locate `==>` and
   `<==>` outside strings and comments.
2. Replace each extension operator with a same-length `||` placeholder and
   remember its original spelling and source offset.
3. Parse the masked expression as the initializer in
   `const __spec = (<expression>);` using TypeScript's parser.
4. Rebuild the affected low-precedence operator spine so the custom operators,
   conditionals, and real `||` expressions have LemmaScript's precedence.
5. Convert the resulting expression to `RawExpr`, rejecting syntax outside the
   supported subset.

The parser records every masked operator and checks that conversion consumed
all of them. A custom operator must never disappear silently into the
TypeScript AST.

## Scanning and masking

The extension operators are recognized as adjacent TypeScript scanner tokens,
not by a regular expression over source text:

```text
==>    EqualsEqualsToken + GreaterThanToken
<==>   LessThanEqualsToken + EqualsGreaterThanToken
```

The component tokens must be contiguous. Consequently, operator-looking text
inside a string or comment is left alone, and `== >` is not treated as `==>`.

Each operator is masked as `||` followed by spaces:

```text
"==>"    becomes "|| "
"<==>"   becomes "||   "
```

The replacement has exactly the same number of UTF-16 code units as the
original. TypeScript scanner positions are UTF-16 offsets, so the
implementation intentionally edits `input.split("")` rather than iterating by
Unicode code point. Keeping offsets stable is an invariant: the operator map
uses those offsets to distinguish a real `||` from a placeholder, including in
expressions containing astral characters such as emoji.

## Restoring the operator spine

Masking lets TypeScript parse the complete surrounding expression, but every
placeholder initially has `||` precedence. That AST cannot be converted
directly. For example, TypeScript would group the masked form of
`a ==> b || c` according to two `||` operators, losing the fact that implication
binds less tightly.

`flattenOperatorSpine` therefore flattens only nodes whose grouping may have
been affected:

- masked `==>` and `<==>` nodes,
- genuine `||` nodes, and
- conditional expressions.

Parenthesized expressions remain atoms. Every tighter TypeScript expression
also remains an atom, preserving TypeScript's authoritative grouping for
arithmetic, comparisons, equality, `&&`, calls, and access expressions.

`convertOperatorExpression` rebuilds the flattened sequence with a small
precedence-climbing parser. This is the only custom expression-precedence logic
in the production parser.

## AST conversion boundary

The converter accepts the pure constructs represented by `RawExpr`, including:

- identifiers, `this`, `$result`, booleans, strings, numbers, bigints, and the
  nullish value used by the model;
- property access, element access, and ordinary calls;
- supported unary and binary operators and conditional expressions;
- array and record literals;
- empty `new Set<T>()` and `new Map<K, V>()` expressions; and
- expression-bodied arrows used as the sole argument of `forall` or `exists`.

It rejects unsupported TypeScript constructs explicitly, including optional
access and calls, spreads, generic calls, arbitrary arrow functions, and
unsupported constructors. Loose equality is normalized in Raw IR (`==` to
`===`, and `!=` to `!==`). Type checking, binder inference, contextual rules
such as where `$result` is legal, and backend restrictions happen later in the
resolver and emitters.

`implies(...)` and `iff(...)` have no parser-level special meaning. They are
ordinary calls; the supported logical syntax is the infix form.

## Diagnostics

There are two classes of parser error:

- TypeScript parse diagnostics for malformed expression structure.
- LemmaScript diagnostics from the AST allowlist or hybrid operator pass.

At present `parseExpr` receives only the annotation text. An error therefore
includes the offending spec but not its source filename, annotation line,
function, or directive, and TypeScript's message may be terse:

```text
Invalid spec expression: ',' expected.
  in spec: forall(k, predicate)
```

This is a known diagnostic limitation, not a source-mapping limitation. The
same-length mask preserves offsets, and TypeScript diagnostics carry source
positions. A future diagnostic layer can add a caret and have the annotation
caller attach file and line context without changing the parsing strategy.

## Migrating 0.5 specifications

The production parser intentionally contains no compatibility grammar. The
standalone migration tool parses old annotations with the frozen 0.5 parser and
prints the current hybrid syntax directly:

```sh
node tools/migrate-0.5-specs.mjs --check .
node tools/migrate-0.5-specs.mjs .
```

Among other changes, it rewrites `\result` to `$result` and comma-style
quantifiers such as `forall(k: nat, P)` to `forall((k: nat) => P)`, while
retaining `==>` and `<==>`. It does not target the short-lived
`implies(...)`/`iff(...)` prototype syntax. See [`TOOLS.md`](TOOLS.md) for the
case-study workflow.

## Maintenance rules

Changes to this parser should preserve these boundaries:

1. Let TypeScript parse all syntax it already understands; do not duplicate
   literal, call, access, or tighter operator parsing.
2. Recognize extensions with scanner tokens, not raw substring replacement.
3. Preserve UTF-16 length while masking, and key placeholder identity by exact
   source offset.
4. Flatten only the operator spine whose precedence masking disturbed.
5. Keep parentheses atomic and retain TypeScript's grouping for tighter
   expressions.
6. Reject every unsupported AST form rather than approximating its meaning.
7. When adding syntax, update the user-facing spec, migration if applicable,
   and focused parser tests together.

The focused tests are in
[`tools/test-specparser.ts`](tools/test-specparser.ts). They cover mixed
precedence, right associativity, conditional branches, parentheses,
quantifiers, decimal literals, strings containing operator spellings, UTF-16
offsets, and operators nested in call arguments. They run as part of:

```sh
./tools/test-fixtures.sh
```
