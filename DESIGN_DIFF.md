# DESIGN_DIFF — additions-only on Dafny's canonical print

Status: proposal. Targets `additionsOnly` in `tools/src/dafny-commands.ts` on
the `diff-minimal` baseline.

## Problem

The additions-only invariant says a `.dfy` is its `.dfy.gen` plus proof text.
It is checked on **source lines**: `git diff --no-index --minimal` must show
no `-` lines. But Dafny's meaning is carried by tokens, and a line can change
the meaning of other lines without touching them:

```dafny
/*                      // added
  requires (x >= 2)     // generated, unchanged, now a comment
*/                      // added
```

`lsc check` accepts this and Dafny verifies a caller that passes `0`. A
verbatim string `@"` … `";` hides generated text the same way, and an added
`|| true` after a generated `ensures (p)` continues the expression. Nothing is
deleted at the line level, yet the theorem being proved is not the generated
one. The line check has always implicitly assumed that lines are
self-contained; the fix is to make them so before diffing.

## Design

Diff the files **as Dafny prints them**, not as the author wrote them.

1. Copy `foo.dfy.gen` to a temporary `foo.gen.dfy` (Dafny only accepts the
   `.dfy` extension) and run `dafny resolve --print:<out>` on it and on
   `foo.dfy`, with the flags `dafnyVerify` would use. Dafny re-prints the
   parsed program: comments gone, string literals intact, one clause per line,
   each declaration header on its own line, parentheses normalized.
2. Drop the first line of each print (a filename comment) and run the
   **existing** `git diff --no-index --minimal` check on the two outputs. Any
   `-` line fails, exactly as today.
3. One new rule, trivial on canonical text: an added `requires`, `reads`, or
   `modifies` line whose nearest preceding declaration header is an
   *unchanged* line is rejected. Those clauses weaken a generated theorem; the
   route for a domain restriction is `//@ requires` in the TypeScript. Added
   `ensures`, `decreases`, and `invariant` lines are fine (more to prove), as
   are axioms and `ensures` on externs, which are how out-of-model code is
   imported.

Measured on the scratch reproductions: the commented-out `requires` becomes a
deleted printed line; the `|| true` becomes a modified printed line; an
inserted `{:verify false}` or `{:axiom}` in front of a generated declaration
modifies its printed header. All three fail with no rule specific to them.

### The `.dfy.gen` need not resolve

A generated file may name a predicate or function whose definition exists
only in the proof file, so `dafny resolve` on it reports unresolved
identifiers. That is fine: Dafny writes the `--print` output after
**parsing**, before resolution (checked on 4.11: resolution errors still
produce a complete print; a parse error produces none). The check therefore
ignores the exit status and requires only that both print files exist. A
`.dfy.gen` that does not parse is an emitter bug, reported as such; a `.dfy`
that does not parse would fail verification anyway.

### Reporting

The source-level diff stays as the reporting layer. When the printed diff
fails, the message shows the printed text that was lost or altered, so the
author can find the comment, string, or continuation responsible:

```
ERROR: needs.dfy: generated text is hidden or altered (not additions-only):
  -  requires x >= 2
  Look for a block comment, verbatim string, or expression continuation around it.
```

## Cost and caching

One extra `dafny resolve` per file, about 3 seconds on the largest example.
The `.dfy.gen` print can be cached beside the run log under its content hash;
the `.dfy` print cannot, but `lsc check` is about to spend far longer
verifying it. Both prints must come from the Dafny binary that verifies, so
printer differences between versions never cross a comparison.

`regen` is unaffected: its three-way merge stays on source lines, and the
check runs on its output as it does today. The `// lsc options` header
comparison stays on source as well, since the print drops comments.

## Testing

Fixtures under `tools/fixtures/additions/`, each asserting the reason: block
comment around a clause, verbatim string, `|| true` continuation, `(0)` call
continuation, `requires false` on a generated declaration, `{:verify false}`
before a generated declaration. Positive fixtures: a proof with block
comments, an `assert` with a string containing `//`, a new `{:axiom}` lemma,
an `ensures` added to a generated function, a `.dfy.gen` that references a
proof-only predicate, and every tracked example `.dfy`. The acceptance test
for switching is that every example and case-study proof still passes; a
rejection there is either a real finding or a rule to relax.

## Non-goals

Proving that additions are *proof-only* (no executable effect inside method
bodies) needs a parser and is deferred. Lean is out of scope: its proof lives
in separate files and has no additions-only invariant.
