# DESIGN_DIFF — additions-only on Dafny's canonical print

Status: implemented in `additionsOnly` (`tools/src/dafny-commands.ts`) on the
`diff-minimal` baseline.

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

1. Copy `foo.dfy.gen` to a temporary `.dfy` (Dafny only accepts that
   extension) and run `dafny resolve --print:<out>` on it and on `foo.dfy`,
   with the `--unicode-char` flag the proof header selects but **without**
   `--standard-libraries`: parsing does not need the library, and with the
   flag Dafny prints the whole library too (18k lines, 3s instead of 0.4s).
   Dafny re-prints the parsed program: comments gone, string literals intact,
   one clause per line, each declaration header on its own line, parentheses
   normalized.
2. Drop the first line of each print (a filename comment) and normalize two
   things the printer does not keep line-stable. Join any multi-line verbatim
   string `@"…"` onto one line: Dafny prints such a literal as written, so
   generated lines wrapped in one would otherwise still appear as present; it
   is the only token that can span lines once comments are gone, so a
   string-literal scan (not a lexer) suffices. Split a loop header's trailing
   `{` onto its own line: the printer writes `while c {` for a loop without
   clauses and `while c` / `invariant …` / `{` once the proof adds invariants,
   which would make every generated loop header look modified. Then run the
   **existing** `git diff --no-index --minimal` check on the two outputs. Any
   `-` line fails, exactly as today.
3. Nothing else. In particular no rule about *which* clauses may be added:
   `modifies this` / `reads this` are proof-level additions by design
   (SPEC.md §2.8), and proofs add preconditions over proof-only predicates to
   generated declarations (`examples/preorder`, `requires ValidNode(root)`).
   Such additions weaken what is proved, but they are visible in the line
   diff, which is what this check is for; the sibling benchmark forbids them
   and that is the right call for a benchmark, not for the tool.

Measured on the scratch reproductions: the commented-out `requires` becomes a
deleted printed line; the `|| true` becomes a modified printed line; an
inserted `{:verify false}` or `{:axiom}` in front of a generated declaration
modifies its printed header. All three fail with no rule specific to them.
The first CI run over the case studies found the loop-header issue above and
nothing else: every other proof printed line-stably.

### The `.dfy.gen` need not resolve

A generated file may name a predicate or function whose definition exists
only in the proof file, so `dafny resolve` on it reports unresolved
identifiers. That is fine: Dafny writes the `--print` output after
**parsing**, before resolution (checked on 4.11: resolution errors still
produce a complete print; a parse error produces none). The check therefore
ignores the exit status and requires only that both print files exist. A
`.dfy` that does not parse is an error (it would fail verification anyway).

One generated form is not Dafny on its own: a `//@ pure` function whose body
cannot auto-convert is emitted as `function f(...) { } by method { ... }` with
an **empty** functional body for the proof to supply (`examples/countBadPairs`,
several functions in a case study). When the generated copy fails to parse,
the check rebuilds it from the full-context source diff, splicing the proof's
lines into each such body; those lines are proof-authored, so comparing
against them hides nothing, and the print pass then runs as usual. Only a
generated file that still fails to parse after that falls back to the
source-line result, with a warning naming the file. The same fallback applies
when `dafny` is not on `PATH` (`lsc gen-check` without a verifier).

## Reporting

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

In `tools/tests/dafny-commands.test.ts`, skipped without a `dafny` on PATH:
block comment around a clause, verbatim string, `|| true` continuation, and
`@Verify(false)` before a generated declaration are rejected; a proof with
block comments, an `assert` with a string containing `//`, a new `{:axiom}`
lemma, an `ensures` and a `requires` added to a generated function, loop
invariants added to a generated `while`, a `.dfy.gen` that references a
proof-only predicate, and the non-parsing and no-`dafny` fallbacks pass. The acceptance test
for switching is that every example and case-study proof still passes; a
rejection there is either a real finding or a rule to relax.

## Non-goals

Proving that additions are *proof-only* (no executable effect inside method
bodies) needs a parser and is deferred. Lean is out of scope: its proof lives
in separate files and has no additions-only invariant.
