# Getting Started — Dafny Backend

A practical walkthrough for verifying a piece of an existing TypeScript codebase with LemmaScript's Dafny backend. This is the path most case studies have followed (e.g., [hono-lemmascript](https://github.com/midspiral/hono-lemmascript/), [opencode-lemmascript](https://github.com/midspiral/opencode-lemmascript/)).

For the annotation language and what each `//@ ` keyword does, see [SPEC.md](SPEC.md). For backend-specific behavior, [SPEC_DAFNY.md](SPEC_DAFNY.md). For agent-specific gotchas, [AGENTS.md](AGENTS.md).

## Prerequisites

- **Node.js >= 18**
- **Dafny >= 4.x** ([install](https://github.com/dafny-lang/dafny))
- **git**

## Directory layout

Clone LemmaScript and your target project as **siblings** under a shared parent directory. To get a working verified example to learn from, clone [midspiral/hono-lemmascript](https://github.com/midspiral/hono-lemmascript/) — it already has the annotations, generated Dafny, proof additions, and CI in place:

```
~/code/
  LemmaScript/                  ← this repo
  hono-lemmascript/             ← worked example: hono with LemmaScript verification
```

Why siblings? Two reasons:

1. The toolchain is invoked from inside the project as `npx tsx ../LemmaScript/tools/src/lsc.ts ...`. Running from source (not the published npm package) lets you take a fix in LemmaScript and immediately re-run verification — no publish step.
2. If you use an AI coding agent (Claude Code, Codex, Cursor, etc.), start it in the **parent directory** (`~/code/` in the example above), not inside the project. That way the agent can read and edit both the project and LemmaScript itself. You will hit cases where the cleanest fix is in the toolchain rather than in your annotations, and you want the agent to be able to make that fix.

```sh
mkdir -p ~/code && cd ~/code
git clone https://github.com/midspiral/LemmaScript.git
cd LemmaScript && npm install && cd tools && npm ci && cd ../..

# Worked example — hono with verified middleware
git clone -b lemmascript https://github.com/midspiral/hono-lemmascript.git
cd hono-lemmascript
```

From here you can run `../LemmaScript/tools/check.sh dafny` to reproduce the full verification, or jump straight to the edit loop below on any file listed in `LemmaScript-files.txt`.

## Pick something to verify

In a brownfield codebase, pick small, pure functions first — string helpers, predicates, parsers without I/O, small algorithms. Add `//@ verify` to opt them in:

```typescript
// src/utils/cookie.ts
export function isValidCookieName(name: string): boolean {
  //@ verify
  //@ ensures \result === true ==> name.length > 0
  if (!name || name.length === 0) return false;
  // ...
}
```

As soon as any function in the file has `//@ verify`, `lsc` switches to opt-in mode for that file and skips everything not marked. Type declarations and module-level `const`s are always extracted.

For richer specs (preconditions, postconditions, ghost variables, assertions, invariants), see [SPEC.md §2](SPEC.md#2-the---annotation-language).

## The edit loop

```sh
# from inside hono-lemmascript/
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny src/utils/cookie.ts
```

This produces two files next to your TS source:

- **`cookie.dfy.gen`** — the generated Dafny. Don't edit this; it gets regenerated.
- **`cookie.dfy`** — starts as a copy of `.dfy.gen`. **This is where you edit.** Helper lemmas, ghost predicates, assert statements, loop invariants, and proof scaffolding all go here.

The diff between `.dfy.gen` and `.dfy` must be **additions only**. `lsc check` enforces this.

Verify the result:

```sh
dafny verify src/utils/cookie.dfy
```

Iterate: when Dafny complains, decide whether the fix belongs in:

- **`cookie.ts`** — strengthen `//@ requires` to rule out the bad input, weaken `//@ ensures` to match what the code actually proves, or add `//@ invariant`/`//@ decreases` to a loop.
- **`cookie.dfy`** — add a helper lemma, an inductive ghost predicate, an `assert` that nudges the solver, or a loop invariant the generator can't infer.

After editing the TS, re-run `regen` (not `gen`):

```sh
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny src/utils/cookie.ts
```

`regen` three-way-merges the new generated code into your `.dfy`, preserving every proof addition. **Never `rm cookie.dfy cookie.dfy.gen` and `gen` fresh** — you will lose all your proofs.

For single-lemma iteration during a tough proof, narrow Dafny down to one symbol:

```sh
dafny verify --filter-symbol=isValidCookieName_ensures src/utils/cookie.dfy
```

For lemmas with many conjuncts, `--isolate-assertions` shows which conjunct is failing.

## When LemmaScript itself needs work

LemmaScript is a tech preview. You **will** hit cases where:

- A TS method (`Math.hypot`, `Array.from`, regex, etc.) isn't in the supported fragment.
- A generated Dafny construct doesn't typecheck for your particular type combination.
- An optional-narrowing or discriminated-union pattern you expect to be detected isn't.

The fix is usually a small change in `../LemmaScript/tools/src/` — most often `transform.ts`, `peephole.ts`, `dafny-emit.ts`, or `types.ts`. Pipeline overview in [TOOLS.md](TOOLS.md).

The hono case study, for example, surfaced operator gaps that ended up as toolchain additions. The rallly case study added `s.startsWith()`, `T | null` nullability, `\result` narrowing under `==>`, and `Math.max(...arr)` spread.

The workflow is:

1. Make the change in `LemmaScript/tools/src/`.
2. Re-run `lsc regen` from your project (`tsx` picks up the new source automatically — no `npm run build` needed when invoking via `npx tsx ../LemmaScript/tools/src/lsc.ts`).
3. Verify the project still works on its existing files (CI catches regressions).
4. PR the LemmaScript change separately from the project change.

This is exactly why the sibling layout matters — an agent active in the parent can read both trees, fix the toolchain, and re-verify in one loop.

## Working with agents

Concrete tips when running an AI coding agent on this workflow:

- **Start the agent in the parent directory** (`~/code/`), not the project directory.
- **Point it at [AGENTS.md](AGENTS.md)** — that file collects the annotation pitfalls and toolchain conventions that agents repeatedly get wrong.
- **Resist `//@ assume` shortcuts.** When verification fails, the agent should restructure the algorithm or prove a helper lemma, not silence the obligation with `//@ assume P`. The exception is constraining a `//@ havoc`'d value whose true behavior is out of model. See [AGENTS.md](AGENTS.md#annotation-pitfalls).
- **Stay in-place when in-place is asked.** If you want to verify the shipping function byte-for-byte, tell the agent so — otherwise it may helpfully refactor the production code for clarity, defeating the point.
- **Maintain a list of files in `LemmaScript-files.txt`** (see [CI](#ci) below). Both the agent and CI use this as the source of truth for what's currently verified.

## CI

Once one or two functions verify, wire up CI. The pattern every case study uses:

```yaml
# .github/workflows/lemmascript.yml
name: Dafny

on:
  push: { branches: [main] }
  pull_request: { branches: [main] }

jobs:
  dafny:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }

      - name: Clone LemmaScript
        run: git clone https://github.com/midspiral/LemmaScript.git ../LemmaScript

      - name: Install LemmaScript tools
        run: cd ../LemmaScript/tools && npm ci

      - uses: actions/setup-dotnet@v4
        with: { dotnet-version: '8.0.x' }
      - uses: dafny-lang/setup-dafny-action@v1
        with: { dafny-version: '4.11.0' }

      - name: Regenerate and verify
        run: ../LemmaScript/tools/check.sh dafny

      - name: Check generated files are up to date
        run: |
          git diff --exit-code -- '*.dfy.gen' '*.dfy'
          untracked=$(git ls-files --others --exclude-standard -- '*.dfy.gen')
          if [ -n "$untracked" ]; then
            echo "ERROR: Untracked .dfy.gen files:"; echo "$untracked"; exit 1
          fi
```

`tools/check.sh` reads `LemmaScript-files.txt` from the project root — one verified file per line, optionally followed by a per-file Dafny timeout and extra flags:

```
src/utils/cookie.ts
src/middleware/ip-restriction/verified.ts 120
src/utils/ipaddr.verified.ts 30 --isolate-assertions
```

The `git diff --exit-code` step catches two failure modes: a proof that drifts out of sync with regenerated code, and a freshly-verified file whose `.dfy.gen` was forgotten in the commit.

To wire your project into LemmaScript's own case-study matrix, open a PR adding an entry to `.github/workflows/ci.yml`'s `case-studies-dafny` matrix.

## Where to go next

- [SPEC.md](SPEC.md) — the annotation language and translation rules.
- [SPEC_DAFNY.md](SPEC_DAFNY.md) — Dafny-specific behavior (regen, helper preambles, `function by method`).
- [AGENTS.md](AGENTS.md) — gotchas worth absorbing before turning an agent loose.
- [examples/](examples) — small, complete LemmaScript files to read.
- [README.md](README.md) — the case-study list, with one-line summaries of what each one proves.
