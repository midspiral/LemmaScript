# Getting Started — Dafny Backend

A practical walkthrough for verifying a piece of an existing TypeScript codebase with LemmaScript's Dafny backend.

For the annotation language, see [SPEC.md](SPEC.md). For backend-specific behavior, [SPEC_DAFNY.md](SPEC_DAFNY.md). For agent-specific gotchas, [AGENTS.md](AGENTS.md).

## Prerequisites

- **Node.js >= 18**
- **Dafny >= 4.x** ([install](https://github.com/dafny-lang/dafny))
- **git**

## Directory layout

Clone LemmaScript and your target project as **siblings** under a shared parent directory. To get a working verified example, clone [midspiral/hono-lemmascript](https://github.com/midspiral/hono-lemmascript/) — it already has annotations, generated Dafny, proofs, and CI in place.

```
~/code/
  LemmaScript/                  ← this repo
  hono-lemmascript/             ← worked example
```

The sibling layout matters because the toolchain is invoked from inside the project as `npx tsx ../LemmaScript/tools/src/lsc.ts ...` (running from source — fixes apply immediately, no publish step), and because an AI coding agent should be started in the **parent directory** so it can read and edit both trees. You will hit cases where the cleanest fix is in the toolchain rather than your annotations.

```sh
mkdir -p ~/code && cd ~/code
git clone https://github.com/midspiral/LemmaScript.git
cd LemmaScript && npm install && cd tools && npm ci && cd ../..

git clone -b lemmascript https://github.com/midspiral/hono-lemmascript.git
cd hono-lemmascript
```

Run `../LemmaScript/tools/check.sh dafny` to reproduce the full verification, or jump straight to the edit loop on any file listed in `LemmaScript-files.txt`.

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

As soon as any function in the file has `//@ verify`, `lsc` switches to opt-in mode for that file and skips everything not marked. Types and module-level `const`s are always extracted.

For richer specs, see [SPEC.md §2](SPEC.md#2-the---annotation-language).

## The edit loop

```sh
# from inside hono-lemmascript/
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny src/utils/cookie.ts
```

This produces two files next to your TS source:

- **`cookie.dfy.gen`** — the generated Dafny. Don't edit; it gets regenerated.
- **`cookie.dfy`** — starts as a copy of `.dfy.gen`. **This is where you edit** — helper lemmas, ghost predicates, asserts, loop invariants.

The diff between `.dfy.gen` and `.dfy` must be **additions only**. `lsc check` enforces this.

```sh
dafny verify src/utils/cookie.dfy
```

When Dafny complains, the fix usually belongs either in `cookie.ts` (tighten `//@ requires`, weaken `//@ ensures`, add `//@ invariant` / `//@ decreases`) or in `cookie.dfy` (helper lemma, ghost predicate, nudging `assert`).

After editing the TS, re-run `regen` (not `gen`):

```sh
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny src/utils/cookie.ts
```

`regen` three-way-merges the new generated code into your `.dfy`, preserving every proof addition. **Never `rm cookie.dfy cookie.dfy.gen` and `gen` fresh** — you will lose all your proofs.

For tough proofs, narrow Dafny to one symbol or split conjuncts:

```sh
dafny verify --filter-symbol=isValidCookieName_ensures src/utils/cookie.dfy
dafny verify --isolate-assertions src/utils/cookie.dfy
```

## When LemmaScript itself needs work

LemmaScript is a tech preview. You will hit unsupported TS methods, missed narrowing patterns, or generated Dafny that doesn't typecheck for your particular types. The fix is usually a small change in `../LemmaScript/tools/src/` — most often `transform.ts`, `peephole.ts`, `dafny-emit.ts`, or `types.ts`. See [TOOLS.md](TOOLS.md) for the pipeline. For example, the rallly case study added `s.startsWith()`, `T | null` nullability, `\result` narrowing under `==>`, and `Math.max(...arr)` spread.

`tsx` picks up edits to LemmaScript source automatically — no `npm run build` step when invoking via `npx tsx`. Land toolchain changes in their own PR, separately from the project change.

## Working with agents

- **Start the agent in the parent directory** (`~/code/`), not the project directory.
- **Point it at [AGENTS.md](AGENTS.md).**
- **Don't use `//@ assume`.** It tells Dafny to trust an obligation unconditionally; if the agent reaches for it to silence a failure, the proof has stopped meaning anything. Restructure or prove a helper lemma instead.
- **Stay in-place when in-place is asked** — otherwise the agent may refactor the production code "for clarity," defeating the point.
- **Add new files to `LemmaScript-files.txt`** so `check.sh` and CI see them.

## CI

Once a function verifies, wire up CI. The pattern every case study uses:

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
      - run: cd ../LemmaScript/tools && npm ci

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

`tools/check.sh` reads `LemmaScript-files.txt` — one verified file per line, optionally followed by a Dafny timeout and extra flags:

```
src/utils/cookie.ts
src/middleware/ip-restriction/verified.ts 120
src/utils/ipaddr.verified.ts 30 --isolate-assertions
```

To add your project to LemmaScript's own case-study matrix, open a PR adding an entry to `.github/workflows/ci.yml`.

## Where to go next

- [SPEC.md](SPEC.md) — annotation language and translation rules.
- [SPEC_DAFNY.md](SPEC_DAFNY.md) — Dafny-specific behavior.
- [AGENTS.md](AGENTS.md) — gotchas before turning an agent loose.
- [examples/](examples) — small, complete LemmaScript files.
- [README.md](README.md) — the case-study list.
