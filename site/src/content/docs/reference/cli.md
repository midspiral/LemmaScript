---
title: "CLI reference (lsc)"
description: "Every lsc command, flag, and file convention — gen, check, regen, extract, info, claimcheck, and batch mode."
---

<!-- Hand-written manual page (not synced from repo root). Source of truth for
     behavior: tools/src/lsc.ts — re-verify against it when the CLI changes. -->

The `lsc` command drives the whole toolchain. Install it globally
(`npm install -g lemmascript`) or run it from a source checkout with
`npx tsx tools/src/lsc.ts`.

```sh
lsc <gen|gen-check|check|regen|extract|info> [--backend=lean|dafny] [flags] <file.ts>
lsc <gen|gen-check|check> [--backend=…] [--slow]        # no file: batch over LemmaScript-files.txt
lsc claimcheck [<file.ts>] [flags…]                     # forwards to lemmascript-claimcheck
```

All flags use the `--flag=value` form. Space-separated flags (`--backend lean`) and
unknown flags are rejected with an error rather than silently ignored. Every command
exits `0` on success and `1` on any failure.

## Commands

| Command | What it does |
|---|---|
| `lsc gen <file.ts>` | Generate backend code next to the source file |
| `lsc gen-check <file.ts>` | `gen`, then verify the hand-edited file is additions-only vs. the generated one (Dafny) |
| `lsc check <file.ts>` | `gen` + additions-only check + run the prover — the full loop |
| `lsc regen <file.ts>` | Regenerate after a TS edit, three-way-merging to preserve proof additions (Dafny) |
| `lsc extract <file.ts>` | Dump the Raw IR as JSON to stdout (backend-neutral) |
| `lsc info <file.ts>` | Write `<file>.ts.json`, a per-function spec summary (backend-neutral) |
| `lsc claimcheck [<file.ts>]` | Check each function's plain-English `//@ contract` against its formal clauses |

### `lsc gen`

Generates the backend files next to your TypeScript source.

- **Dafny** (`--backend=dafny`, the default): writes `<name>.dfy.gen` (always
  regeneratable — never edit) and, on first run, `<name>.dfy` (the file you and your
  proofs own; starts as a copy of `.dfy.gen`).
- **Lean** (`--backend=lean`): writes `<name>.types.lean` (when the module declares
  types) and `<name>.def.lean`.

### `lsc check`

The whole loop for one file: generate, confirm the diff between `<name>.dfy` and
`<name>.dfy.gen` is **additions-only**, then run the prover (`dafny verify`, or
`lake build` for Lean). Passes only when every contract holds.

```sh
lsc check --backend=dafny src/domain.ts
lsc check --backend=dafny --time-limit=120 src/domain.ts
lsc check --backend=dafny --extra-flags="--isolate-assertions" src/domain.ts
```

### `lsc regen`

After editing the TypeScript, regenerate **without losing proof work**: the new
generated code is three-way-merged into `<name>.dfy` (using `<name>.dfy.base`),
preserving your helper lemmas, ghost predicates, and asserts, then re-verified.

Never delete `<name>.dfy` and `gen` fresh — you'd lose every proof addition.
`regen` is the safe path. Use `--no-verify` to run only the merge and
additions-only check, skipping the prover (CI uses this when a separate `check`
pass does the verifying).

### `lsc extract` and `lsc info`

Backend-neutral: they run regardless of any `//@ backend` directive.

- `extract` prints the structured Raw IR as JSON — the supported way for external
  tools to consume LemmaScript's frontend instead of re-parsing TypeScript.
- `info` writes `<file>.ts.json`: each function's signature plus its `requires` /
  `ensures` / `decreases` clauses. Tools like `lemmascript-seal` build on this.

### `lsc claimcheck`

Forwards to the bundled `lemmascript-claimcheck` CLI, which cross-examines the
plain-English `//@ contract` line against the formal clauses. With a file, it checks
that file (extra flags pass through verbatim); with no file, it runs once per entry
in `LemmaScript-files.txt`.

## Batch mode

Run `gen`, `gen-check`, or `check` with **no file argument** to batch over
`LemmaScript-files.txt` in the current directory — one entry per line:

```
src/domain.ts
src/allocate.ts 120
src/scanner.ts 300 --isolate-assertions
```

Format: `filepath [timeout_in_seconds] [extra prover flags…]`. Batching is
fail-fast — the first failing entry stops the run.

One safeguard: in a `check` batch (Dafny), entries whose timeout exceeds **60
seconds** are downgraded to `gen-check` (generation + additions-only, no proving) so
routine runs stay fast. Pass `--slow` to verify every entry with its full timeout.

## Flags

| Flag | Applies to | Meaning |
|---|---|---|
| `--backend=dafny\|lean` | all except extract/info | Backend to target. Default: `dafny` |
| `--time-limit=<seconds>` | check, regen | Prover time limit (positive integer) |
| `--extra-flags="…"` | check, regen | Extra flags passed to the prover verbatim |
| `--slow` | batch `check` | Verify long-timeout entries instead of downgrading them |
| `--no-verify` | regen | Merge + additions-only check only; skip the prover |

## In-file directives the CLI honors

| Directive | Effect |
|---|---|
| `//@ backend <dafny\|lean>` | The file belongs to one backend; commands for the other backend skip it (`extract`/`info` always run) |
| `//@ safe-slice` | File-level option consumed by the Dafny emitter |
| `//@ lean-module <name>` | Overrides the Lean module base name (Lean module names are global; this prevents collisions between identically-named files) |

## Project resolution

`lsc` resolves imports using the **nearest `tsconfig.json`** above the source file;
without one it falls back to strict ESNext defaults. From a source checkout, the
equivalent of `lsc` is `npx tsx <checkout>/tools/src/lsc.ts` — no build step needed.

## Next

- [Installation](/installation/) — get `lsc` on your PATH
- [Supported TypeScript subset](/subset/) — what the toolchain can express
- [Full specification](/spec/) — precise semantics of the annotation language
