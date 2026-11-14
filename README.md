# LemmaScript (Tech Preview)

A verification toolchain for TypeScript. Write ordinary TypeScript with `//@ ` specification annotations. The toolchain generates verifiable code from your TypeScript — either in Dafny or Lean 4 (with Velvet 2).

See [SPEC.md](SPEC.md), [DESIGN.md](DESIGN.md), and [GETTING_STARTED.md](GETTING_STARTED.md).

For changes to LemmaScript itself, see [CONTRIBUTING.md](CONTRIBUTING.md).

This is a **Tech Preview**: the core idea is there, but support, semantics, and ergonomics are still evolving.

See our [blog post](https://midspiral.com/blog/lemmascript-a-verification-toolchain-for-typescript/).

## Examples and Case Studies

See the [examples](examples) and [case studies](CASE_STUDIES.md) for verified TypeScript programs, libraries, and apps.

## Setup

**Prerequisites:** Node.js >= 18. For the Lean backend: [elan](https://github.com/leanprover/elan). For the Dafny backend: [Dafny](https://github.com/dafny-lang/dafny) >= 4.x.

**Install from npm:**

```sh
npm install -g lemmascript
```

**Or from source:**

```sh
git clone https://github.com/midspiral/LemmaScript.git
cd LemmaScript && npm install && npm run build
```

**Lean backend:** from the LemmaScript source checkout, clone Velvet 2 as a sibling on the **`lemma2` branch**:

```sh
git clone --branch lemma2 https://github.com/namin/velvet.git ../velvet
lake build
```

For an existing Velvet checkout, select the branch with:

```sh
git -C ../velvet fetch origin
git -C ../velvet checkout lemma2
```

The `lemma` branch is for the previous Velvet version. Use the Lean version pinned in `lean-toolchain` (currently 4.34.0); Lake resolves the Mathlib dependency. Velvet 2 does not require a Loom checkout or external Z3/cvc5 binaries. See [SPEC_LEAN.md](SPEC_LEAN.md) for the project layout and proof workflow.

## Usage

### Dafny backend

```sh
lsc gen --backend=dafny src/myModule.ts
lsc check --backend=dafny src/myModule.ts
lsc regen --backend=dafny src/myModule.ts
```

With no file argument, `lsc check` batches over `LemmaScript-files.txt` (one `filepath [timeout] [extra dafny flags…]` per line — the list `tools/check.sh` runs in CI).

From a sibling source checkout, the equivalent of `lsc` is `npx tsx ../LemmaScript/tools/src/lsc.ts` — no build step, toolchain edits apply immediately.

The Dafny backend generates two files per TS source: `foo.dfy.gen` (always regeneratable) and `foo.dfy` (source of truth, with LLM/user proof additions). The diff between them must be additions-only.

### Lean backend

```sh
lsc gen --backend=lean src/myModule.ts
lake build
```

## Sub-packages

### Claimcheck

`lsc claimcheck` forwards to [lemmascript-claimcheck](https://github.com/midspiral/lemmascript-claimcheck) to sanity check the natural language `//@ contract` against the formal specifications.

### Runtime precondition checks

`lsc guard` forwards to [lemmascript-guard](https://github.com/midspiral/lemmascript-guard) to generate a sibling `*.guarded.ts` module that checks `//@ requires` at runtime. Import its wrappers at application boundaries.

## Continuous Integration

LemmaScript ships a **reusable GitHub Actions workflow** that regenerates your artifacts, verifies them, and fails the build if any committed generated file is out of date. Call it from your own repo's workflow:

```yaml
# .github/workflows/lemmascript.yml
name: LemmaScript

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  verify:
    uses: midspiral/LemmaScript/.github/workflows/verify.yml@main
    with:
      backend: dafny      # dafny | lean | dafny-slow
```

The workflow installs the toolchain and (per `backend`) the Dafny or Lean stack, then runs `tools/check.sh`, which batches over a **`LemmaScript-files.txt`** at your repo root. This file is the list of sources CI verifies — you create and maintain it. One entry per line, `filepath [timeout] [extra dafny flags…]`:

```
src/domain.ts
src/patch.ts 120
src/heavy.ts 300 --isolate-assertions
```

The optional second column is a per-file timeout in seconds; anything after it is passed verbatim to Dafny. The same list drives `lsc check` locally when you run it with no file argument, so CI and your local runs verify exactly the same set. To verify additional Dafny files outside that list, add an executable `check-extra.sh` at the root and it runs automatically (Dafny backends only).

Inputs (all optional):

| Input | Default | Purpose |
|-------|---------|---------|
| `backend` | `dafny` | `dafny`, `lean`, or `dafny-slow` (isolate-assertions / long-running proofs) |
| `node-version` | `24` | Node.js version |
| `ls-ref` | `main` | LemmaScript ref to verify against |
| `typecheck` | `true` | Run `npm ci && npm run typecheck` in the calling repo first |

To verify against **both** backends, add a second job with `backend: lean`.

Examples:
- **[talktimer-lemmascript](https://github.com/midspiral/talktimer-lemmascript/blob/main/.github/workflows/lemmascript.yml)** — Dafny-only.
- **[pi-lemmascript](https://github.com/midspiral/pi-lemmascript/blob/lemmascript/.github/workflows/lemmascript.yml)** — Dafny + Lean (two jobs).

## Annotations

```typescript
//@ requires arr.length > 0
//@ ensures \result >= -1 && \result < arr.length
//@ invariant 0 <= i && i <= arr.length
//@ decreases arr.length - i
//@ type i nat
```

For the full surface, see [SPEC.md](SPEC.md).

## File Structure

### Dafny backend

| File | Generated? | Purpose |
|------|-----------|---------|
| [**.ts**](examples/majority.ts) | — | TypeScript source with `//@ ` annotations |
| [**.dfy.gen**](examples/majority.dfy.gen) | Yes | Generated Dafny (merge base, always regeneratable) |
| [**.dfy**](examples/majority.dfy) | Yes (initial) | Annotated Dafny (gen + proof additions) |

### Lean backend

| File | Generated? | Purpose |
|------|-----------|---------|
| [**.ts**](examples/majority.ts) | — | TypeScript source with `//@ ` annotations |
| [**.types.lean**](examples/majority.types.lean) | Yes | Lean types, `namespace Pure` defs |
| [**.spec.lean**](examples/majority.spec.lean) | No | Ghost definitions, helper lemmas |
| [**.def.lean**](examples/majority.def.lean) | Yes | Velvet method definitions |
| [**.proof.lean**](examples/majority.proof.lean) | No | `prove_correct` with proof tactics |

