---
title: "Installation"
description: "Install the lsc toolchain from npm and add the agent skills — or clone the source kit with everything bundled."
---

<!-- Hand-written manual page. Twin: lemmascript-landing/src/pages/install.astro —
     keep the two in lockstep when the install story changes. -->

Two ways in. Use the **package** if you're using LemmaScript; take the **kit** if
you're changing it.

## Option A — the package

The standard setup: the `lsc` toolchain from npm, plus the skills that teach your
agent to drive it.

### 1. Check the prerequisites

- **Node.js ≥ 18**
- **[Dafny ≥ 4.x](https://dafny.org/latest/Installation)** — the prover that does the checking
- **git**

```sh
node -v          # ≥ 18
dafny --version  # ≥ 4.x
```

For the optional Lean backend you'll also need **Lean 4** (managed via `elan`/`lake`).

### 2. Install the package

One global install puts `lsc` — and companions like `lsc claimcheck` — on your PATH:

```sh
npm install -g lemmascript
```

### 3. Add the skills

Mount the [lemmascript-skills](https://github.com/midspiral/lemmascript-skills) repo
at your agent's skills directory — e.g. `.claude/skills` for Claude Code. Your agent
picks them up and drives the whole loop itself: contracts, checks, iteration.

```sh
git clone https://github.com/midspiral/lemmascript-skills <your/skills/dir>
```

### 4. Check something

```sh
lsc check --backend=dafny path/to/file.ts
```

## Option B — from source: lemmascript-kit

Working on the toolchain itself, or want the tools and skills pinned together?
[lemmascript-kit](https://github.com/midspiral/lemmascript-kit) bundles the toolchain
source and the skills as git submodules — one clone, one setup script, skills
already in place at `.claude/skills/`.

```sh
git clone --recurse-submodules https://github.com/midspiral/lemmascript-kit.git
cd lemmascript-kit
./setup.sh
```

Run the same commands straight out of the source tree (the skills write the CLI as
`npx lsc`; in the kit, substitute this form or `npm link` the package):

```sh
npx tsx LemmaScript/tools/src/lsc.ts check --backend=dafny path/to/file.ts
```

## Next

- [CLI reference](/reference/cli/) — every `lsc` command
