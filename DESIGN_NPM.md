# DESIGN_NPM — Packaging LemmaScript for npm

**Status:** draft, for review
**Date:** July 2026

## Goals

1. **Source in the box.** Agents work best when the LemmaScript source and spec are readable in `node_modules` — shipping only compiled JS defeats that. This is the bare minimum.
2. **Skills that stay fresh.** A new project should get the Claude Code skills with one command, and updating them should be as cheap as `npm update`.
3. **A cooperation convention** for the satellite tools (`lemmascript-claimcheck`, `lemmascript-guard`, future `lemmascript-*` packages).
4. **Don't reinvent git.** No custom sync/merge/versioning machinery. npm is the distribution channel; git (submodules upstream, the consumer's own repo downstream) handles history and merging.

## Current state (observed)

- The published `lemmascript` package (0.5.9) ships only `tools/dist` — no source, no `SPEC.md`, no skills.
- Consumers already route around this to get at the source: the kit README tells users to run `npx tsx LemmaScript/tools/src/lsc.ts`, and `lemmascript-claimcheck/src/extract.ts` has a fallback that shells into a source checkout via tsx.
- Skills live in `midspiral/lemmascript-skills`, consumed as a git submodule at the kit's `.claude/skills/`. Projects outside the kit have no install or update story.
- **Drift exists today:** `.claude/skills/lemmascript/SPEC.md` differs from `LemmaScript/SPEC.md`. Some difference may be the deliberate Dafny-only trim, but nothing enforces consistency.
- The Lean backend emits `import LemmaScript.JSString`, yet the Lean support library (`LemmaScript/`) is not in the package — Lean users need the repo regardless.
- `lemmascript-claimcheck` is published and already follows a good pattern: peerDep on `lemmascript`, communicates via the `lsc` CLI contract (`lsc extract` JSON).
- `lemmascript-guard` is `private: true` with `bin` pointing at raw `.ts` — not publishable as-is.

## Plan

### 1. Ship source, docs, and the Lean library

Expand `files` in `package.json`:

```jsonc
"files": [
  "tools/dist",       // compiled CLI — bin stays here (fast startup, no tsx)
  "tools/src",        // readable source for agents
  "SPEC.md",
  "SPEC_DAFNY.md",
  "SPEC_LEAN.md",
  "SUBSET.md",
  "GETTING_STARTED.md",
  "TOOLS.md",
  "LemmaScript",      // Lean support library (imported by generated Lean)
  "LemmaScript.lean",
  "lakefile.lean",
  "lean-toolchain"
]
```

Cost: ~750K uncompressed on top of the current 608K — negligible for npm. The full `examples/` tree (1.1M) stays out; at most one or two curated examples.

After `npm i -D lemmascript`, an agent can grep and read the real pipeline (`extract.ts`, `dafny-emit.ts`, `lean-emit.ts`, …) and the annotation grammar without leaving `node_modules`.

### 2. Vendor skills into the package; add `lsc skills`

- Add `midspiral/lemmascript-skills` as a **git submodule** of this repo (e.g. at `skills/`) — the same mechanism the kit already uses, no new machinery. Include it in `files`.
- Add a subcommand alongside `gen|regen|check|info`:

  ```sh
  npx lsc skills    # copy skills into .claude/skills/, overwriting
  ```

- The command is a **dumb copy**: no merge logic, no manifests, no hash tracking. The consuming project's git is the merge tool — if a skill was customized locally, `git diff` after a sync shows exactly what upstream changed, and the user resolves it with tools they already know. This is the concrete meaning of "don't reinvent git."
- Stamp each copied `SKILL.md` with the `lemmascript` version it came from (one marker line), so staleness is visible to humans and agents.

Update story in a consuming project:

```sh
npm update lemmascript && npx lsc skills
```

Projects that want it automatic add `"prepare": "lsc skills"` (the husky pattern): skills refresh on every install.

### 3. Kill SPEC drift structurally

The skill's spec copy is **generated at publish time**: `prepublishOnly` copies (or applies the Dafny-only trim to) the repo's `SPEC.md` into the skill directory. The skill shipped with compiler X.Y.Z always describes compiler X.Y.Z.

This is also the argument for vendoring skills *into* the `lemmascript` package rather than publishing a separate `lemmascript-skills` npm package: the skill documents the annotation grammar, which is versioned with the compiler, so their versions should move together. A skill typo fix becomes a patch release — cheap.

> **Caution:** the submodule must pin the **public** remote. The skills repo also has a
> `lemmascript-skills-private` remote; the npm tarball ships whatever commit the submodule
> points at, so a wrong pin would publish private content.

### 4. Cooperation convention for `lemmascript-*` satellites

One-line convention: **any `lemmascript-*` package may ship a `skills/` directory; `lsc skills` also scans `node_modules` for installed `lemmascript-*` packages and copies theirs in.**

Concretely:

- `lemmascript-claimcheck` — keeps its peerDep + CLI-contract pattern (already correct). Optionally gains `skills/claimcheck/` with agent guidance.
- `lemmascript-guard` — gets the claimcheck treatment before publishing: `tsc` build to `dist/`, `prepublishOnly`, `peerDependencies: { "lemmascript": ">=…" }`, drop `private: true`.
- Inter-package communication stays on the **CLI contract** (`lsc extract` JSON). No programmatic API until something actually needs one.

### 5. The kit's role afterward

The kit keeps its submodule setup for source-first hacking. Its README caveat ("the skills write `npx lsc`; substitute the tsx incantation") disappears for normal projects: the npm path now delivers source, spec, skills, and CLI in one install. `setup.sh` can later prefer the npm path.

## Non-goals

- **No runtime fetching** of skills from GitHub — that reinvents both git and npm.
- **No merge machinery** in the skill installer — overwrite; the consumer's git handles conflicts.
- **No npm scope migration.** `lemmascript` / `lemmascript-*` unscoped names are published and the prefix works.
- **No programmatic API** for the compiler yet; the CLI JSON contract is the interface.

## Optional extra

Expose the skills repo as a Claude Code plugin marketplace (`/plugin marketplace add midspiral/lemmascript-skills`) — git-native distribution that Claude Code updates itself. Complement, not primary channel: plain `.claude/skills/` files remain agent-agnostic.

## Rollout

1. Expand `files`; verify with `npm pack --dry-run` and a scratch-project install (grep the source from `node_modules`, run `npx lsc`).
2. Add the skills submodule; implement `lsc skills` (copy + version stamp); wire the `prepublishOnly` SPEC copy/trim.
3. Publish `lemmascript` patch/minor; test `npm update && npx lsc skills` in a real case-study repo.
4. Add `node_modules` scanning to `lsc skills`; publish `lemmascript-guard`; optionally add `skills/` to claimcheck and guard.
5. Update kit README / `setup.sh`; document the convention in `TOOLS.md`.

## Open questions

- Does the Dafny-only trim of the skill's `SPEC.md` stay (generated via a script at publish time), or does the skill reference the full spec with a "Dafny only" preamble?
- Should `lsc skills` take a `--dir` flag for agents other than Claude Code (e.g. `.cursor/rules`-style layouts), or is `.claude/skills/` enough for now?
- Version stamp format: frontmatter field vs. HTML comment at top of `SKILL.md`?
