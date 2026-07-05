# DESIGN_NPM — Packaging LemmaScript for npm

**Status:** draft v2, for review (v1 vendored source + skills into the tarball; revised after discussion)
**Date:** July 2026

## Requirements

1. **node_modules contains only the binary.** No source code in the tarball. Agents have no reason to enter `node_modules` at all.
2. **The skills have access to the source code and the spec of the latest release**, as ordinary files in the consuming project's working tree — greppable, and git-visible if edited.
3. **Skills serve all agents**, not just Claude Code: agent-neutral content, consumer-chosen install location.
4. **Every mechanism is stock git or stock npm.** No custom sync/merge/versioning machinery, no version stamps (git commits and tags are the provenance), no installer that could clobber user-defined skills.
5. **Installing the tools is one npm command:** `npm i -g lemmascript` brings the officially included satellites with it (umbrella with shim bins, §4). No bespoke installer or setup script.

## Architecture: three homes

| Home | Contains | Role |
|------|----------|------|
| npm package `lemmascript` | `tools/dist` (+ auto-included README, LICENSE) | **Run.** Opaque execution artifact; integrity via immutable tarball + lockfile hash. |
| skills repo `midspiral/lemmascript-skills` | skills + `reference/` (spec, source snapshot) | **Read.** The agent-facing layer, synced from each release by CI. |
| repo `midspiral/LemmaScript` | everything | **Develop.** Single source of truth; its release workflow feeds the other two. |

Each artifact lives in exactly one place; every copy is machine-maintained and one-directional.

## 1. The npm package: binary only

`files: ["tools/dist"]` — which is the published package today, so the npm side requires no change beyond the README. npm force-includes README and LICENSE; the README points at the skills repo as the documentation and source channel.

Deliberate properties of the tarball:

- **No source, no build script.** The readable source lives in the skills layer (§2). What ships is the execution artifact only; converting a source edit into changed behavior would require deliberately routing around the packaging, which no packaging choice prevents and which CI's fresh install erases anyway.
- **Dafny-first, unchanged from v1:** the Lean workspace (velvet/loom sibling checkouts, mathlib, solver downloads) cannot resolve outside a source checkout. `lsc gen --backend=lean` keeps working exactly as far as it naturally does — no gating code. Lean verification's distribution channel is the source kit.

## 2. The skills repo: the agent layer

### Layout

```
lemmascript/
  SKILL.md            # workflow, failure→fix guidance, source map (relative paths)
  reference/          # machine-owned: written only by the release sync (§3)
    SPEC.md           # verbatim copy of the release's SPEC.md
    src/              # snapshot of tools/src from the release
lemmascript-design-doc/
lemmascript-proof-review/
lemmascript-verified-codebase/
```

- **`reference/` is machine-owned.** Humans never edit it; the release workflow overwrites it wholesale. Humans own everything else. This split means sync commits and human PRs cannot conflict by construction.
- **Skill names carry the `lemmascript` prefix** (one-time rename of `design-doc`, `proof-review`, `verified-codebase`). Ownership is legible in a directory listing, and collisions with a consumer's own generically-named skills become practically impossible.
- **Content is agent-neutral:** workflow steps, shell commands, file paths, failure→fix tables. No harness-specific tool names. SKILL.md (frontmatter + markdown) is an open format read by multiple harnesses; what differs per agent is only the install location.

### The source map

SKILL.md points into `reference/` with **relative paths** (`reference/src/dafny-emit.ts` — "when the spec doesn't answer why `lsc` emitted something, read the emitter here"). Relative paths are stable in every layout; there is no node_modules discoverability caveat, no hoisting workaround. One norm-setting line: *"`reference/` is a read-only snapshot of the release — edits here have no effect on the installed binary; if `lsc` seems wrong, that's a bug report or a version pin, not a local patch."*

### Consumption

Consumers mount the skills repo at `.claude/skills/` (or wherever their harness looks):

- **git submodule** — a pointer, no weight in the consumer's history; the kit's proven pattern. Downside: the mount point owns the whole directory, so user-defined skills live beside it, and clones need `--init`.
- **git subtree** — skills merge in as regular files; user-defined skills coexist in the same directory, and a consumer who customized a shipped skill gets a real three-way merge *by git* on update. Downside: ~600K of reference source lands in the consumer's history per sync.
- Agents with no skills support: the files are ordinary markdown in the repo; a one-line pointer in the project's `AGENTS.md` ("before writing verified code, read `.claude/skills/lemmascript/SKILL.md`") makes them reachable. Documented snippet — nothing auto-edits the consumer's files.

Updating is the consumer's existing git discipline: bump the submodule / `git subtree pull`, review the diff. Pinning: the skills repo is tagged in lockstep with npm releases (§3), so a project pinned to `lemmascript@0.5.9` can pin skills to `v0.5.9`.

## 3. The release + sync workflow (the "sure process")

The reliability requirement: **skills must not silently drift from releases.** The way to make the process *sure* is atomicity — publishing and syncing are one workflow, so one cannot happen without the other being attempted, and a failure is a red run, not silent drift.

Recommended: releases run in a GitHub Action in `midspiral/LemmaScript`.

```yaml
# .github/workflows/release.yml (sketch)
on:
  push:
    tags: ["v*"]          # created by `npm version`; pushed via `git push --follow-tags`

jobs:
  publish:
    runs-on: ubuntu-latest
    permissions:
      id-token: write      # npm trusted publishing (OIDC) — no npm token secret
    steps:
      - checkout @ tag
      - npm ci && npm run build && npm test/typecheck
      - npm publish --provenance

  sync-skills:
    needs: publish         # atomicity: only after a successful publish
    runs-on: ubuntu-latest
    steps:
      - checkout LemmaScript @ tag
      - checkout midspiral/lemmascript-skills   # token: SKILLS_SYNC secret
      - run: cp SPEC.md skills/lemmascript/reference/SPEC.md   # verbatim, no trim script
      - run: rsync --delete tools/src/ skills/lemmascript/reference/src/
      - run: scripts/check-source-map.ts        # every path cited in SKILL.md exists
      - commit "sync from lemmascript vX.Y.Z" && push
      - tag skills repo vX.Y.Z && push tag
```

Design points, including the ones to settle:

- **Trigger (decided).** Tag-push. `npm version` already creates the annotated `vX.Y.Z` tag; a plain `git push` does not send tags, so the tag reaches GitHub via `git push --follow-tags` — set `git config push.followTags true` once to make it automatic rather than a habit. A `workflow_dispatch` input (tag name) rides along as a three-line fallback for backfills and re-runs where no tag-push run exists. The interim failure mode "published to npm but tag never pushed" disappears entirely once publishing itself moves into the Action — the recommended endpoint: trusted publishing (OIDC) means no npm token on any laptop, and `--provenance` links the tarball verifiably to the exact commit, which complements the trust story below.
- **Cross-repo auth.** The sync job needs `contents: write` on the skills repo: a fine-grained PAT or a GitHub App installation token as a repo secret. It pushes to the **public** skills repo only — the private mirror remote is untouched by automation.
- **Direct push, not PR.** The sync only writes `reference/` (machine-owned), so there is nothing for a human to review; a PR would just be a button to forget. Human skill edits flow through normal PRs and never touch `reference/`, so the two streams cannot conflict.
- **Built-in checks.** The sync fails loudly if the source map cites a path that no longer exists — catching a renamed emitter file at release time instead of leaving a dangling pointer in the skill.
- **No drift alarm needed.** With publish and sync in one workflow, "npm has vX.Y.Z but skills don't" can only mean a red workflow run, which GitHub already surfaces. A scheduled comparison job would be redundant mechanism; skip it unless local publishing is kept long-term.

## 4. Satellites: `lemmascript-claimcheck` and others

- Same tarball rule: **dist only**. `lemmascript-claimcheck` drops `DESIGN.md` from `files` or keeps it — immaterial; new packages ship binaries.
- Same interface rule: peerDep on `lemmascript`, communication via the CLI contract (`lsc extract` JSON). No programmatic API until something needs one.
- Not-yet-published satellites get the claimcheck treatment before release: `tsc` build to `dist/`, `prepublishOnly`, peerDep, drop `private: true`.
- **Satellite skills live in the skills repo** (`lemmascript-claimcheck/`, …), not in the satellite tarballs — one agent layer for the whole ecosystem, one consumption story. If a satellite needs reference material synced, its release workflow reuses the same sync pattern.

### `lemmascript` is the umbrella: one npm command for all tools

**Decision:** `npm i -g lemmascript` installs the whole toolchain. The `lemmascript` package lists the officially included satellites as `dependencies` and exposes their CLIs through its own `bin` entries:

```jsonc
"bin": {
  "lsc": "tools/dist/lsc.js",
  "lemmascript-claimcheck": "tools/dist/shims/claimcheck.js"
  // one shim per officially included satellite
},
"dependencies": {
  "ts-morph": "…",
  "lemmascript-claimcheck": "^0.1.0"
}
```

The shims are necessary because npm links only the *named* package's bin entries — dependencies' bins stay in the nested tree, never on PATH (verified empirically on npm 11; a bin-less meta-package installed `-g` exposes zero commands). Each shim is one line, delegating in-process so args, stdio, exit codes, and signals behave as if the satellite were invoked directly (Node strips the shebang on import):

```js
#!/usr/bin/env node
import "lemmascript-claimcheck/cli";   // satellite adds "./cli" to its exports map
```

Verified end to end in both install modes: with `-g` (scratch prefix), the umbrella's own CLI and the shim both land in the global bin dir and the shim runs the nested satellite's CLI with arguments passing through. In a local project install, the shim's name collides with the satellite's own bin in `node_modules/.bin`; npm resolves this silently in favor of the direct dependency (the umbrella), and the collision is benign by construction — both candidates run the same satellite CLI, so either winner behaves identically.

Mechanics and accepted consequences:

- **No circularity.** Satellites keep their peerDep on `lemmascript`; nested under the umbrella, the peer resolves to the umbrella itself (an ancestor in the tree). npm handles this shape natively.
- **Caret ranges keep cadences decoupled.** Satellites release on their own schedule; fresh installs and `npm update -g lemmascript` pick up the latest compatible satellite versions without a `lemmascript` release. A `lemmascript` release is only needed to add a satellite to the official set (a new shim + dependency) or to raise a floor.
- **Project installs carry the satellites too.** `npm i -D lemmascript` brings the official set into the project's lockfile. Accepted: the officially included satellites are part of what "the LemmaScript toolchain" means, and CI pins the whole set via the lockfile.
- **"Officially included" = public + blessed.** A satellite joins the umbrella when it is published and considered part of the standard toolchain; until then it is installed individually.

## 5. The kit

The kit keeps its submodule setup and remains the **Lean channel** (source checkout + velvet/loom siblings). Its skills submodule now also delivers `reference/`, so the kit's caveat about substituting tsx incantations can shrink: reading source no longer requires knowing the checkout layout — the skill's relative paths work identically in the kit and in npm-consuming projects.

## Trust story

The tampering concern ("readable source invites edits; a patched verifier produces meaningless green"):

- **Run/read split.** The thing that runs (`tools/dist` in node_modules) and the thing you read (`reference/src` in the working tree) are different trees. The read copy is on no execution path — patching it accomplishes nothing.
- **Edits are visible.** `reference/` lives in the consumer's working tree: any edit shows in `git status` and diff review — the inverse of invisible node_modules edits.
- **The claim anchors in CI.** Local green is advisory; the verification that counts runs `npm ci` — pristine tooling from an immutable, hash-pinned tarball (with `--provenance`, verifiably built from the tagged commit).
- **Norms over gates.** One read-only line in the skill; no permission bits, no checksum machinery in consumers.

## Non-goals

- No source, docs, or skills in npm tarballs — the tarball is the execution artifact.
- No `lsc skills` command, no installer, no overwrite semantics — consumption is git.
- No version stamps in skill files — sync commit messages and lockstep tags are the provenance.
- No merge machinery — subtree consumers get git's own three-way merge; that is the ceiling.
- No runtime fetching of anything from GitHub.
- No Lean toolchain in the package; no gating code around the Lean backend.
- No npm scope migration.

## Rollout

1. Skills repo: restructure to prefixed skill names + `reference/`; hand-run one sync from v0.5.9 to validate the trim script and source-map check.
2. LemmaScript repo: add `release.yml` (publish + sync); set up npm trusted publishing and the skills-repo write token; move `npm publish` into CI.
3. Slim `files` if needed, update README to point at the skills repo; release a patch through the new workflow end to end.
4. Consumers: document the two mount recipes (submodule, subtree) + the `AGENTS.md` pointer snippet; migrate the kit's submodule to the restructured skills repo.
5. Satellites: publish the remaining satellites; add satellite skill dirs to the skills repo as needed.

## Open questions

- **Curated examples in `reference/`?** Two or three Dafny triples (`binarySearch`, one lemma-heavy case like `toposort`, `todo-domain`) ride the same sync train at ~150K, giving agents worked proof patterns. Decide after the base sync works.
- **Companion docs in `reference/`?** `SPEC_DAFNY.md` and `SUBSET.md` are small and load-bearing for agents — lean toward syncing them. Human-facing docs (`GETTING_STARTED.md`, `TOOLS.md`) stay in this repo only; for agents, SKILL.md is the getting-started.
