# DESIGN_NPM — Packaging LemmaScript for npm

**Status:** v2, implemented and live — umbrella + `lsc claimcheck` shipped (claimcheck 0.6.0, lemmascript-claimcheck 0.2.0, lemmascript 0.5.10/0.5.11); skills repo restructured with machine-owned `reference/`; release-sync workflow validated end to end at v0.5.11, publish-from-CI added alongside it (§3 — first release through it pending, after the npmjs.com trusted-publisher config). Open questions below. (v1 vendored source + skills into the tarball; revised after discussion.)
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

The reliability requirement: **skills must not silently drift from releases.** One human action — pushing the `vX.Y.Z` tag — drives everything; each downstream step is idempotent, and any failure is a red run, never silent drift.

Implemented as two sibling workflows on the same tag trigger:

- [`release.yml`](.github/workflows/release.yml) — **publish.** npm trusted publishing (OIDC): no npm token anywhere, and provenance links the tarball to the exact commit and run. Two guards keep it re-runnable: the package.json version must equal the tag, and an already-published version is skipped rather than failed.

  Configuring the trusted publisher (one-time, on npmjs.com; no secret to store):
  1. Log in to npmjs.com → package **lemmascript** → **Settings**.
  2. Under **Trusted Publisher**, choose **GitHub Actions** and enter: organization/user `midspiral`, repository `LemmaScript`, workflow filename `release.yml` (exact filename; renaming the workflow later means updating this), environment left blank. Save.

  That's all — the workflow authenticates via short-lived OIDC tokens minted per run.
- [`release-sync.yml`](.github/workflows/release-sync.yml) — **sync.** Copies the release's `SPEC.md` + `tools/src` into the skills repo's machine-owned `lemmascript/reference/`, commits as `sync from lemmascript vX.Y.Z`, and tags the skills repo in lockstep. It does **not** bump the kit — that is now decoupled (see below). Validated live at v0.5.11.

**Kit tracks tip, not just releases.** The `midspiral/lemmascript-kit` superproject's two submodules advance on every source push, not only on a release tag, via a small `kit-bump.yml` in each source repo:

- [`kit-bump.yml`](.github/workflows/kit-bump.yml) in **LemmaScript** — on push to `main`, advances the kit's `LemmaScript` submodule to the pushed commit.
- `kit-bump.yml` in **lemmascript-skills** — on push to `main`, advances the kit's `.claude/skills` submodule. This fires on ordinary skill edits *and* on the per-release `reference/` sync commit above, so `.claude/skills` still moves on every release — just as a side effect of the skills push rather than a step in `release-sync.yml`.

  Each bumper is idempotent (no-op when the kit already points at the commit) and guarded two ways against the release-time race where both push to the kit at once: a same-repo `concurrency` group serializes a repo's own bumps, and a `git pull --rebase` retry loop absorbs a cross-repo push landing mid-run (the two touch different submodule paths, so rebases auto-merge). A single `release-sync` step doing both bumps atomically was the alternative; per-repo bumpers were chosen so the kit follows tip continuously rather than lurching once per release.

The release loop, in full:

```sh
npm version patch      # the only versioning decision
git push --follow-tags # the only publishing action — the tag is the release
```

The two workflows run in parallel; if publish fails while sync succeeds, skills/kit briefly lead npm — visible as a red `release.yml` run, fixed by re-running via `workflow_dispatch` (the guards make retries free). Only `lemmascript` publishes from CI; satellites release locally at their own, slower cadence.

Design points:

- **Trigger (decided).** Tag-push. `npm version` already creates the annotated `vX.Y.Z` tag; a plain `git push` does not send tags, so the tag reaches GitHub via `git push --follow-tags` — set `git config push.followTags true` once to make it automatic rather than a habit. Both workflows carry a `workflow_dispatch` input (tag name) for backfills and re-runs.
- **Cross-repo auth.** The workflows that push across repos need `contents: write` on the skills repo and the kit repo: a fine-grained PAT (`SYNC_TOKEN`) scoped to exactly those two. `release-sync.yml` and this repo's `kit-bump.yml` read it from the **LemmaScript** repo's secrets; the skills repo's `kit-bump.yml` reads it from the **lemmascript-skills** repo's secrets. The **same token value** serves all three — its scope already covers both target repos — but Actions secrets are per-repo, so it must be set in both source repos. It pushes to the **public** skills repo only — the private mirror remote is untouched by automation. Publishing needs no secret at all — trusted publishing is OIDC.

  Creating/rotating `SYNC_TOKEN` (the one manual step; repo maintainer only):
  1. GitHub → Settings → Developer settings → Fine-grained tokens: resource owner **midspiral**, repository access limited to **lemmascript-skills** and **lemmascript-kit**, permission **Contents: read & write**. (If midspiral is an org, its settings must allow fine-grained PATs — worth a glance.)
  2. Set it as a secret in **both** source repos (same value):
     ```sh
     gh secret set SYNC_TOKEN -R midspiral/LemmaScript
     gh secret set SYNC_TOKEN -R midspiral/lemmascript-skills
     ```
     Or, if `midspiral` is an org, one org secret instead: `gh secret set SYNC_TOKEN --org midspiral --repos LemmaScript,lemmascript-skills`.

  Fine-grained PATs expire — when the workflows start failing on the push steps with auth errors, rotate by repeating these steps (both repos, or the single org secret).
- **Direct push, not PR.** The sync only writes `reference/` (machine-owned), so there is nothing for a human to review; a PR would just be a button to forget. Human skill edits flow through normal PRs and never touch `reference/`, so the two streams cannot conflict.
- **Built-in checks, idempotent by construction.** The sync sanity-checks its output (non-empty spec, `src/lsc.ts` present), commits only when `reference/` actually changed, and tags only if the tag doesn't already exist — so a re-run, or a release that was already hand-synced, is a clean no-op.
- **No drift alarm needed.** With both workflows driven by the same tag, "npm has vX.Y.Z but skills don't" (or vice versa) can only mean a red workflow run, which GitHub already surfaces. A scheduled comparison job would be redundant mechanism.

## 4. Satellites: `lemmascript-claimcheck` and others

- Same tarball rule: **dist only**. `lemmascript-claimcheck` drops `DESIGN.md` from `files` or keeps it — immaterial; new packages ship binaries.
- Same interface rule: peerDep on `lemmascript`, communication via the CLI contract (`lsc extract` JSON). No programmatic API until something needs one.
- Not-yet-published satellites get the claimcheck treatment before release: `tsc` build to `dist/`, `prepublishOnly`, peerDep, drop `private: true`.
- **Satellite skills live in the skills repo** (`lemmascript-claimcheck/`, …), not in the satellite tarballs — one agent layer for the whole ecosystem, one consumption story. If a satellite needs reference material synced, its release workflow reuses the same sync pattern.

### `lemmascript` is the umbrella: one npm command for all tools

**Decision (implemented):** `npm i -g lemmascript` installs the whole toolchain. The officially included satellites are `dependencies` of `lemmascript`, and their functionality is exposed through **`lsc` subcommands** — not separate bin names:

```sh
lsc claimcheck <file.ts> [flags…]   # forwards verbatim to lemmascript-claimcheck
```

How the forwarding works: `lsc` intercepts the subcommand before its own flag parsing, rewrites `process.argv`, and runs the satellite CLI in-process via `import("lemmascript-claimcheck/cli")` — args, stdio, exit codes, and signals behave exactly as a direct invocation (Node strips the shebang on import). A too-old satellite produces a friendly reinstall hint. In-tree forwarding is necessary because npm links only the *named* package's bin entries — dependencies' bins stay in the nested tree, never on PATH (verified empirically on npm 11; a bin-less meta-package installed `-g` exposes zero commands).

The contract a satellite honors to join the umbrella:

- **Export the CLI entry** — `"exports": { "./cli": "./dist/cli.js" }` — and ship type declarations, so the consumer side stays a one-line typed import.
- **Own your runtime needs.** lemmascript-claimcheck moved `claimcheck` from peerDependencies to a real dependency and resolves it from its own tree (`require.resolve("claimcheck/cli")`, spawned) with `$CLAIMCHECK` override above and PATH fallback below — the umbrella needs no knowledge of transitive tooling.

Mechanics and accepted consequences:

- **Standalone commands still exist** — installing a satellite directly (`npm i -g lemmascript-claimcheck`) links its own bin, unchanged.
- **No circularity.** Satellites keep their peerDep on `lemmascript`; nested under the umbrella, the peer resolves to the umbrella itself (an ancestor in the tree). npm handles this shape natively.
- **Caret ranges keep cadences decoupled — within a 0.x minor.** Fresh installs and `npm update -g lemmascript` pick up satellite patches without a `lemmascript` release. Note the 0.x caret rule: `^0.5.1` does *not* match 0.6.0, so a satellite **minor** release requires a hand-edited range bump in its consumer (npm version does not do this).
- **Project installs carry the satellites too.** `npm i -D lemmascript` brings the official set into the project's lockfile. Accepted: the officially included satellites are part of what "the LemmaScript toolchain" means, and CI pins the whole set via the lockfile.
- **"Officially included" = public + blessed.** A satellite joins the umbrella when it is published and considered part of the standard toolchain; until then it is installed individually.
- **Release order flows up the dependency chain:** claimcheck → lemmascript-claimcheck → lemmascript, each consumer bumping its range after its dependency publishes.

## 5. The kit

The kit keeps its submodule setup and remains the **Lean channel** (source checkout + velvet/loom siblings). Its skills submodule now also delivers `reference/`, so the kit's caveat about substituting tsx incantations can shrink: reading source no longer requires knowing the checkout layout — the skill's relative paths work identically in the kit and in npm-consuming projects. The release-sync workflow bumps the kit's submodules to tip on every release, so the kit tracks releases with no manual pointer maintenance.

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
