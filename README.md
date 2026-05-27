# LemmaScript (Tech Preview)

A verification toolchain for TypeScript. Write ordinary TypeScript with `//@ ` specification annotations. The toolchain generates verifiable code from your TypeScript — either in Dafny or Lean 4 (with Velvet/Loom).

See [SPEC.md](SPEC.md), [DESIGN.md](DESIGN.md), and [GETTING_STARTED.md](GETTING_STARTED.md).

This is a **Tech Preview**: the core idea is there, but support, semantics, and ergonomics are still evolving.

See our [blog post](https://midspiral.com/blog/lemmascript-a-verification-toolchain-for-typescript/).

## Examples and Case Studies

Each example and case study is verified in Lean 4 and/or Dafny from the same annotated TypeScript source.

See the internal [examples](examples).

See the external case studies:
- **[collab-todo-lemmascript](https://github.com/midspiral/collab-todo-lemmascript/)** — collaborative task management web app (React + Supabase) with a verified domain model. Single `domain.ts` imported directly by the UI, hooks, and edge functions — no adapter layer. 123 Dafny lemmas (120 in a separate `domain.proofs.dfy`): 16-conjunct invariant preserved across 25 single-project + 3 cross-project actions, NoOp completeness/soundness, initialization. Dafny only.
- **[colorwheel-lemmascript](https://github.com/midspiral/colorwheel-lemmascript/)** — verified color palette generator with mood + harmony constraints. 31 Lean proofs + 18 behavioral properties, 115 Dafny lemmas (invariant preservation, commutativity, NoOp completeness).
- **[clear-split-lemmascript](https://github.com/midspiral/clear-split-lemmascript/)** — greenfield verified expense splitting web app. Conservation theorem, invariant preservation, delta laws — all proven in both Lean (no sorry) and Dafny (56 lemmas).
- **[github-star-checker-lemmascript](https://github.com/midspiral/github-star-checker-lemmascript/)** — small verified CLI that tracks GitHub star counts across repos and reports per-run deltas. Verifies: per-row diff correctness and `totalDiff == sumDiffs(rows)` (via an inductive `SumDiffs_append` lemma); three sign-classified extractors (gainers / losers / unchanged) with soundness, completeness, **ordered completeness** (gainers appear in the notification in the same order they were listed on the command line), and count/sum equalities against prefix-indexed `upTo` helpers; conservation theorem `decompose(r)` — the three splits partition every row exactly once, and `sumDiffs(increases) + sumDiffs(decreases) == totalDiff`. 33 Dafny VCs, 0 errors; proof additions include a head/tail bridge (`sumDiffs` ↔ `sumDiffsUpTo`) and two partition-on-n inductions. Dafny only.
- **[equality-game-lemmascript](https://github.com/midspiral/equality-game-lemmascript/)** — greenfield verified arithmetic equality card game (React + Tailwind). Sound + complete decision procedure for "can these two card lists be combined into equal expressions": `canEqualize(L, R) ⟺ ∃ eL, eR. eval(eL) == eval(eR) ∧ multiset(leaves(eL)) == multiset(L) ∧ same for R`. Algorithm is subset-DP over a bitmask `m ∈ [1, 2^n − 1)`; the proof composes a `PopCount` upper/lower bound chain (with stdlib `LemmaDivDenominator` / `LemmaFundamentalDivModConverse`), a `splitLeft`/`splitRight` ↔ imperative-loop connection, a `WitnessCombine` lemma threading existential `Expr` witnesses through the cross-product loops, and a `ChooseMask` combinatorial constructor that, given any sub-multiset of `cards`, produces the realizing mask. Capped by `CompletenessFromMaskCoverage`. 753 verification conditions, 0 errors, 0 `assume`s, 0 axioms under `--isolate-assertions --verification-time-limit 180`. Dafny only.
- **[talktimer-lemmascript](https://github.com/midspiral/talktimer-lemmascript/)** — verified talk timer React app, ported from a Dafny-only [`talktimer-lemmafit`](https://github.com/midspiral/talktimer-lemmafit/) twin. 17-variant `Action` state machine + verified `History` (undo/redo/preview/commitFrom) all in one `domain.ts` — the original Dafny's `Domain refines Kernel` abstract-module pattern inlined since LS has no abstract modules. 108 VCs in `domain.dfy` (invariant preservation) + 123 in `domain.proofs.dfy` (behavioral lemmas + Kernel round-trip). Dafny only.
- **[node-casbin-lemmascript](https://github.com/midspiral/node-casbin-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [node-casbin](https://github.com/casbin/node-casbin). 5 functions verified, 217 existing tests pass. End-to-end correctness and order independence for all 4 effect modes in both Lean and Dafny (39 lemmas).
- **[hono-lemmascript](https://github.com/midspiral/hono-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [hono](https://github.com/honojs/hono)'s security middleware. Four CVEs covered: IP restriction bypass ([CVE-2026-39409](https://github.com/honojs/hono/security/advisories/GHSA-3mpf-rcc7-5347)) and cookie name bypass ([CVE-2026-39410](https://github.com/honojs/hono/security/advisories/GHSA-r5rp-j6wh-rvv4)) — 51 Dafny lemmas, [cookie verification **in-place**](https://github.com/midspiral/hono-lemmascript/blob/lemmascript/src/utils/cookie.ts#L79); plus `serveStatic`'s URL-encoded directory traversal ([CVE-2024-32869](https://github.com/honojs/hono/security/advisories/GHSA-q5w7-8mq6-2hxq)) + repeated-slash bypass ([CVE-2026-39407](https://github.com/honojs/hono/security/advisories/GHSA-jw53-c2g8-vmwm)), proved as a *composition* — `decode(rawPath)` before `check(decoded)`, so a buggy implementation that reordered the steps would fail the proof. First use of `//@ assume` + `//@ havoc`-on-assign. Dafny only.
- **[charmchat](https://github.com/CHARM-BDF/charmchat/blob/lemma/README_LemmaScript.md)** — brownfield verification of an AI agent orchestration backend. `isEmptyResult` (string emptiness predicate, 8 postconditions, <1s) and `topologicalSort` (Kahn's algorithm — memory safety, output bounds, completeness via acyclicity ranking witness, termination). Full completeness proof: 23 helper lemmas, 14 opaque ghost predicates, 115 loop invariants; 736 VCs verified under `--isolate-assertions --verification-time-limit 600`. Key technique: snapshot-based inner invariants (`ghost var originalRemDeps := remDeps`) replace the mid-iteration SEEN/UNSEEN split so preservation is frame reasoning against a ghost-constant rather than set-subtraction against mutating state. Dafny only.
- **[xyflow-lemmascript](https://github.com/midspiral/xyflow-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [xyflow](https://github.com/xyflow/xyflow)'s core edge and geometry utilities. 9 functions verified: `addEdge` (dedup — never loses edges, adds at most one), `reconnectEdge` (semantic: under a unique-id precondition, the result is in-place — `|result| ≤ |edges|`, no insertion — *and* when a matching edge existed with non-empty new endpoints, the output contains an edge with those endpoints. Uses `//@ assume` to characterize destructuring, `find`, and the constructed edge), `connectionExists`, `getEdgeCenter` (midpoint correctness), `clamp` (bounds), `rectToBox`/`boxToRect` (field arithmetic), `getBoundsOfBoxes` (enclosure), `getOverlappingArea` (non-negative), `areSetsEqual` (subset + same size). 14 Dafny proof obligations. Dafny only.
- **[rallly-lemmascript](https://github.com/midspiral/rallly-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [rallly](https://github.com/lukevella/rallly)'s meeting-poll Next.js app. 2 functions: `validateRedirectUrl` (in-place — open-redirect predicate; non-`undefined` outputs start with `/` but not `//`) and `scorePoll` (extracted ranking core — length preservation, score bounds, top-choice characterization, score-formula equality, within-poll monotonicity, tiebreaker injectivity). The injectivity proof surfaced a real spec-level constraint on the existing `(yes + ifNeedBe) * 1000 + yes` encoding: it overflows when an option has ≥ 1000 yes votes. 10 Dafny VCs, 0 errors. Drove four toolchain additions: `s.startsWith()`, `T | null` nullability, `\result` narrowing under `==>`, `Math.max(...arr)` spread. Dafny only.
- **[opencode-lemmascript](https://github.com/midspiral/opencode-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield verification of [opencode](https://github.com/anomalyco/opencode)'s permission system and unified-diff patch parser. Highlights: (1) `Patch.parsePatch` carries conservation loop invariants over local ghost state — a parser bug here would silently corrupt user files when an AI applies a patch, and (2) the permission-engine work mechanically closes opencode bug #26514 (subagents bypassing Plan Mode's file-edit restrictions). 9 functions verified in-place, 0 errors. Dafny only.
- **[pi-lemmascript](https://github.com/midspiral/pi-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield, **in-place** verification of the context-compaction cut-point selector in **pi** (the [earendil-works](https://pi.dev) agent harness). When the context window fills, pi discards history before a chosen cut; a provider API rejects a retained prefix containing an orphaned `toolResult` (a tool result whose tool call was cut away). Both selector functions proven: the cut never lets the kept suffix *start with* — nor *split a tool-use/tool-result run* into — an orphaned tool result, even across the backward metadata snap. The no-orphan result forced the session tree's tool-pairing ordering into an explicit `requires`. 4 VCs, 0 errors. Drove five toolchain additions, headlined by an **opaque fall-through type**: a union LemmaScript can't discriminate (here an array-element union of unreachable imports) becomes a single opaque `type` — the field stays present so distinct values stay distinct, and with no constructor or tag predicate it can only be passed through, never unsoundly observed. Dafny only.
- **[balanced-match-lemmascript](https://github.com/midspiral/balanced-match-lemmascript/blob/lemmascript/README_LemmaScript.md)** — brownfield, **in-place** verification of [balanced-match](https://github.com/juliangruber/balanced-match), the ~70-line balanced-bracket finder pulled in by `npm`, `webpack`, and most of the JS tooling stack (1B+ downloads/month). The stack-based `range` core is verified by **refinement**: a pure recursive spec `range_spec` mirrors the loop one branch per recursive case, so the single equivalence `range == range_spec` transfers every property automatically — including an unconditional Dyck body-balance theorem for the interior of every returned pair. 2233 VCs, 0 errors under `--isolate-assertions` (registered on the `dafny-slow` track). Dafny only.
- **[guardians-lemmascript](https://github.com/midspiral/guardians-lemmascript)** — greenfield verification of the core safety argument behind [Guardians](https://github.com/metareflection/guardians) (Erik Meijer, "Guardians of the Agents", CACM Jan 2026), a generate-verify-execute checker for AI-agent workflows. Instead of verifying an app, it proves the agent *guardrail itself sound* — that a static taint/automaton check over the real recursive workflow AST can never admit an unsafe plan. Highlights: taint over **nested conditionals** as a sound branch-union over-approximation; per-source **provenance** with a join (a multi-input tool is tainted if *any* input was); **unbounded loops** discharged by a one-step pre-fixpoint (`sat = t0 ‖ bodyTaint(t0)`) that bounds taint over any iteration count without iterating to a fixpoint; and a **unified capstone** (`verifyWfSound`) — one clean verdict rules out, on *every* path, both a tainted-data-to-sink leak and a security-automaton error. 54 Dafny obligations, 0 errors. The verified cores are reached from a Guardians-style `Workflow`/`Policy` through a thin *unverified* adapter, differentially tested against the real Python Guardians (used as the oracle, not a porting target). Dafny only.
- **[quorum-lemmascript](https://github.com/midspiral/quorum-lemmascript)** — greenfield verified when2meet/Doodle-style group scheduler (React + Cloudflare Durable Objects), with one `domain.ts` running unchanged in the browser, the in-app query, and the server. The standout is that **the proof licenses the architecture**: `countFree` is a homomorphism from participant-list concatenation to integer addition (so the heatmap is order-independent) plus same-participant last-writer-wins convergence — which is exactly what makes the lock-free, no-login, *optimistic* multi-device backend safe, with the Durable Object and the browser applying the **same** verified `applyOp` (server-authoritatively, client-optimistically) with no rollback or operational transform. Also: heatmap is exactly the per-slot count and `isBest` exactly its argmax; monotonicity; invariant-preserving mutations + op-log `replay`; a sparse export codec round-trip; an in-app `whoIsFree(e, s)` whose length provably equals the cell's count; and a separate `grid.ts` proving the `(day, time) → slot` map in-range + injective — which makes specific-dates-vs-days-of-the-week pure shell labeling at zero proof cost; and full element-level permutation invariance (`heatmapPermInvariant` — the heatmap depends only on the *multiset* of participant rows), which drove the `perm(...)` spec predicate into LemmaScript itself. 100 Dafny VCs (90 + 10), 0 errors. The *aggregate* is proven; the React UI, WebSocket/DO I/O, and timezone labeling are the stated trust boundary. Dafny only.
- **[quota-lemmascript](https://github.com/midspiral/quota-lemmascript)** — greenfield verified booking app: providers publish a page of limited-capacity *featured slots*, signed-in users grab them (React + Cloudflare Durable Objects + D1). A deliberate **inverse** of [quorum-lemmascript](https://github.com/midspiral/quorum-lemmascript): where Quorum counts *up to* a threshold over data partitioned **per participant** (no conflicts ⇒ optimistic, lock-free, no rollback), Quota's bookings **contend** for shared inventory, so the load-bearing fact flips from a count to a **bound** — for every slot `j`, `confirmedCount(bookings, j) <= slots[j].capacity` — and so does the concurrency story: the *same* `domain.ts` runs in the browser and the Durable Object, but **server-authoritatively** (it never oversells under contention; no optimistic client apply). Proven: no overbooking (invariant preservation across `tryBook` / cancel), accept-iff-room, an **idempotent three-way `tryBook`** (a retry reads as success, not rejection — only "confirmed" mutates), cancellation frees seats, replay determinism, and full order-invariance of availability under contention — `confirmedCountPerm` / `hasRoomPermInvariant` show availability depends only on the *multiset* of the booking log (any reordering, not just a pairwise swap), via the same `perm(...)` predicate Quorum drove into LemmaScript. NDJSON export is built on the verified `confirmedOnly`. The counting kernel is Quorum's `countFree` re-pointed at bookings — total and precondition-free so it composes. 80 Dafny VCs, 0 errors. Trust boundary (stated plainly): auth, the React UI, WebSocket/DO/D1 I/O, email, slot date/time labeling, and abuse/rate-limiting. Dafny only.
- **[henri-lemmascript](https://github.com/midspiral/henri-lemmascript)** — a runnable TypeScript coding-agent CLI (a port of [henri](https://github.com/metareflection/henri/); multi-provider, Anthropic + AWS Bedrock) whose security- and protocol-critical core is verified and **imported directly by the live agent** — `decide()` gates every real tool call and the conversation invariant is asserted on every turn (it streams end-to-end against Bedrock). Three modules, 48 Dafny VCs, 0 errors. (1) **Permission gate**: soundness (`decide == Allow ⟺ isAllowed`), **path-traversal containment** — auto-allow-in-cwd can never resolve outside cwd, with `.`/`..` normalization proved in-core so the shell is trusted only to `resolve().split('/')` — grant monotonicity, and `rejectPrompts` is deny-only. (2) **Conversation protocol**: tool-call/result pairing plus the [pi-lemmascript](https://github.com/midspiral/pi-lemmascript)-style **no-orphaned-`tool_result`** property, proved as an invariant *preserved by the loop* — `wellFormed(msgs + [assistant(calls), tool(makeResults(calls))])` — not checked after the fact. (3) **Hook/config merge**: removal, **tool-name uniqueness — a fix** (henri concatenated hook tool lists with no dedup, so two hooks could shadow a name), order-independence, and additivity composed **cross-module** with the gate's monotonicity (merging only grows the allow-sets, which by P3 never revokes an `Allow`). The merge is verified **in place** via `//@ declare-type Tool { name: string }`, shadowing the real `Tool`'s function-valued `execute` so the actual `mergeTools(Tool[])` is the proof target rather than a parallel model. Dafny only.

## Setup

**Prerequisites:** Node.js >= 18. For the Lean backend: [elan](https://github.com/leanprover/elan). For the Dafny backend: [Dafny](https://github.com/dafny-lang/dafny) >= 4.x.

**Install from npm:**

```sh
npm install lemmascript
```

**Or from source:**

```sh
git clone https://github.com/midspiral/LemmaScript.git
cd LemmaScript && npm install && npm run build
```

**Lean backend** additionally requires the Loom and Velvet forks:

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
```

## Usage

### Dafny backend

```sh
npx lsc gen --backend=dafny src/myModule.ts
npx lsc check --backend=dafny src/myModule.ts
npx lsc regen --backend=dafny src/myModule.ts
```

The Dafny backend generates two files per TS source: `foo.dfy.gen` (always regeneratable) and `foo.dfy` (source of truth, with LLM/user proof additions). The diff between them must be additions-only.

### Lean backend

```sh
npx lsc gen --backend=lean src/myModule.ts
lake build
```

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

