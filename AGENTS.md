# AGENTS.md

Guidance for AI coding agents working on LemmaScript itself or on projects that use it. Human-oriented docs live in [README.md](README.md), [SPEC.md](SPEC.md), [SPEC_DAFNY.md](SPEC_DAFNY.md), [SPEC_LEAN.md](SPEC_LEAN.md), [DESIGN.md](DESIGN.md), [TOOLS.md](TOOLS.md). This file collects the things that are easy to get wrong if you only read those.

## What LemmaScript is

A verification toolchain for TypeScript. The user writes ordinary TS with `//@ ` annotations. `lsc` generates either:
- **Dafny** — one `.dfy.gen` (always regeneratable) + one `.dfy` (the source of truth where proof additions accumulate). Diff must be additions-only.
- **Lean 4 / Velvet / Loom** — four files: `.types.lean` + `.def.lean` are generated; `.spec.lean` + `.proof.lean` are hand-written.

Whatever you do, the TS file is the source of truth for *the program*. The hand-written verification files are the source of truth for *the proof*. Don't conflate them.

## Toolchain commands

```sh
npx lsc gen   --backend=<dafny|lean> path/to/foo.ts   # generate artifacts
npx lsc check --backend=<dafny|lean> path/to/foo.ts   # gen + verify
npx lsc regen --backend=dafny        path/to/foo.ts   # three-way merge after TS changes
```

Default backend is Dafny. Pass `--backend=...` explicitly anyway — case-study CIs and helper scripts all do, and the default has been flipped before.

After editing `lsc` itself (anything under `tools/`), run `npm run build` before re-invoking `npx lsc` — the CLI runs the compiled `tools/dist/lsc.js`, not the TS source.

## File-edit boundaries

**Never edit these — they are regenerated from `.ts`:**
- `foo.dfy.gen` (Dafny)
- `foo.types.lean`, `foo.def.lean` (Lean)

If a generated file is wrong, the fix is in `foo.ts` (or in the emitter under `tools/`), not in the generated file. The `.gen` extension on the Dafny file is a deliberate signal — it keeps Dafny tooling from auto-verifying it and reminds you it is not the source of truth.

**Edit these freely — they hold proofs:**
- `foo.dfy` (Dafny) — copy of `.dfy.gen` plus additions
- `foo.spec.lean` (Lean) — ghost definitions and helper lemmas
- `foo.proof.lean` (Lean) — `prove_correct` plus tactics

For Dafny, the diff between `foo.dfy.gen` and `foo.dfy` must be **additions-only**. You may insert helper lemmas, ghost predicates, asserts, and loop invariants, but you may not modify or delete generated lines. `lsc check` enforces this. (A subtle trap: don't append a trailing comment to a generated line like `{` or `decreases fuel` — that counts as a *modified* generated line. Put your comment on its own new line.)

### Function-level `ensures` for caller composition

A TS `//@ ensures` always emits a separate `<fn>_ensures` **lemma**; the generated Dafny **function** carries only `requires`/`decreases`. Since a Dafny *function* can't invoke a lemma, a *function* caller can't see a callee's postcondition — e.g. `g()` calling `h(f(x))` where `h` requires `arg >= 0` and `f`'s `>= 0` lives only in `f_ensures` will not verify.

Fix: **hand-add the `ensures` to the generated Dafny function** as an addition. Dafny discharges it inline against the body — even recursively (the function's own postcondition serves as the IH, e.g. `ensures scan(...) >= startDay` on a recursive scan). Callers then compose it with no lemma call. Keep it additions-only: put the `ensures` (and any comment) on their own new lines, above the `{`.

## Regen, don't rm

When the TS changes and the existing `foo.dfy` needs to absorb the new generated code:

```sh
npx lsc regen --backend=dafny foo.ts
```

Do **not** `rm foo.dfy foo.dfy.gen && npx lsc gen ...` — that drops every proof addition you (or the previous agent) made in `foo.dfy`. `regen` does a three-way merge against the old `.dfy.gen` and preserves additions. On conflict it restores the original `foo.dfy` and writes the merged result to `foo.dfy.merged` for manual inspection.

### When regen duplicates declarations: delete `foo.dfy.base`

`regen` anchors its three-way merge on `foo.dfy.base` if that file exists, otherwise on the previous `.dfy.gen`. It writes `foo.dfy.base` when it starts a merge and **deletes it only on success** (after verification passes). So if a `regen` ends in `FAILED` (verification) or `CONFLICT`, a **stale `foo.dfy.base` is left on disk** — seeded from that run's old gen.

The next `regen` then anchors on that stale base instead of the current `.dfy.gen`. If the TS changed again in the meantime, the merge base no longer matches either side and `git merge-file` mis-resolves by **appending fresh copies of the changed declaration and everything after it** — the symptom is a cascade of `Error: Duplicate member name: ...` from Dafny.

**Fix:** delete the stale base and regen again:

```sh
rm -f foo.dfy.base
npx lsc regen --backend=dafny foo.ts
```

With no `.base` present, regen correctly anchors on the current `.dfy.gen`, preserves your proof additions, and merges cleanly. (Equivalently: after any failed `regen`, fix the proofs in `foo.dfy` and run `lsc check` — which never touches `.base` — then `rm -f foo.dfy.base` before your next `regen`.) Keep `*.dfy.base` out of version control.

## Annotation pitfalls

These are the ones that bite repeatedly:

- **`//@ assume` is not a proof shortcut.** It emits `assume P;` in Dafny, telling the verifier to trust `P` unconditionally. It is appropriate to constrain a `//@ havoc`'d value (whose true behavior is outside the LS fragment) — and that's about it. Don't reach for it to paper over a proof obligation you don't feel like discharging. If you find yourself adding `//@ assume` to make verification pass on code you wrote, restructure the algorithm or prove the lemma. (Same goes for `//@ assume false` to silence a `throw new Error(...)` path — instead, characterize the valid-input domain in `//@ requires`.)
- **`//@ havoc` is Dafny-only.** It marks the RHS of a declaration or assignment as nondeterministic. The Lean backend will reject files that use it. Pair it with `//@ assume` immediately after if you need to constrain the resulting value (`|cleaned| <= |text|`, for example).
- **`//@ extern` is the deterministic cousin of `//@ havoc`.** Use it when callers should reason *parametric over* a function whose body is out of model (regex, IO, parser). The axiom is deterministic and extensional — proofs that depend on `f(x) == f(x)` go through.
- **`//@ ` annotations don't support `\old(...)`.** For mutating methods, `this.field` in `ensures` is the post-state; pre-state references must be added as `old(this.field)` in `.dfy` proof additions (see SPEC.md §2.8).
- **Empty Dafny lemma body means *proven*.** `lemma foo() ensures P {}` is auto-discharged by Z3 — it is not "skipped" or "unproven." Only `assume` / `havoc` / weak specs side-step the verifier.
- **Regex isn't in the model.** Code that uses `RegExp`, `String.prototype.match`, `String.prototype.replace(regex, ...)`, etc. cannot be verified inside the LS fragment. Either rewrite to non-regex string operations, or wrap the regex behind `//@ havoc` / `//@ extern` and verify the surrounding logic.

## Dafny verification workflow

Single-lemma iteration is far faster than re-verifying the whole file:

```sh
dafny verify --filter-symbol=lemma_name foo.dfy
```

For a final whole-file pass, run once and inspect with `tail -50` rather than narrowing with `grep` — the verifier's summary line lives at the end, and a partial grep can hide errors that don't match your filter pattern. Add `--isolate-assertions` when one lemma has many conjuncts and you want a clean breakdown of which conjunct is failing; add `--verification-time-limit=<sec>` when the default 30s isn't enough.

### Nonlinear arithmetic: reach for the standard library, don't hand-roll

Goals involving multiplication/division of variables — `(m*p)/p == m`, `(m*p)%p == 0`, `x <= y ==> x*p <= y*p` — are **nondeterministic in Z3**: they verify on one run and time out the next, even as isolated lemma goals. Hand-rolled inductive helpers don't rescue you, because the inductive *step* needs an equally-flaky div/mod-add fact (`(q+p)%p == q%p`).

The robust fix is Dafny's standard arithmetic library, whose `Mul`/`DivMod` lemmas are proven once, robustly:

```dafny
import opened Std.Arithmetic.Mul       // LemmaMulInequality(x,y,z): x<=y && z>=0 ==> x*z<=y*z
import opened Std.Arithmetic.DivMod     // LemmaMulStrictInequality(x,y,z): x<y && z>0 ==> x*z<y*z
                                        // LemmaModMultiplesBasic(m,p): m>=0 && p>0 ==> (m*p)%p == 0
```

`lsc`'s `dafnyVerify` (`tools/dist/dafny-commands.js`) **auto-adds `--standard-libraries` whenever the `.dfy` text contains the substring `Std.`** — so an `import opened` is all you need; no CLI flag or config change, and `lsc check` picks it up. The imports go in as an *inserted* block (additions-only — don't touch the generated header). Euclidean identities (`x == x/p*p + x%p`, `0 <= x%p < p`) and small distributivity (`(k+1)*p == k*p + p`) *are* reliable inline; reserve the library for the cancellation and monotonicity goals.

## Lean verification workflow

`lake build` runs the full chain. `loom_solve` is the default tactic for discharging Velvet VCs, but **it does not automatically apply step lemmas to recursive helpers** — for those, you need an explicit chain (e.g., `loomAbstractionSimp` + the step lemma name) rather than a bare `loom_solve`.

`.spec.lean` is for ghost definitions and helper lemmas; `.proof.lean` is for `prove_correct` plus the tactic script. Keep them separate; don't push everything into `.proof.lean`.

## Brownfield (existing TS codebases)

When verifying a small slice of a larger TS project:

- Add `//@ verify` to the function bodies you want verified. As soon as *any* function in the file has it, `lsc` switches to opt-in mode and silently skips the rest. Type and `const` declarations are always extracted.
- For functions outside the LS fragment that you still want callers to reason about, use `//@ extern` (deterministic axiom) or `//@ havoc` (nondeterministic).
- **In-place means in-place.** When the user asks for in-place verification of an existing function, add annotations only. Don't refactor the production code, don't restructure control flow, don't rename things. The point is that the verified function and the shipping function are byte-for-byte the same.

## Case studies and external repos

If you are working in a `<name>-lemmascript/` clone of an upstream library:

- **Clone with full history.** `git clone --depth=1` will break case-study work that needs to compare against upstream commits.
- **Confirm the upstream is TS-native before proposing it.** Check `repository`, `language`, and the source tree on GitHub. A package with shipped `@types/...` and types-at-API but a JS source tree (e.g., `semver`) is not a LemmaScript brownfield candidate.
- **Pick algorithms where the proof difficulty is the cleverness.** A case study lands well when the interesting part of the proof is the algorithmic insight (an invariant, a witness construction, a partition argument), not data-structure plumbing.
- **Don't reference other case studies or working design docs from production source comments.** `// see DESIGN_X.md for context` and `// like the foo-lemmascript pattern` rot fast and are noise in the verified TS.

## Style for repo edits

- **README case-study entries:** ~2–3 sentences, headline technique only. Lead with what makes the case study compelling (the WHY — what was proven and why it matters), not a function-by-function enumeration. Don't overclaim ("verified end-to-end") and don't apologize ("just a demo") — name the trust assumption inline.
- **SPEC.md / SPEC_DAFNY.md / SPEC_LEAN.md subsections:** match the existing peers in length (~15 lines per subsection). Don't expand a section into multiple subheadings to fit a new feature; usually a sentence and a code block is enough.
- **No customer or partner names in persisted docs.** Use generic terms ("a pilot," "a brownfield user") instead.
- **Light edits stay light.** When the user says "lightly edit" or "one-paragraph edit," that's a single paragraph with no new sub-headings.

## When in doubt

- Re-read the relevant SPEC.md section before adding an annotation you haven't used before.
- `lsc extract foo.ts` prints the Raw IR JSON — useful when the toolchain is doing something you don't expect and you need to see what `extract` produced.
- If a generated file looks wrong, the bug is in `tools/` (most likely `transform.ts`, `peephole.ts`, or one of the emitters), not in the generated text.
