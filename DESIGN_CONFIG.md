# DESIGN_CONFIG — Project options via `lemmascript.json`

**Status:** proposal, not implemented. Motivated by two open PRs that each flip a default incompatibly — #209 (externs impure by default) and #211 (Dafny strings as JavaScript UTF-16 code units) — and by #205 (JavaScript number semantics, explicitly "behind an option"). Today `lsc` has no place to put such a switch: behavior is fixed by the emitter, tweaked only by per-file `//@` directives and ad-hoc CLI flags.
**Date:** August 2026

## Requirements

1. **One file, one place.** A project declares its semantic choices in `lemmascript.json`, discovered like `tsconfig.json` (nearest ancestor of the source file). No new flags per choice.
2. **Declared once.** Every option has exactly one declaration — key, type, default, one-line doc — in a registry. Validation, the `LscOptions` type, `lsc config`'s report, and the docs table derive from it. Unknown keys and bad values are errors, never silently ignored (the CLI already rejects stray flags for the same reason: a typo must not verify the wrong thing).
3. **Backward compatible by construction.** No `lemmascript.json` means today's behavior, byte for byte. Both pending PRs land as opt-in options; the checked-in examples don't regenerate. Flipping a default later is a one-line registry edit plus a regen — and any project can pin the old behavior with one key.
4. **Explicit flow.** Options are resolved once per source file in `lsc.ts` and *passed* to the phases that consume them. No phase reads the filesystem or a global.
5. **Self-describing artifacts.** A generated `.dfy` that requires non-default verifier flags says so in its header, so `dafny verify` run by hand and `lsc check` agree on how to read it.

## What counts as an option

An option is a **project-wide model choice**: it changes generated text or verifier flags for every file, has a sensible default, and is not a property of one function. Per-function facts stay `//@` annotations (`pure`, `extern`, `havoc`); per-file prover tuning stays in `LemmaScript-files.txt` (`timeout`, extra flags). The two are complementary: `//@ pure` on one extern overrides `extern-default` for that extern; the option sets what *unmarked* externs mean.

## 1. The file

```json
{
  "backend": "dafny",
  "extern-default": "impure",
  "javascript-utf16": true
}
```

- **Discovery:** nearest `lemmascript.json` at or above the source file, same walk as `tsconfig.json` (`findTsConfig` in `lsc.ts` becomes a shared `findUp`). Absent file → defaults.
- **`--config=<path>`** pins a specific file (CI matrices, fixtures). Same `--flag=value` form as every other flag.
- **Batch mode** resolves per entry, so a `LemmaScript-files.txt` spanning two subprojects with different configs behaves as if each file were run alone. Parsed files are cached per path.
- **Layering, later wins:** built-in defaults ← `lemmascript.json` ← file-level directives (`//@ safe-slice`) ← CLI flags (`--backend=`). `//@ backend` is *not* an override: it restricts which backend a file belongs to and stays a skip, as today.
- `"$schema"` is accepted and ignored (editor convention). Anything else unknown is an error listing the known keys.

## 2. The registry (`tools/src/config.ts`)

One `as const` table; the option type is derived from it, so there is no parallel interface to keep in sync:

```ts
export const OPTION_SPECS = {
  "backend":          { type: "enum", values: ["dafny", "lean"],      default: "dafny",   description: "…" },
  "extern-default":   { type: "enum", values: ["pure", "impure"],     default: "pure",    description: "…" },
  "javascript-utf16": { type: "boolean",                              default: false,     description: "…" },
  "dafny-lib":        { type: "enum", values: ["std-lib", "local-lib"], default: "std-lib", description: "…" },
  "safe-slice":       { type: "boolean",                              default: false,     description: "…" },
} as const;

export type LscOptions = { readonly [K in keyof typeof OPTION_SPECS]: /* boolean | union of values */ };
export const DEFAULT_OPTIONS: LscOptions;

export function validateOptions(raw: unknown, source: string): Partial<LscOptions>;  // per-key checks; returns only explicit keys
export function resolveOptions(explicit: Partial<LscOptions>, source: string): LscOptions; // defaults + dependent defaults + cross-key checks
export function loadOptions(sourcePath: string, configPath?: string): { options: LscOptions; configFile: string | null };
export function withFileDirectives(options: LscOptions, sourceText: string): LscOptions;
```

`validateOptions` returns only the keys that were present, so `resolveOptions` can tell an explicit setting from a default — needed for the one dependent default (§3.2). Cross-key contradictions are errors at load time, not silent overrides, and the message names the fix.

Adding an option is: one registry entry, then `options["<key>"]` in the consuming phase, then a row in SPEC.md §7 and a fixture. Nothing else.

## 3. Initial options

| Key | Values | Default | Consumed by | Backend |
|---|---|---|---|---|
| `backend` | `dafny` \| `lean` | `dafny` | `lsc.ts` (when `--backend=` absent) | — |
| `extern-default` | `pure` \| `impure` | `pure` | extract (`externIsImpure`) | both (Lean rejects impure) |
| `javascript-utf16` | boolean | `false` | dafny-emit, dafny-commands | Dafny |
| `dafny-lib` | `std-lib` \| `local-lib` | `std-lib` (`local-lib` under UTF-16) | dafny-emit | Dafny |
| `safe-slice` | boolean | `false` | dafny-emit | Dafny |

Defaults are today's behavior in every row (requirement 3). The `//@ safe-slice` directive keeps working as a per-file override that sets the option to `true`.

### 3.1 `extern-default` (PR #209)

PR #209's `externIsImpure` becomes the option's consumer, with the same precedence: `//@ impure` → impure; `//@ pure` → pure; both → error; neither → `options["extern-default"] === "impure"`. It applies uniformly to in-file `//@ extern` declarations and to cross-file auto-externs (read from the *source* declaration, including a `//@ pure` on a `const` arrow's variable statement). `extractModule(sourceFile, options)` carries the option in; `RawExtern.impure` stays a resolved boolean, so `lsc extract` output reflects the project's choice and resolve/transform/emit need no change beyond comments and the Lean error text ("add `//@ pure` for a deterministic extern").

### 3.2 `javascript-utf16` and `dafny-lib` (PR #211, issue #210)

Under `javascript-utf16: true`, the Dafny emitter does what PR #211 does, gated:

- `string` types and `str` literals set a per-emission flag; literals are written as `\uXXXX` code-unit escapes for everything outside printable ASCII, so astral pairs and lone surrogates survive the UTF-8 file.
- Preambles that mention chars vary with the mode. This is forced, not stylistic: Dafny 4.11 rejects `\U{…}` escapes under `--unicode-char:false` and `\u…` escapes under the default, so `IsJSWhitespace` (StringTrim) must be emitted with `\u0009…` in UTF-16 mode and `\U{0009}…` otherwise, and `StringFromCharCode`'s `requires` is `0 <= n < 0x10000` vs the surrogate-free scalar range. `PREAMBLE_CODE` entries become `string | (options) => string`.
- The file header records the model (§5), and `dafnyVerify` passes `--unicode-char:false --allow-warnings` when it sees it. `--allow-warnings` is required: 4.11 prints a deprecation warning for the flag and, by default, a warning fails the run.

`dafny-lib` selects where `filter`/`every`/`reduce` come from: `Std.Collections.Seq.Filter/All/FoldLeft` (today; `dafnyVerify` already auto-adds `--standard-libraries` on a `Std.` substring) or the local `SeqFilter`/`SeqAll`/`SeqFoldLeft` recursive helpers from PR #211, emitted into the preamble on demand like `SeqFind`.

The two interact: Dafny's precompiled standard library is built for Unicode-scalar chars and cannot load under `--unicode-char:false`. Hence the one **dependent default** — `javascript-utf16: true` sets `dafny-lib` to `local-lib` unless the user wrote `"dafny-lib"` themselves — and the one **cross-key error**: writing `"std-lib"` next to `"javascript-utf16": true` is rejected at load with the reason. PR #211's per-file fail-closed check stays as the last line of defense (a UTF-16 file whose *proof additions* import `Std.*`), because the config can't see hand-written proof text; its message should name the config key. A string-free file may keep importing `Std.*` in its proofs: the header marker is only emitted when strings actually appear.

### 3.3 `backend`

Sets the backend used when `--backend=` is absent. `AGENTS.md` still recommends passing `--backend=` explicitly and CI scripts keep doing so; the option exists so a project's choice is recorded next to its other choices and `lsc check foo.ts` does the right thing for a human at the keyboard.

### 3.4 Next: `javascript-numbers` (issue #205)

Nothing in this design is specific to strings. #205's preliminary encoding needs (a) a type-mapping change in resolve/emit (`number` → a wrapping newtype rather than `int`/`nat`), and (b) verifier flags (`--type-system-refresh --general-traits=datatype --general-newtypes`). Both slot in: a `"javascript-numbers": boolean` registry entry, a preamble variant, a header marker, and a flag mapping in `dafnyVerify`. The header/flag pattern in §5 is written so a second such option adds a token, not a second bespoke comment.

## 4. Threading through the pipeline

| Phase | Change |
|---|---|
| `lsc.ts` | Parse `--config=`. In `runFile`: `loadOptions(absPath, configPath)` → `withFileDirectives(options, fullText)` → `backend = flags.backend ?? options.backend`, stored back into `options` so the effective set is one object. Pass `options` to `extractModule` and `emitDafnyFile`. `runBatch` resolves per entry (needed for its >60s downgrade rule, which is Dafny-only). |
| `extract.ts` | `extractModule(sourceFile, options = DEFAULT_OPTIONS)`; module-level `_options` set on entry, following the existing `_externs` reset pattern; `externIsImpure` reads it. |
| `resolve`, `narrow`, `autohavoc`, `peephole` | Unchanged. Add an `options` parameter only when an option needs one (`javascript-numbers` will, for resolve). |
| `transform.ts` | Unchanged. `TransformOptions { backend, monadic }` is backend-*intrinsic* configuration chosen by the pipeline, not by the user; keep the two apart rather than merging `LscOptions` into it. |
| `dafny-emit.ts` | `emitDafnyFile(file, tsFileName, options = DEFAULT_OPTIONS)` replaces the `{ safeSlice }` bag; `_useSafeSlice` becomes `_options["safe-slice"]`; adds the `_usesJavaScriptStrings` flag and header line; `filter`/`every`/`reduce` and the two char-sensitive preambles branch on options. All per-emission state resets at the top of `emitDafnyFile`, as `_neededPreambles` does today. |
| `dafny-commands.ts` | `dafnyVerify` derives flags from the generated header (§5) plus the existing `Std.` scan; fail-closed check on the UTF-16 + `Std.` combination. |
| `lean-emit.ts` | Error text only. Dafny-only options are ignored under Lean without a warning — a per-file warning would be noise in batch mode, and the docs table carries the backend column. |
| `info-command.ts` | `lsc info --typed` gains a top-level `options` field (the effective set). Additive, so `schema` stays `1`; satellites that build runtime oracles need to know which string model the Dafny side used. |

Optional-with-default parameters keep any external programmatic caller of `extractModule`/`emitDafnyFile` working; the CLI always passes explicitly.

## 5. The artifact header

PR #211 marks generated files with `// LemmaScript string model: javascript-utf16-code-units` and has `dafnyVerify` grep for it. Keep the idea — the artifact, not the config, is what a human hands to `dafny verify` — but generalize the form so the next option doesn't invent another sentence:

```
// Generated by lsc from foo.ts
// lsc options: javascript-utf16
```

One line, space-separated `key` (boolean) or `key=value` tokens, listing only the non-default options that *materially affected this file* (UTF-16 appears only when the file has strings; `dafny-lib` never appears — it changes emitted helpers, not verifier flags). `dafnyVerify` parses the line and maps tokens to flags: `javascript-utf16` → `--unicode-char:false --allow-warnings`; later `javascript-numbers` → the #205 flags. The additions-only check already guarantees `.dfy` and `.dfy.gen` share the header, so flipping an option in `lemmascript.json` surfaces as an ordinary generator change: `regen` three-way-merges the new header line in, then verifies under the new flags.

Reading flags from the artifact rather than from the config is deliberate: the two can't drift within one `lsc check`, but a standalone `.dfy` (a fixture, a file someone pulled out of a repo) still verifies correctly, and a reader sees the model on line 2.

## 6. CLI surface

- `--config=<path>` — pin the config file (default: discovery).
- `lsc config [<file.ts>]` — print `{ "configFile": …, "options": {…} }`, the effective set for that file after directives and `--backend=`; with no file, from the current directory. The "is my config being picked up?" tool, in the spirit of `lsc extract`.
- `lsc info --typed` — adds `options`.

## 7. Docs and tests

- **SPEC.md §7**: `config` in the command list, `--config=` in flags, new §7.6 "Project configuration: `lemmascript.json`" with the table from §3 (~15 lines, per AGENTS.md style). §2.9/§2.11 extern prose becomes conditional on `extern-default`; §6 type-mapping notes the UTF-16 model. **SPEC_DAFNY.md**: PR #211's paragraph, rephrased as option-gated; helper-table rows for `SeqFilter`/`SeqAll`/`SeqFoldLeft` under `dafny-lib: local-lib`. **SPEC_LEAN.md**: one line on impure externs. **TOOLS.md**: `config.ts` in the file table plus a short "Options" section on the flow in §4. **AGENTS.md**: one line under Toolchain commands pointing at `lsc config`. **site `reference/cli.md`**: flag row, command row, a "Project configuration" section (hand-written page; `DESIGN_CONFIG.md` itself joins `sync-docs.mjs` like the other design docs).
- **`tools/test-fixtures.sh`** grows fixture *directories*, each with its own `lemmascript.json`, so discovery is exercised rather than mocked: `tools/fixtures/extern-impure/` (PR #209's four files: default extern emits `method {:axiom}`, `//@ pure` cross-file equality verifies, unmarked equality fails, Lean rejects unmarked), `tools/fixtures/utf16/` (PR #211's fixture: `"😀".length === 2`, surrogate `charCodeAt`s, header present, the escaped literal `"\uD83D\uDE00"` in the `.dfy.gen`; the `Std.` + UTF-16 standalone `.dfy` fails closed), an invalid config (unknown key; `"std-lib"` + UTF-16) that must fail, and a `lsc config` invocation grepped for its effective values. Existing fixtures run without a config and pin the defaults.
- **CI** is otherwise untouched: examples and case studies verify under defaults, so neither PR's mass regeneration lands.

## 8. Migration of the pending PRs

- **#209** rebases to: `externIsImpure` reading the option; its fixtures move under `tools/fixtures/extern-impure/` with a config; docs phrased conditionally. Its regenerated examples (`autohavoc`, `inlineHandler`, `genericExtern`, `impureExtern`, `impureDie`) are dropped — those examples keep their explicit `//@ impure` and the default keeps them as they are.
- **#211** rebases to: gated emission and preambles, the generic header, `dafnyVerify` flag mapping, `SeqFilter`/`SeqAll`/`SeqFoldLeft` behind `dafny-lib`. Its 60-file example regeneration is dropped.
- **Flipping a default later** (either one): change the registry line, run `./regen-dafny.sh`, note it in the release. Projects that want the old model add one key. The registry's `default` field is where that decision lives, visibly, rather than being implicit in emitter code.

## Non-goals

- A generic `//@ option <key> <value>` per-file directive. Only `safe-slice` has a directive form, and it predates this design. If per-file overrides prove necessary the registry entry grows a `directive` field; nothing else changes.
- Nested/namespaced config (`{"dafny": {…}}`). Flat kebab-case keys with a backend column in the docs are enough at five options; revisit past ~15.
- `time-limit` / `extra-flags` as project defaults. `LemmaScript-files.txt` already carries them per file; adding a project-wide default is a registry entry away if a case study asks.
- JSON Schema generation (`lsc config --schema`). Cheap follow-up from the registry; not needed to land.
- Options in the Raw IR JSON (`lsc extract`). The IR already reflects their effect (`RawExtern.impure`).

## Open questions

1. **Defaults.** This design keeps today's behavior as the default for both pending changes. The alternative — adopt #209's and #211's semantics as the defaults and let projects opt *out* — is the same code with two registry lines flipped and a mass regen, and is arguably where both PRs were headed. Decide before landing; changing later is cheap but touches every checked-in `.dfy`.
2. **`javascript-utf16` as a boolean vs a `strings: "unicode-scalar" | "javascript-utf16"` enum.** The boolean matches how the option was named in discussion and how #205 will be named; the enum leaves room for a third string model that no one has proposed.
3. **`--allow-warnings` scope.** It is needed for the `--unicode-char` deprecation warning but also un-fatals every other warning in the file. Acceptable for now; if Dafny later removes the flag entirely, UTF-16 mode needs a different encoding (e.g. `seq<bv16>` with a string view), which the option boundary would absorb.
4. **Header parsing for hand-edited files.** Because the header is a generated line, the additions-only check protects it. Should `dafnyVerify` also warn when a `.dfy` lacks the `// Generated by lsc` line entirely (a stray file), rather than silently verifying with default flags? Probably yes, as a warning, not an error.
