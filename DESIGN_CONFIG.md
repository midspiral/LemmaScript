# DESIGN_CONFIG — Project options via `lemmascript.json`

**Status:** initial implementation complete. The registry, `extern-default`, `safe-slice`, `proof-dir`, file overrides, and `lsc config` are implemented. #211 (Dafny strings as JavaScript UTF-16 code units) and #205 (JavaScript number semantics) remain future users of the mechanism and are not implemented here.
**Date:** August 2026

## Requirements

1. **One project default file.** A project declares its model and artifact-layout defaults in `lemmascript.json`, discovered like `tsconfig.json` (nearest ancestor of the source file). An exceptional source file may override an eligible model option with `//@ option`; no new CLI flag is added per choice.
2. **Declared once.** Every option has exactly one declaration — key, type, default, file-override eligibility, one-line doc, and any legacy directive alias — in a registry. Validation, file-level overrides, the `LscOptions` type, `lsc config`'s report, and the docs table derive from it. Unknown keys and bad values are errors, never silently ignored (the CLI already rejects stray flags for the same reason: a typo must not verify the wrong thing). Dependent defaults and incompatibilities are centralized in `resolveOptions`, never enforced ad hoc by a consumer.
3. **Backward compatible by construction.** No `lemmascript.json` means today's behavior, byte for byte. `extern-default` lands as opt-in; the checked-in examples don't regenerate. Future model options follow the same rule. Flipping a default later is a one-line registry edit plus a regen — and any project can pin the old behavior with one key.
4. **Explicit flow.** Options are resolved once per source file in `lsc.ts` and *passed* to the phases that consume them. No phase reads the filesystem or a global.
5. **Future-ready artifacts.** When a future option requires non-default verifier flags, the generated `.dfy` says so in its header, so `dafny verify` run by hand and `lsc check` agree on how to read it. No initial option requires this machinery.

## What counts as an option

Most options are **file-effective model choices with a project-wide default**: they change generated text or verifier flags, have a sensible default, and are not properties of one function. `lemmascript.json` records the ordinary choice for the project; `//@ option <key> <value>` records an exceptional choice in the source file whose verification semantics it changes. The registry may also contain **project-layout settings**, such as `proof-dir`; these are config-only because putting filesystem routing inside a TS annotation would be surprising and makes relative paths ambiguous.

Per-function facts stay `//@` annotations (`pure`, `extern`, `havoc`); per-file prover tuning stays in `LemmaScript-files.txt` (`timeout`, extra flags). The mechanisms are complementary: `//@ pure` on one extern overrides `extern-default` for that extern; the option sets what *unmarked* externs in that file mean.

## 1. The file

```json
{
  "extern-default": "impure",
  "safe-slice": true,
  "proof-dir": "proofs"
}
```

- **Discovery:** nearest `lemmascript.json` at or above the source file, same walk as `tsconfig.json` (`findTsConfig` in `lsc.ts` becomes a shared `findUp`). Absent file → defaults.
- **`--config=<path>`** pins a specific file (CI matrices, fixtures). Same `--flag=value` form as every other flag.
- **Batch mode** resolves per entry, so a `LemmaScript-files.txt` spanning two subprojects with different configs behaves as if each file were run alone. Parsed files are cached per path.
- **Layering, later wins:** built-in defaults ← `lemmascript.json` ← file-level option directives. Implement this by merging the explicit config and file layers first and resolving defaults and cross-key constraints once afterward. Keeping defaults out of the partial layers also leaves room for future dependent defaults.
- **Per-file syntax:** one `//@ option <key> <value>` per line, at file level. Values use the same boolean or enum spelling as `lemmascript.json`, for example:

  ```typescript
  //@ option extern-default impure
  //@ option safe-slice false
  ```

  Only registry entries with `fileOverride: true` are eligible. Unknown keys, config-only keys, bad values, and duplicate settings in one file are errors with the source line. `//@ safe-slice` remains as a compatibility alias for `//@ option safe-slice true`; using both in one file is a duplicate. `backend` is not an option: `--backend=` selects what the command generates, while `//@ backend` restricts which backend a file belongs to and stays a skip, as today.
- `"$schema"` is accepted and ignored (editor convention). Anything else unknown is an error listing the known keys.

## 2. The registry (`tools/src/config.ts`)

One `as const` table; the option type is derived from it, so there is no parallel interface to keep in sync:

```ts
export const OPTION_SPECS = {
  "extern-default": { type: "enum", values: ["pure", "impure"], default: "pure", fileOverride: true, description: "…" },
  "safe-slice":     { type: "boolean", default: false, fileOverride: true, directiveAliases: ["safe-slice"], description: "…" },
  "proof-dir":      { type: "path", default: null, fileOverride: false, description: "…" },
} as const;

export type LscOptions = { readonly [K in keyof typeof OPTION_SPECS]: /* boolean | enum union | string | null */ };
export type ExplicitOptions = Partial<LscOptions>;
export const DEFAULT_OPTIONS: LscOptions;

export function validateOptions(raw: unknown, source: string): ExplicitOptions; // per-key checks; returns only explicit keys
export function parseFileOptions(sourceText: string, source: string): ExplicitOptions;
export function resolveOptions(explicit: ExplicitOptions, source: string): LscOptions; // defaults + dependent defaults + cross-key checks
export function loadConfigOptions(sourcePath: string, configPath?: string): { explicit: ExplicitOptions; configFile: string | null };
export function resolveDafnyArtifactDir(sourcePath: string, configFile: string | null, options: LscOptions): string;
```

`validateOptions` and `parseFileOptions` return only the keys that were present. `lsc.ts` merges those two partial objects, file over config, and calls `resolveOptions` once, so future dependent defaults can distinguish an explicit setting from a default. `resolveOptions` applies dependent defaults and then rejects cross-key contradictions; the message names the conflicting explicit settings and the fix. The file parser uses the registry's types, enum values, and `fileOverride` field rather than maintaining a second switch; its only special cases come from declared `directiveAliases`. The `path` type accepts a non-empty relative string; the artifact helper anchors it at the selected config file and performs the containment check from §3.3.

Adding an independent option is: one registry entry, then `options["<key>"]` in the consuming phase, then a row in SPEC.md §7 and a fixture. An interacting option also adds its dependent-default or incompatibility rule to `resolveOptions` and a negative fixture; consumers still receive only a valid, fully resolved set.

## 3. Initial options

| Key | Values | Default | Consumed by | Backend |
|---|---|---|---|---|
| `extern-default` | `pure` \| `impure` | `pure` | extract (`externIsImpure`) | both (Lean rejects impure) |
| `safe-slice` | boolean | `false` | dafny-emit | Dafny |
| `proof-dir` | relative path | unset (source directory) | `lsc.ts` artifact paths | Dafny |

Defaults are today's behavior in every row (requirement 3). The two model options accept `//@ option`; the config-only `proof-dir` does not. The legacy `//@ safe-slice` directive keeps working as an alias that sets `safe-slice` to `true`.

### 3.1 `extern-default`

The existing explicit-impurity check becomes `externIsImpure`, with this precedence: `//@ impure` → impure; `//@ pure` → pure; both → error; neither → `options["extern-default"] === "impure"`. It applies uniformly to in-file `//@ extern` declarations and to cross-file auto-externs (read from the *source* declaration, including a `//@ pure` on a `const` arrow's variable statement). `extractModule(sourceFile, options)` carries the option in; `RawExtern.impure` stays a resolved boolean, so `lsc extract` output reflects the project's choice and resolve/transform/emit need no change beyond comments and the Lean error text ("add `//@ pure` for a deterministic extern"). This is an opt-in extension of today's behavior, not a global default flip, and does not depend on a separate extern-default PR.

### 3.2 `safe-slice`

`safe-slice: true` makes JS-clamping slice semantics the project default; `//@ option safe-slice false` can recover direct Dafny slicing for a file with proved bounds. The existing `//@ safe-slice` spelling remains supported. `emitDafnyFile` reads the resolved boolean rather than receiving a separate `{ safeSlice }` bag.

### 3.3 `proof-dir`

`proof-dir` moves the complete Dafny artifact set out of the TS source tree: `.dfy.gen`, the hand-maintained `.dfy`, and transient `.dfy.base` / `.dfy.merged` files all use the mapped directory. It is a non-empty relative path resolved from the directory containing `lemmascript.json`; absent means today's layout beside the `.ts`. This initial option is Dafny-only — relocating Lean's four files also changes Lean module names and Lake roots, so that needs a separate design.

The source path below the config directory is mirrored under the proof root, avoiding basename collisions:

```text
project/lemmascript.json        { "proof-dir": "proofs" }
project/src/search/binary.ts    source
project/proofs/src/search/binary.dfy.gen
project/proofs/src/search/binary.dfy
```

The source must be inside the config directory when `proof-dir` is set (including with `--config=`); otherwise resolution fails rather than inventing a path containing `..`. `lsc` creates the mapped directory before generation and passes it as the working directory for Dafny verification and regen. `lsc config foo.ts` reports the resolved artifact directory as well as the configured option.

Enabling the option must not silently strand proof additions. If the mapped `.dfy` is absent but a sibling `.dfy`, `.dfy.base`, or `.dfy.merged` exists beside the TS, `lsc` fails with paths and tells the user to move the hand-written `.dfy`, discard or inspect merge-state files, and rerun; `.dfy.gen` is regeneratable. Changing from one non-default proof directory to another likewise requires moving the proof first and is documented as a migration, because the new config cannot discover an arbitrary old root.

## Future options (not part of the initial implementation)

The registry and resolution path are intended to accept the following options later, but this proposal does not add their keys, change their emitters, add verifier flags, or add their fixtures.

### `javascript-utf16` and `dafny-lib` (PR #211, issue #210)

A later `javascript-utf16: true` option would gate PR #211's Dafny emitter behavior:

- `string` types and `str` literals set a per-emission flag; literals are written as `\uXXXX` code-unit escapes for everything outside printable ASCII, so astral pairs and lone surrogates survive the UTF-8 file.
- Preambles that mention chars vary with the mode. This is forced, not stylistic: Dafny 4.11 rejects `\U{…}` escapes under `--unicode-char:false` and `\u…` escapes under the default, so `IsJSWhitespace` (StringTrim) must be emitted with `\u0009…` in UTF-16 mode and `\U{0009}…` otherwise, and `StringFromCharCode`'s `requires` is `0 <= n < 0x10000` vs the surrogate-free scalar range. `PREAMBLE_CODE` entries become `string | (options) => string`.
- The file header records the model (§5), and `dafnyVerify` passes `--unicode-char:false --allow-warnings` when it sees it. `--allow-warnings` is required: 4.11 prints a deprecation warning for the flag and, by default, a warning fails the run.

A future `dafny-lib` option would select where `filter`/`every`/`reduce` come from: `Std.Collections.Seq.Filter/All/FoldLeft` (today; `dafnyVerify` already auto-adds `--standard-libraries` on a `Std.` substring) or the local `SeqFilter`/`SeqAll`/`SeqFoldLeft` recursive helpers from PR #211, emitted into the preamble on demand like `SeqFind`.

The two would interact: Dafny's precompiled standard library is built for Unicode-scalar chars and cannot load under `--unicode-char:false`. After config and file layers are merged, `resolveOptions` must implement exactly this rule: if `javascript-utf16` is true and `dafny-lib` is absent, supply the dependent default `local-lib`; if `dafny-lib` is explicitly `std-lib`, reject the combination and name both keys. An explicit incompatible choice is never silently replaced. PR #211's per-file fail-closed check would stay as the last line of defense (a UTF-16 file whose *proof additions* import `Std.*`), because the config can't see hand-written proof text; its message should name the config key. A string-free file could keep importing `Std.*` in its proofs: the header marker would only be emitted when strings actually appear.

### `javascript-numbers` (issue #205)

A later implementation of #205 would need (a) a type-mapping change in resolve/emit (`number` → a wrapping newtype rather than `int`/`nat`), and (b) verifier flags (`--type-system-refresh --general-traits=datatype --general-newtypes`). Both slot into the design as a `"javascript-numbers": boolean` registry entry, a preamble variant, a header marker, and a flag mapping in `dafnyVerify`. The future header/flag pattern in §5 lets it add a token rather than a second bespoke comment.

## 4. Threading through the pipeline

| Phase | Change |
|---|---|
| `lsc.ts` | Parse `--config=`. In `runFile`: `loadConfigOptions(absPath, configPath)` → `parseFileOptions(fullText, absPath)` → merge file over config → `resolveOptions(...)`. Backend selection and `//@ backend` handling stay separate and unchanged. For Dafny, map and create the artifact directory from `proof-dir`, perform the legacy-proof guard, and build all four companion paths there. Pass the effective options to `extractModule` and `emitDafnyFile`. `runBatch` resolves per entry. |
| `extract.ts` | `extractModule(sourceFile, options = DEFAULT_OPTIONS)`; module-level `_options` set on entry, following the existing `_externs` reset pattern; `externIsImpure` reads it. |
| `resolve`, `narrow`, `autohavoc`, `peephole` | Unchanged initially. Add an `options` parameter only when a future option needs one. |
| `transform.ts` | Unchanged. `TransformOptions { backend, monadic }` is backend-intrinsic pipeline configuration; keep it separate rather than merging `LscOptions` into it. |
| `dafny-emit.ts` | `emitDafnyFile(file, tsFileName, options = DEFAULT_OPTIONS)` replaces the `{ safeSlice }` bag; `_useSafeSlice` becomes `_options["safe-slice"]`. No other emission changes are part of this proposal. |
| `dafny-commands.ts` | Algorithms are unchanged; `lsc.ts` passes mapped artifact paths and uses the mapped directory as the verifier/regen working directory. Artifact-derived verifier flags belong to the future options in §5. |
| `lean-emit.ts` | Error text only. Dafny-only options are ignored under Lean without a warning — a per-file warning would be noise in batch mode, and the docs table carries the backend column. |
| `info-command.ts` | `lsc info --typed` gains a top-level `options` field (the effective set). Additive, so `schema` stays `1`. |

Optional-with-default parameters keep any external programmatic caller of `extractModule`/`emitDafnyFile` working; the CLI always passes explicitly.

## 5. Future artifact headers

The initial options do not require non-default verifier flags, so this proposal does not change generated headers or `dafnyVerify`. When a future option does require flags, preserve PR #211's idea — the artifact, not the config, is what a human hands to `dafny verify` — but generalize the form so each option does not invent another sentence:

```
// Generated by lsc from foo.ts
// lsc options: javascript-utf16
```

The future line is space-separated `key` (boolean) or `key=value` tokens, listing only non-default options that *materially affected this file* (UTF-16 would appear only when the file has strings; `dafny-lib` would never appear because it changes emitted helpers, not verifier flags). `dafnyVerify` would parse the line and map tokens to flags: `javascript-utf16` → `--unicode-char:false --allow-warnings`; `javascript-numbers` → the #205 flags. The additions-only check already guarantees `.dfy` and `.dfy.gen` share the header, so flipping an option in `lemmascript.json` would surface as an ordinary generator change: `regen` three-way-merges the new header line in, then verifies under the new flags.

Reading future flags from the artifact rather than from the config is deliberate: the two could not drift within one `lsc check`, while a standalone `.dfy` (a fixture, a file someone pulled out of a repo) would still verify correctly and a reader would see the model on line 2.

## 6. CLI surface

- `--config=<path>` — pin the config file (default: discovery).
- `lsc config [<file.ts>]` — print `{ "configFile": …, "options": {…}, "artifactDir": … }`, the effective set for that file after directives and its resolved Dafny artifact directory; with no file, resolve project defaults from the current directory and omit `artifactDir`. The "is my config being picked up?" tool, in the spirit of `lsc extract`.
- `lsc info --typed` — adds `options`.

## 7. Docs and tests

- **SPEC.md §2 and §7**: add `option` to the file-level directive table; add `config` to the command list, `--config=` to flags, and new §7.6 "Project configuration: `lemmascript.json`" with the table from §3 (~15 lines, per AGENTS.md style). §2.7 describes `safe-slice` as both an option and a legacy directive; §2.9/§2.11 extern prose becomes conditional on `extern-default`. **SPEC_DAFNY.md**: document `proof-dir`, its mirrored layout, and proof migration. **SPEC_LEAN.md**: one line on impure externs. **TOOLS.md**: `config.ts` in the file table plus a short "Options" section on the flow in §4. **AGENTS.md**: one line under Toolchain commands pointing at `lsc config`; its regen rules apply to mapped paths unchanged. **site `reference/cli.md`**: directive, flag, and command rows plus a "Project configuration" section (hand-written page; `DESIGN_CONFIG.md` itself joins `sync-docs.mjs` like the other design docs).
- **`tools/test-fixtures.sh`** keeps a small fixture directory with `lemmascript.json` and a nested source file to exercise nearest-ancestor discovery, plus invalid config fixtures for an unknown key and a bad value. It verifies that `proof-dir` mirrors the nested path, creates `.dfy.gen` and `.dfy` there rather than beside the TS, and refuses to bypass a pre-existing sibling proof. Self-contained source fixtures use `//@ option` to exercise `extern-default`, `safe-slice: false`, a config-only `proof-dir` directive error, bad and duplicate directives, and precedence over the project config. A `lsc config` invocation is grepped for the effective post-directive values and resolved artifact directory. Existing fixtures run without a config and pin the defaults. UTF-16 and JavaScript-number fixtures are deferred with those options.
- **CI** is otherwise untouched: examples and case studies verify under today's pure-extern default; #211 and #205 are outside the initial scope.

## 8. Initial scope and future PRs

- **`extern-default`** generalizes the existing explicit `//@ impure` path and adds config/directive fixtures and conditional docs. No default-flipping PR or regenerated examples are needed; existing examples keep their explicit `//@ impure`, and unmarked externs remain pure.
- **Existing `safe-slice`** moves from an emitter-specific boolean into the registry without changing generated output. Its old directive remains an alias.
- **`proof-dir`** adds path routing only; it does not change emitter text or the additions-only/regen algorithms. Existing projects stay beside-source until they opt in and move their hand-written proofs.
- **#211 and #205** do not land as part of this proposal. When their encodings are ready, they add registry entries and the explicitly future emitter/header work above, with their own fixtures and docs.
- **Flipping a default later:** change the registry line, run `./regen-dafny.sh`, and note it in the release. Projects that want the old model add one key. The registry's `default` field is where that decision lives, visibly, rather than being implicit in emitter code.

## Non-goals

- Per-function option overrides. `//@ option` is file-level; function facts keep their specific annotations.
- A `backend` config option. `--backend=` selects the command target and `//@ backend` declares file membership; neither is a semantic model option.
- Relocating Lean artifacts with `proof-dir`. Lean paths participate in module names and Lake roots, unlike standalone Dafny files, so that needs its own design.
- Implementing `javascript-utf16`, `dafny-lib`, or `javascript-numbers`; they are future applications documented above, not initial registry entries.
- Nested/namespaced config (`{"dafny": {…}}`). Flat kebab-case keys with a backend column in the docs are enough for the initial options; revisit past ~15.
- `time-limit` / `extra-flags` as project defaults. `LemmaScript-files.txt` already carries them per file; adding a project-wide default is a registry entry away if a case study asks.
- JSON Schema generation (`lsc config --schema`). Cheap follow-up from the registry; not needed to land.
- Options in the Raw IR JSON (`lsc extract`). The IR already reflects their effect (`RawExtern.impure`).

## Open questions

1. **Future string option shape.** Should `javascript-utf16` be a boolean or should a later proposal use `strings: "unicode-scalar" | "javascript-utf16"`? This does not block the initial config implementation.
2. **Future `--allow-warnings` scope.** UTF-16 mode would need it for Dafny's `--unicode-char` deprecation warning, but it also un-fatals every other warning in the file. Resolve this with the UTF-16 implementation, not here.
3. **Future header parsing.** When artifact-derived flags exist, should `dafnyVerify` warn when a `.dfy` lacks the `// Generated by lsc` line entirely? Resolve this with the first option that needs such a header.
