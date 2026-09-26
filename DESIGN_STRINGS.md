# DESIGN_STRINGS — JavaScript string semantics as a versioned profile

**Status:** rung 0 and rung 1 implemented in PR #211; later rungs unscheduled. Takes up the `javascript-utf16` sketch in [DESIGN_CONFIG.md](DESIGN_CONFIG.md) §"Future options" and answers its open question 1 with the enum shape it asked about. Rung 1 is PR #211 rebased onto the option registry that shipped in 0.6.4 — #211's merge-base is 0.6.1 (`bcaf168`), before `tools/src/config.ts` existed.
**Date:** September 2026
**Issue:** [#210](https://github.com/midspiral/LemmaScript/issues/210) · **PR:** [#211](https://github.com/midspiral/LemmaScript/pull/211)

## Decision summary

A kind of string is a **named, versioned profile**: a domain of admitted values, a
length/index/equality semantics proved to agree with JavaScript on that domain, a closed
set of operations each with a stated meaning, and an **identity stamped into every proof**.
LemmaScript should expose it as an enum-shaped project option, not a boolean — the same
shape [DESIGN_NUMBERS.md](DESIGN_NUMBERS.md) chose for `number-semantics`:

```json
{
  "string-semantics": "unicode-scalar"
}
```

| Value | Artifact identity | Meaning | Intended use |
|---|---|---|---|
| `unicode-scalar` | `unicode-scalar-1` | Today's model, byte for byte: Dafny `string` under `unicode-char:true`, one `char` per Unicode scalar. `.length`, indexing, `slice`, and `charCodeAt` are over scalars and differ from JavaScript for astral characters; unpaired surrogates are outside the domain. | Existing proofs. Strings that are ASCII, or where only emptiness, equality of well-formed text, and search matter. |
| `javascript-utf16` | `javascript-utf16-1` | PR #211's model: `unicode-char:false`, one `char` per UTF-16 code unit. `.length`, indexing, `slice`, and `charCodeAt` are exact; `String.fromCharCode` is exact for `0 <= n < 0x10000` (JavaScript's ToUint16 wrap is refused by precondition). The Dafny standard library is unavailable. | Code whose behaviour depends on code-unit counts, surrogates, or `charCodeAt` of non-BMP text. |

`unicode-scalar` stays the default so no `lemmascript.json` means today's behaviour
([DESIGN_CONFIG.md](DESIGN_CONFIG.md) requirement 3). A project opts into `javascript-utf16`
with one key. A `javascript-utf16` proof carries `// lsc options: string-semantics=javascript-utf16`
in its header ([DESIGN_CONFIG.md](DESIGN_CONFIG.md) §5 form); the default's header is
unchanged, so no existing artifact changes. Each identity's claim sentence lives in
SPEC_DAFNY.md §4. `dafnyVerify` pins `--unicode-char:true` whenever the token is absent —
today the default is Dafny's *unstated* setting rather than a pin.

The immediate deliverable is rung 0 (§7): name the profile, make it configuration, and pin the
default in the verifier. It changes no semantics and no checked-in file, and is worth landing
whether or not #211 merges. Rung 1 is #211's emitter work on the option registry, gated on the
option.

## 1. What "faithful" means for strings

For each supported string construct, translation must commute with ECMAScript evaluation on
the profile's domain:

```text
decode(evalBackend(translate(e))) = evalECMAScript(e)   for every string value in Domain(profile)
```

The observable results are: a Number for `.length`, `indexOf`, and `charCodeAt`; a string
for `slice`, `substring`, `trim`, case mapping, `repeat`, concatenation, and template
literals; a Boolean for `includes`, `startsWith`, `endsWith`, and `===`; and a string array
for `split`. A JavaScript string is a sequence of UTF-16 code units
([ECMAScript §6.1.4](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-ecmascript-language-types-string-type));
`.length` counts code units, indexing yields code units, and unpaired surrogates are legal
values. Nothing in the language distinguishes a code point from its surrogate pair except by
value.

This is scoped to the LemmaScript fragment. Constructs outside it — regular expressions,
`normalize`, `localeCompare`, `Intl.*`, iteration by code point — do not become supported
because the string model is faithful. Every accepted construct must be faithful on the
selected profile's domain, or refused with a diagnostic. An unmodelled construct is never an
opportunity to emit a scalar operation and call it a code-unit one.

Where the two languages disagree, the difference becomes an obligation, a refusal, or a
stated claim in the artifact. It never becomes an approximation that looks right.

## 2. The mismatch, and why a boolean is the wrong shape

Dafny defines `string` as `seq<char>`, and `char` depends on `--unicode-char`
([Dafny 4.11 reference](https://dafny.org/v4.11.0/Compilation/StringsAndChars)):

| Concern | JavaScript | Dafny, `unicode-char:true` (4.x default) | Dafny, `unicode-char:false` |
|---|---|---|---|
| Element | UTF-16 code unit | Unicode scalar value | UTF-16 code unit |
| `"😀".length` / `\|"😀"\|` | 2 | 1 | 2 |
| `"\uD83D"` (lone surrogate) | length 1 | not representable | length 1 |
| Standard library | — | available | **incompatible** (`--standard-libraries` help: "Not compatible with the --unicode-char:false option") |
| Status of the option | — | silent (not listed by `dafny verify --help`) | deprecated in the CLI: `:false` prints `CLI: Warning: the option unicode-char has been deprecated.`; `:true` prints nothing |

`main` passes no `--unicode-char` at all
([`tools/src/dafny-commands.ts` `dafnyVerify`](tools/src/dafny-commands.ts)), so the scalar
model is Dafny's default, not a LemmaScript decision, and the one-line header
`// Generated by lsc from foo.ts` does not mention it. A reader of a standalone `.dfy` cannot
tell that `|s|` in the proof is not JavaScript's `s.length`. #211 flips the model whenever a
file contains a string, marks the artifact, and text-scans the mark in the verifier. That
makes the model observable, but it is presence-selected *semantics*: every string-bearing
case study's obligations are reinterpreted and its `.dfy.gen` changes, so `lsc check` fails
until a `regen` — that is the "breaking" in #210. A presence-emitted *annotation* is harmless
to proofs and is what DESIGN_CONFIG.md §5 already specifies; the fix is to declare the model
in configuration and let the header record a non-default choice.

A boolean fixes the declaration and stops there. A profile family is what the next rung
needs: JavaScript also offers `normalize()` (canonical equivalence) and `Intl.Segmenter`
(grapheme clusters), each a different domain and equality with its own trusted, versioned
tables. LemmaSwift's `textProfile` went from one rung to four on one key; each rung landed as
its own PR with its own evidence, and asking for an unimplemented rung is a configuration
error naming today's values, never a silent reinterpretation. Those rungs exist because
Swift's `.count` is grapheme-based; JavaScript's `.length` is code units and no issue asks for
`normalize()` or `Intl.Segmenter`, so the same *shape* applies here — the enum costs nothing
now and avoids a second key later — not the same schedule.

## 3. The two rungs, operation by operation

The string surface is the twelve `string.*` entries in
[`tools/src/builtins.ts`](tools/src/builtins.ts) (typed by the resolver), plus `s.indexOf`
and `s.charCodeAt` — which the resolver types `unknown` and the Dafny emitter lowers by
method name (`dafny-emit.ts`) — plus `.length` (typed `nat` in resolve), indexing (typed
`unknown`), `String.fromCharCode` (typed `string`), `+`, template literals, and `===`.
Registering `string.indexOf`/`string.charCodeAt` there is deferred (§7): they type `unknown`
today, and a registered return type would change emitted text. Each row states what a proof
under each rung claims. "Exact"
means the emitted Dafny equals the JavaScript result for every value in the rung's domain.

| Operation | Emitted Dafny (today) | `unicode-scalar-1` | `javascript-utf16-1` |
|---|---|---|---|
| `s.length` | `\|s\|` | scalar count — **differs from JS for astral text** | exact |
| `s[i]`, `s.charCodeAt(i)` | `s[i]`, `(s[i] as int)` | scalar at scalar index — **differs** | exact |
| `s.slice(a, b)`, `s.substring(a, b)` | `s[a..b]` | scalar indices — **differs** | exact |
| `String.fromCharCode(n)` | `StringFromCharCode(n)`, `requires 0 <= n < 0xD800 \|\| 0xE000 <= n < 0x110000` | surrogates refused by precondition (today's behaviour, now stated) | `requires 0 <= n < 0x10000`; exact |
| `a + b`, template literals | `+` | exact on the domain | exact |
| `===`, `!==` | `==` | exact on the domain (no two distinct scalar sequences are equal) | exact |
| `s.indexOf(t)`, `.includes` | `StringIndexOf` | scalar offsets — **differs** | exact |
| `s.startsWith(t)`, `.endsWith(t)` | prefix/suffix `==` | exact on the domain | exact |
| `s.split(d)` | `StringSplit` (axiomatic; `requires \|d\| > 0`, `1 <= \|res\| <= \|s\| + 1`) | trusted axiom, as today; `split("")` refused by precondition | same |
| `s.trim*()` | `StringTrim` via `IsJSWhitespace` | exact — whitespace set is BMP-only in both encodings | exact; escape form changes (`\u` vs `\U{}`) |
| `s.toLowerCase()`, `.toUpperCase()` | `StringToLower`/`Upper`, ASCII letters only (`A–Z` → `a–z`, `a–z` → `A–Z`), `ensures \|res\| == \|s\|` | **ASCII case mapping only**; non-ASCII letters unchanged — differs from JS, which is full Unicode and not length-preserving (`"ß".toUpperCase() === "SS"`) | same restriction, same claim |
| `s.repeat(n)` | `StringRepeat` | exact | exact |
| Literal | written raw; only `\`, `"`, `\n` escaped | literal must be in the domain: a source literal containing an unpaired surrogate is **refused at extraction** (today Node's UTF-8 writer would silently replace it — a current defect this rung closes) | every literal admitted; non-printable-ASCII units written as `\uXXXX` |

Two rows deserve a sentence each. The `fromCharCode` precondition on `main` is the scalar
profile being honest at exactly one point — it refuses `String.fromCharCode(0xD83D)` by an
obligation the caller cannot discharge — while `.length` two lines away is silently scalar.
Rung 0 makes SPEC_DAFNY.md §4 say what that precondition already knows. And case mapping is
ASCII-only under *both* rungs; each profile's claim sentence names it, because `toLowerCase`
is the
kind of operation that looks identical in both languages and is not.

Under `unicode-scalar` the domain is "strings with no unpaired surrogate", which Dafny
enforces structurally: the type cannot hold one. That is a fact of both type systems, not a
premise a caller must discharge, so the profile's claim sentence says *no caller premise*
for the domain and states the operations that differ instead.

## 4. Configuration

One registry entry in [`tools/src/config.ts`](tools/src/config.ts), following the shape
`OPTION_SPECS` already has:

```ts
"string-semantics": {
  type: "enum",
  values: ["unicode-scalar", "javascript-utf16"],
  default: "unicode-scalar",
  fileOverride: false,
  description: "Which model of JavaScript strings a proof is made under (DESIGN_STRINGS.md).",
},
```

`fileOverride: false` for the same reason `number-semantics` is config-only
([DESIGN_NUMBERS.md](DESIGN_NUMBERS.md) §6): the model changes every string signature, so
a per-file `//@ option` would let a caller reinterpret an auto-externed callee's `string`
under its own model. Profiles must agree across a checked dependency closure, including
across nested `lemmascript.json` files; a mismatch is an error naming both files, and
auto-extern must not invent a bridge.

`resolveOptions` gains no rule: with one key there is no cross-option constraint (the
`config.ts` comment reserving "UTF-16 → local Dafny library" is retired). The emitter derives
the helper source from the profile — `Std.Collections.Seq` under `unicode-scalar`, the local
`SeqFilter`/`SeqAll`/`SeqFoldLeft` under `javascript-utf16` — because the user never chooses
the library. `dafnyVerify`'s text detection of `Std.` is unchanged; a `javascript-utf16`
artifact whose proof additions import `Std.*` is refused by #211's fail-closed check with a
message naming `string-semantics`. `lsc config` reports the resolved value.

Selecting `javascript-utf16` with `--backend=lean` is an error. Lean's `String` is a sequence
of `Char` (Unicode scalars) and [`LemmaScript/JSString.lean`](LemmaScript/JSString.lean)
defines `indexOf`/`slice` over `List Char`; it has a scalar model and no UTF-16 encoding.
The error must say so rather than emit scalar Lean for a UTF-16 claim. A value not on the
knob is an error listing today's values.

## 5. The artifact

Generated files carry the model in [DESIGN_CONFIG.md](DESIGN_CONFIG.md) §5's `lsc options`
form, and only when it is non-default:

```dafny
// Generated by lsc from foo.ts
// lsc options: string-semantics=javascript-utf16
```

Under the default the header is `// Generated by lsc from foo.ts`, unchanged, and no example
or case-study file regenerates.

- The `lsc options:` line lists only non-default options that materially affected the file,
  exactly as §5 specifies. `string-semantics=javascript-utf16` appears only when the file uses
  `string` — DESIGN_CONFIG.md already decided this ("the header marker would only be emitted
  when strings actually appear") — and is tied to emission the way #211's flag is
  (`dafny-emit.ts`: "Keep this tied to emission, rather than a textual scan").
- There is no second prose line. §5 asks that each option not invent another sentence, so the
  claim sentences of §3 live in SPEC_DAFNY.md §4 keyed by identity (`unicode-scalar-1`,
  `javascript-utf16-1`); that is where a reader of a standalone `.dfy` is sent. The default's
  identity is documented, not stamped. Stamping every artifact would touch 64 files today and
  fail the case-study CI (§7), so if it is ever wanted it is a separate PR paired with a
  regen sweep of every case study.
- The public value is `javascript-utf16`; the artifact identity is `javascript-utf16-1`
  (DESIGN_NUMBERS's `javascript` / `ecma262-2026-v1` split). The suffix is internal (open
  decision 4) and moves when the domain or an operation's meaning changes, so a later helper
  change cannot silently alter what a standalone proof claims.
- `dafnyVerify` maps the token to flags (§6) and pins `--unicode-char:true` whenever no
  `string-semantics=` token is present — including a `.dfy` with no `// Generated by lsc`
  line at all. That resolves DESIGN_CONFIG.md open question 3: no warning, because such a
  file was already verifying under that setting and the pin only makes it explicit. The
  additions-only check already guarantees `.dfy` and `.dfy.gen` share the header, so flipping
  the key in `lemmascript.json` surfaces as a generator change: `regen` three-way-merges the
  new line 2 in, then verifies under the new flags. Measured with `dafnyRegen`: the merge is
  clean when the proof's line 2 is unchanged generated text (`examples/toposort.dfy`,
  collab-todo `domain.dfy`), and conflicts — reported, `.dfy` restored — when the proof
  inserted its own line 2 (an `import opened Std.*` block as AGENTS.md prescribes, or a comment block as
  `examples/countBadPairs.dfy` and `preorder.dfy` have). Opting in is a one-time manual merge
  for such files. Reading flags from the artifact rather than the config is deliberate — a
  fixture or a file pulled out of a repo still verifies correctly.

## 6. Verifier flags — and why not `--allow-warnings`

| Profile | Flags added by `dafnyVerify` |
|---|---|
| `unicode-scalar` | `--unicode-char:true` — an explicit pin of today's default. A default is not a pin; verifying under a changed setting would silently reinterpret every string obligation. |
| `javascript-utf16` | `--unicode-char:false --allow-deprecation` |

#211 passes `--allow-warnings`, because Dafny 4.11 prints
`CLI: Warning: the option unicode-char has been deprecated.` and, by default, any warning
fails the run (`--allow-warnings` still prints it and only un-fatals it; `--allow-deprecation`
removes it). But `--allow-warnings` un-fatals *every* warning in the file — including
`warn-contradictory-assumptions` (a `requires` proved vacuous) and the missing-`{:axiom}`
warning, which are exactly the guards a verifier most needs. Dafny 4.11 has the narrow
alternative, `--allow-deprecation`: "Do not warn about the use of deprecated features."
Measured on 4.11.0: with `unicode-char = false`, `allow-deprecation = true`, and
`allow-warnings = false`, a surrogate literal verifies with no warning, and a method with
`requires false` under `warn-contradictory-assumptions` still fails the run. That resolves
[DESIGN_CONFIG.md](DESIGN_CONFIG.md) open question 2: the `unicode-char` deprecation — and,
by the flag's definition, every other *deprecated-feature* warning, which are style warnings —
is suppressed; `warn-contradictory-assumptions`, missing-`{:axiom}` (bodiless `ensures`,
`assume`), `{:verify false}`, and missing-trigger warnings all remain fatal (measured on
4.11.0).

Two facts that make this safe, both measured on Dafny 4.11.0. `--unicode-char:true` is
silent — only the `:false` value is warned as deprecated — so pinning the default costs
nothing. And `--standard-libraries` under `--unicode-char:false` is a hard CLI error
(`CLI: Error: cannot load /DafnyStandardLibraries.doo: --unicode-char is set locally to False, but the library was built with True`;
a second line names `/DafnyStandardLibraries-notarget.doo`; exit code 1, unaffected by
`--allow-warnings`), not a warning: Dafny itself refuses the misload, so #211's per-file fail-closed check (a UTF-16 file
whose *proof additions* import `Std.*`) is about giving a good message, not about soundness.

## 7. The ladder

One PR per rung, stacked, each landing only with its evidence.

**Rung 0 — name the profile, make it configuration, pin the default.** No semantic change,
no artifact change.

- `string-semantics` registry entry; `lsc config` row. No `dafny-lib` key (open decision 3):
  the emitter derives helper source from the profile.
- `dafnyVerify` parses the `lsc options:` line; pins `--unicode-char:true` whenever no
  `string-semantics=` token is present (a header-less `.dfy` gets the pin and no warning —
  DESIGN_CONFIG.md open question 3); rejects a token naming an unknown or unimplemented value.
- Registering `string.indexOf` and `string.charCodeAt` in `builtins.ts` (§3) is deferred:
  they type `unknown` today, and a registered return type changes emitted text. The profile
  gate keys on the emitter's method-name dispatch, where both already live.
- A source literal containing an unpaired surrogate is refused at extraction under
  `unicode-scalar`, with the source line.
- `javascript-utf16` is accepted by the parser and **rejected by every emitter** with a
  message naming this document and rung 1 — a staged answer, not a silent no-op.
- No regeneration. The always-stamp variant would have meant: regenerate the examples, where
  32 of 70 `.dfy.gen` mention `string` and gain one header line, and their 32 checked-in
  `.dfy` files gain the same line via regen — 64 files, the same 32 #211 stamps — and
  `dafnyCheckDiff` reports the missing line as a modified generated line, so `lsc check` on
  collab-todo's `domain.dfy.gen` (42 `string` occurrences, no `lemmascript.json`) fails this repo's
  `case-studies-dafny` CI job (`.github/workflows/ci.yml`) until that repo regenerates. Rung 0
  does none of it.
- Docs: SPEC.md §7.6 table (one row, "File override: no"), SPEC_DAFNY.md §4 String helpers
  (the two identity claim sentences from §3, keyed `unicode-scalar-1` / `javascript-utf16-1`)
  and §5 flags, SUBSET.md's `string` row, TOOLS.md §Options, site `reference/cli.md`,
  AGENTS.md's `Std.` auto-detect sentence (DESIGN_CONFIG.md §7 lists it; it gains the
  `javascript-utf16` caveat with rung 1).

Gate: existing examples and case studies verify byte-for-byte with no file changes;
`lsc config` shows the resolved profile; the verifier-flag test (§8) shows `--unicode-char:true`
in every `dafnyVerify` invocation that lacks the token; a `.dfy` carrying
`string-semantics=javascript-utf16` fails with the rung-1 message.

**Rung 1 — `javascript-utf16`.** #211's emitter work, gated on the option:

- `\uXXXX` escaping of every unit outside printable ASCII
  (`escapeDafnyUTF16String`), so astral pairs and lone surrogates survive the UTF-8 file.
- `StringFromCharCode` precondition `0 <= n < 0x10000`.
- Preambles that mention chars vary with the mode (`IsJSWhitespace` must use `\u` escapes
  under `unicode-char:false` and `\U{}` otherwise; Dafny rejects the other form).
  `PREAMBLE_CODE` entries become `string | (options) => string`.
- `SeqFilter` / `SeqAll` / `SeqFoldLeft` local helpers emitted whenever the profile is `javascript-utf16`.
- `--unicode-char:false --allow-deprecation`; never `--allow-warnings`.
- Lean: hard error.

Gate: #211's fixture verifies under the option — `"😀".length === 2`,
`charCodeAt(0) === 0xD83D`, `charCodeAt(1) === 0xDE00`, a lone surrogate has length 1,
slicing preserves the high surrogate, `String.fromCharCode(0xD83D)` round-trips — plus a
Node oracle agreeing on each; the `Std.*`-in-proof-additions negative fixture fails with a message naming
`string-semantics`; `unicode-scalar` output is byte-identical to rung 0; no case study
changes; flipping the key in a project regenerates every string-bearing artifact through
`regen`, with proofs that inserted their own line 2 reporting a conflict rather than a silent
merge (§5).

**Later rungs** are new values on the same key, each with its own design and evidence:
`unicode-nfc` (equality as canonical equivalence through a versioned normalization summary,
for code using `normalize()`) and `grapheme` (`Intl.Segmenter` semantics through a versioned
segmentation summary). Their identities must carry the Unicode table version *range* they
hold on — segmentation moves between Unicode releases and runtimes mix them — never a single
engine pin. Casing beyond ASCII is a third summary with the non-length-preserving cases named.
None of these are scoped here.

## 8. Test plan

- `tools/test-fixtures.sh`: a config fixture directory selecting each value; `lsc config`
  grepped for the resolved profile; #211's positive fixture under `javascript-utf16`; the
  negative Std fixture; an
  unpaired-surrogate literal refused under `unicode-scalar`; a Lean rejection.
- A JavaScript runtime oracle for every operation in §3 on a boundary corpus — ASCII, BMP
  non-ASCII, astral pairs, lone high and low surrogates, empty string, CR-LF — asserting the
  `javascript-utf16` proof result equals Node's, and recording where `unicode-scalar` differs
  so the documented claim is tested, not asserted.
- Golden header: #211's fixture's `lsc options:` line is pinned and diffed; `unicode-scalar`
  example output is asserted header-identical to `main`.
- Verifier-flag test: `dafnyVerify` maps each token to exactly the flags in §6, pins
  `--unicode-char:true` for a header without the token and for no header at all, and rejects
  a `.dfy` whose token names an unknown value.

Differential tests support the model; they do not replace the Dafny proofs.

## 9. Open decisions

1. *Resolved.* The `lsc options:` line appears only when the file uses `string` and the
   profile is non-default — DESIGN_CONFIG.md §"Future options" decided this ("the header
   marker would only be emitted when strings actually appear"), #211's emission-tied flag is
   the mechanism, and the always-on cost is measured in §7. There is no separate
   `String model:` line.
2. Should `unicode-scalar` refuse `.length`, indexing, and `charCodeAt` on literals that
   contain astral text (where the answer is knowably wrong), rather than stating the
   difference in the profile's claim sentence (SPEC_DAFNY.md §4)? Refusal is safer; the
   documented claim is what today's proofs already rely on. Rung 0 keeps the claim; rung 1
   may add the refusal as a warning.
3. *Resolved.* `dafny-lib` is not a user-facing key: the profile determines helper source
   (§4), `Std.` detection stays text-based, and nobody asked for `local-lib` under
   `unicode-scalar`. Byte-for-byte default output is preserved. If the local helpers ever
   become the only library under both profiles, that is an emitter change plus a regen, with
   no registry entry to remove.
4. Should the identity suffix be part of the public value (`javascript-utf16-1` in
   `lemmascript.json`) or internal, as DESIGN_NUMBERS proposes? This design keeps it internal.

## Primary references

- [ECMAScript 2026 §6.1.4, The String Type](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-ecmascript-language-types-string-type)
- [ECMAScript 2026 §22.1, String Objects](https://tc39.es/ecma262/multipage/text-processing.html#sec-string-objects)
- [Dafny 4.11 — Strings and characters](https://dafny.org/v4.11.0/Compilation/StringsAndChars)
- [Dafny reference manual — escaped characters per `--unicode-char` mode](https://dafny.org/v4.11.0/DafnyRef/DafnyRef#sec-escaped-characters) and [§5.2.5 Characters](https://dafny.org/v4.11.0/DafnyRef/DafnyRef#sec-characters)
- [PRECIS framework (RFC 8264)](https://www.rfc-editor.org/rfc/rfc8264) — the named-string-profile pattern
- LemmaSwift `DESIGN_SWIFT_STRINGS.md` — the versioned-profile shape this design borrows (its four rungs are Swift-driven; none is scheduled here)
