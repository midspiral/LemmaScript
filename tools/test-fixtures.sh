#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Run executable tests before the Dafny fixture checks.
npx tsx --test tools/tests/*.test.ts

expect_failure() {
  local message="$1"
  shift
  if "$@"; then
    echo "ERROR: $message"
    exit 1
  fi
}

expect_absent() {
  if [ -e "$1" ]; then
    echo "ERROR: failed generation wrote $1"
    exit 1
  fi
}

expect_failure \
  "Dafny accepted an unsupported declaration" \
  npx tsx tools/src/lsc.ts gen --backend=dafny tools/fixtures/unsupported-dafny-emission.ts

expect_failure \
  "Lean accepted an unsupported declaration" \
  npx tsx tools/src/lsc.ts gen --backend=lean tools/fixtures/unsupported-extraction.ts

expect_absent tools/fixtures/unsupported-dafny-emission.dfy.gen
expect_absent tools/fixtures/unsupported-dafny-emission.dfy
expect_absent tools/fixtures/unsupported-extraction.types.lean
expect_absent tools/fixtures/unsupported-extraction.def.lean

# A deterministic extern remains extensional, while `//@ impure` makes the two
# call results independent and therefore invalidates the equality proof. Copy
# to a temporary directory so expected generated artifacts never enter fixtures.
fixture_dir=$(mktemp -d)
trap 'rm -rf "$fixture_dir"' EXIT
cp tools/fixtures/deterministic-extern-equality.ts "$fixture_dir/deterministic.ts"
cp tools/fixtures/impure-extern-equality.ts "$fixture_dir/impure.ts"
cp examples/safeSlice.ts "$fixture_dir/legacy-safe-slice.ts"
cp -R tools/fixtures/utf16-project "$fixture_dir/utf16-project"
cp tools/fixtures/unpaired-surrogate.ts "$fixture_dir/unpaired.ts"

npx tsx tools/src/lsc.ts gen --backend=dafny "$fixture_dir/impure.ts"
if ! grep -Fq 'method {:axiom} rollDie' "$fixture_dir/impure.dfy.gen"; then
  echo "ERROR: impure extern did not emit as a body-less method"
  exit 1
fi

npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/deterministic.ts"
expect_failure \
  "Dafny equated two calls to an impure extern" \
  npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/impure.ts"

npx tsx tools/src/lsc.ts gen --backend=dafny "$fixture_dir/legacy-safe-slice.ts"
if ! grep -Fq 'function SafeSlice' "$fixture_dir/legacy-safe-slice.dfy.gen"; then
  echo "ERROR: legacy //@ safe-slice no longer enables safe slice emission"
  exit 1
fi

# Project configuration: nearest-ancestor discovery, generic file overrides,
# extern defaults, safe-slice, and mirrored Dafny artifact routing. Work from a
# copy because proof-dir generation intentionally creates companion files.
config_fixture="$fixture_dir/config-project"
cp -R tools/fixtures/config-project "$config_fixture"
configured="$config_fixture/src/configured.ts"

config_report=$(npx tsx tools/src/lsc.ts config "$configured")
for expected in \
  "\"configFile\": \"$config_fixture/lemmascript.json\"" \
  '"extern-default": "impure"' \
  '"safe-slice": false' \
  '"proof-dir": "proofs"' \
  "\"artifactDir\": \"$config_fixture/proofs/src\""; do
  if ! grep -Fq "$expected" <<<"$config_report"; then
    echo "ERROR: lsc config report missing: $expected"
    exit 1
  fi
done

npx tsx tools/src/lsc.ts gen --backend=dafny "$configured"
configured_gen="$config_fixture/proofs/src/configured.dfy.gen"
if [ ! -e "$configured_gen" ] || [ ! -e "$config_fixture/proofs/src/configured.dfy" ]; then
  echo "ERROR: proof-dir did not create the Dafny pair in the mirrored directory"
  exit 1
fi
expect_absent "$config_fixture/src/configured.dfy.gen"
expect_absent "$config_fixture/src/configured.dfy"
if ! grep -Fq 'method {:axiom} rollDie' "$configured_gen"; then
  echo "ERROR: extern-default=impure did not emit an unmarked extern as a method"
  exit 1
fi
if grep -Fq 'function SafeSlice' "$configured_gen"; then
  echo "ERROR: file-level safe-slice=false did not override project config"
  exit 1
fi
printf '\n// retained proof addition\n' >> "$config_fixture/proofs/src/configured.dfy"
npx tsx tools/src/lsc.ts regen --backend=dafny --no-verify "$configured"
if ! grep -Fq '// retained proof addition' "$config_fixture/proofs/src/configured.dfy"; then
  echo "ERROR: regen did not preserve a proof addition under proof-dir"
  exit 1
fi

npx tsx tools/src/lsc.ts gen --backend=dafny "$config_fixture/src/safe.ts"
if ! grep -Fq 'function SafeSlice' "$config_fixture/proofs/src/safe.dfy.gen"; then
  echo "ERROR: safe-slice=true from lemmascript.json was not consumed"
  exit 1
fi

npx tsx tools/src/lsc.ts gen --backend=dafny "$config_fixture/src/pure-override.ts"
if ! grep -Fq 'function {:axiom} rollDie' "$config_fixture/proofs/src/pure-override.dfy.gen"; then
  echo "ERROR: file-level extern-default=pure did not override project config"
  exit 1
fi

npx tsx tools/src/lsc.ts gen --backend=dafny "$config_fixture/src/cross-file.ts"
cross_file_gen="$config_fixture/proofs/src/cross-file.dfy.gen"
if ! grep -Fq 'method {:axiom} defaultRoll' "$cross_file_gen"; then
  echo "ERROR: extern-default=impure did not apply to a cross-file auto-extern"
  exit 1
fi
if ! grep -Fq 'function {:axiom} stableRoll' "$cross_file_gen"; then
  echo "ERROR: //@ pure on a cross-file const arrow did not override extern-default"
  exit 1
fi

typed_report=$(npx tsx tools/src/lsc.ts info --typed "$configured")
if ! grep -Fq '"options"' <<<"$typed_report" || ! grep -Fq '"extern-default": "impure"' <<<"$typed_report"; then
  echo "ERROR: lsc info --typed did not report effective options"
  exit 1
fi

defaults_report=$(npx tsx tools/src/lsc.ts config --config="$config_fixture/lemmascript.json")
if ! grep -Fq '"proof-dir": "proofs"' <<<"$defaults_report" || grep -Fq '"artifactDir"' <<<"$defaults_report"; then
  echo "ERROR: file-less lsc config did not report project defaults correctly"
  exit 1
fi

expect_failure \
  "Lean accepted an extern made impure by project config" \
  npx tsx tools/src/lsc.ts gen --backend=lean "$configured"
expect_failure \
  "an extern was accepted with both //@ pure and //@ impure" \
  npx tsx tools/src/lsc.ts gen --backend=dafny "$config_fixture/src/conflicting-extern.ts"

expect_failure \
  "unknown file option was accepted" \
  npx tsx tools/src/lsc.ts config "$config_fixture/src/bad-option.ts"
expect_failure \
  "duplicate file option was accepted" \
  npx tsx tools/src/lsc.ts config "$config_fixture/src/duplicate-option.ts"
expect_failure \
  "config-only proof-dir was accepted in a source directive" \
  npx tsx tools/src/lsc.ts config "$config_fixture/src/proof-dir-option.ts"
expect_failure \
  "late file option was accepted" \
  npx tsx tools/src/lsc.ts config "$config_fixture/src/late-option.ts"

expect_failure \
  "unknown lemmascript.json key was accepted" \
  npx tsx tools/src/lsc.ts config tools/fixtures/config-invalid-unknown/source.ts
expect_failure \
  "bad lemmascript.json value was accepted" \
  npx tsx tools/src/lsc.ts config tools/fixtures/config-invalid-value/source.ts
expect_failure \
  "proof-dir accepted a source outside the pinned config directory" \
  npx tsx tools/src/lsc.ts config --config="$config_fixture/lemmascript.json" "$fixture_dir/deterministic.ts"

expect_failure \
  "proof-dir silently bypassed a sibling hand-written proof" \
  npx tsx tools/src/lsc.ts gen --backend=dafny "$config_fixture/src/legacy.ts"
expect_absent "$config_fixture/proofs/src/legacy.dfy"

# ── String profile (DESIGN_STRINGS.md) ──────────────────────────────────────
# Under "string-semantics": "javascript-utf16" a JavaScript string is a UTF-16
# code-unit sequence: astral characters occupy two Dafny chars and lone
# surrogates stay representable. The header token is what dafnyVerify maps to
# --unicode-char:false --allow-deprecation.
utf16="$fixture_dir/utf16-project/src/utf16.ts"
utf16_gen="$fixture_dir/utf16-project/src/utf16.dfy.gen"
if ! npx tsx tools/src/lsc.ts config "$utf16" | grep -Fq '"string-semantics": "javascript-utf16"'; then
  echo "ERROR: lsc config did not report string-semantics=javascript-utf16"
  exit 1
fi
npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$utf16"
grep -Fq '// lsc options: string-semantics=javascript-utf16' "$utf16_gen"
grep -Fq '"\uD83D\uDE00"' "$utf16_gen"
grep -Fq '"\uD83D"' "$utf16_gen"
if grep -Fq 'Std.Collections' "$utf16_gen"; then
  echo "ERROR: javascript-utf16 emitted a Dafny standard-library call"
  exit 1
fi

expect_failure \
  "Dafny standard library was combined with javascript-utf16 strings" \
  npx tsx -e 'import { dafnyVerify } from "./tools/src/dafny-commands.ts"; process.exit(dafnyVerify("tools/fixtures/string-with-standard-library.dfy", ".") ? 0 : 1)'

expect_failure \
  "javascript-utf16 was accepted by the Lean backend" \
  npx tsx tools/src/lsc.ts gen --backend=lean "$fixture_dir/utf16-project/src/lean-rejected.ts"
expect_absent "$fixture_dir/utf16-project/src/lean-rejected.def.lean"

# The default profile cannot represent a lone surrogate: refused at extraction
# with the source line, not silently replaced by the UTF-8 file writer.
expect_failure \
  "unicode-scalar accepted an unpaired surrogate literal" \
  npx tsx tools/src/lsc.ts gen --backend=dafny "$fixture_dir/unpaired.ts"
expect_absent "$fixture_dir/unpaired.dfy.gen"

# The default profile leaves generated text exactly as before: no header token.
npx tsx tools/src/lsc.ts gen --backend=dafny "$fixture_dir/legacy-safe-slice.ts"
if grep -Fq '// lsc options:' "$fixture_dir/legacy-safe-slice.dfy.gen"; then
  echo "ERROR: unicode-scalar stamped an options header"
  exit 1
fi
