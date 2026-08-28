#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."

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
cp tools/fixtures/javascript-utf16-strings.ts "$fixture_dir/utf16.ts"

npx tsx tools/src/lsc.ts gen --backend=dafny "$fixture_dir/impure.ts"
if ! grep -Fq 'method {:axiom} rollDie' "$fixture_dir/impure.dfy.gen"; then
  echo "ERROR: impure extern did not emit as a body-less method"
  exit 1
fi

npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/deterministic.ts"
expect_failure \
  "Dafny equated two calls to an impure extern" \
  npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/impure.ts"

# JavaScript string length/indexing are UTF-16-code-unit operations. Astral
# characters therefore occupy two Dafny chars, and lone surrogates remain
# representable instead of being replaced while writing the generated file.
npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/utf16.ts"
grep -Fq '// LemmaScript string model: javascript-utf16-code-units' "$fixture_dir/utf16.dfy.gen"
grep -Fq '"\uD83D\uDE00"' "$fixture_dir/utf16.dfy.gen"
grep -Fq '"\uD83D"' "$fixture_dir/utf16.dfy.gen"

expect_failure \
  "Dafny standard library was combined with JavaScript UTF-16 strings" \
  npx tsx -e 'import { dafnyVerify } from "./tools/src/dafny-commands.ts"; process.exit(dafnyVerify("tools/fixtures/string-with-standard-library.dfy", process.cwd()) ? 0 : 1)'
