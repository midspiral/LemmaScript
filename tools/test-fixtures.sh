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

# Extern results are independent by default, while `//@ pure` opts into the
# deterministic/extensional model. Cover both same-file extern declarations and
# a pure cross-file source annotation. Copy to a temporary directory so expected
# generated artifacts never enter fixtures.
fixture_dir=$(mktemp -d)
trap 'rm -rf "$fixture_dir"' EXIT
cp tools/fixtures/deterministic-extern-equality.ts "$fixture_dir/deterministic.ts"
cp tools/fixtures/impure-extern-equality.ts "$fixture_dir/impure.ts"
cp tools/fixtures/pure-cross-file-equality.ts "$fixture_dir/pure-cross-file.ts"
cp tools/fixtures/pure-cross-file-source.ts "$fixture_dir/pure-cross-file-source.ts"

npx tsx tools/src/lsc.ts gen --backend=dafny "$fixture_dir/impure.ts"
if ! grep -Fq 'method {:axiom} rollDie' "$fixture_dir/impure.dfy.gen"; then
  echo "ERROR: impure extern did not emit as a body-less method"
  exit 1
fi

npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/deterministic.ts"
npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/pure-cross-file.ts"
npx tsx tools/src/lsc.ts gen --backend=lean "$fixture_dir/deterministic.ts"
npx tsx tools/src/lsc.ts gen --backend=lean "$fixture_dir/pure-cross-file.ts"
expect_failure \
  "Lean accepted a default-impure extern" \
  npx tsx tools/src/lsc.ts gen --backend=lean "$fixture_dir/impure.ts"
expect_failure \
  "Dafny equated two calls to a default-impure extern" \
  npx tsx tools/src/lsc.ts check --backend=dafny --time-limit=10 "$fixture_dir/impure.ts"
