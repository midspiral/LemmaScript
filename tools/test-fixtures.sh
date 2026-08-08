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

migration_tmp="$(mktemp -d)"
trap 'rm -rf "$migration_tmp"' EXIT
cp tools/fixtures/migrate-0.5-specs.input.txt "$migration_tmp/case.ts"

expect_failure \
  "migration check missed 0.5 spec syntax" \
  node tools/migrate-0.5-specs.mjs --check "$migration_tmp/case.ts"

node tools/migrate-0.5-specs.mjs "$migration_tmp/case.ts"
diff -u tools/fixtures/migrate-0.5-specs.expected.txt "$migration_tmp/case.ts"
node tools/migrate-0.5-specs.mjs --check "$migration_tmp/case.ts"
