#!/bin/bash
# Regenerate and verify all Dafny files from TypeScript sources.
# Extra args are forwarded to each `lsc regen` call — notably `--no-verify`,
# which does regen + three-way merge + additions-only check but skips
# `dafny verify` (CI verifies separately via the `lsc check` pass).
set -e
cd "$(dirname "$0")"
for f in examples/*.ts; do
  echo "=== $f ==="
  npx tsx tools/src/lsc.ts regen --backend=dafny "$@" "$f"
  echo
done
