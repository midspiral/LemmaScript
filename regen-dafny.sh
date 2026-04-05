#!/bin/bash
# Regenerate and verify all Dafny files from TypeScript sources.
set -e
cd "$(dirname "$0")"
for f in examples/*.ts; do
  echo "=== $f ==="
  npx tsx tools/src/lsc.ts regen --backend=dafny "$f"
  echo
done
