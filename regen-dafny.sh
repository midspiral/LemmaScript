#!/bin/bash
# Regenerate .dfy.gen files and check .dfy files for ported examples.
set -e
cd "$(dirname "$0")"

# Explicitly list ported examples
FILES=(
  examples/clamp.ts
  examples/binarySearch.ts
)

for f in "${FILES[@]}"; do
  echo "=== $f ==="
  npx tsx tools/src/lsc.ts gen --backend=dafny "$f"
  npx tsx tools/src/lsc.ts check --backend=dafny "$f"
  echo
done
