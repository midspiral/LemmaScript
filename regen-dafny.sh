#!/bin/bash
# Regenerate Dafny files for ported examples.
set -e
cd "$(dirname "$0")"

FILES=(
  examples/clamp.ts
  examples/binarySearch.ts
  examples/linearSearch.ts
  examples/arraySum.ts
  examples/maxElement.ts
  examples/isSorted.ts
)

for f in "${FILES[@]}"; do
  echo "=== $f ==="
  npx tsx tools/src/lsc.ts regen --backend=dafny "$f"
  echo
done
