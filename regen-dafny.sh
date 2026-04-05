#!/bin/bash
# Regenerate Dafny files for ported examples.
set -e
cd "$(dirname "$0")"

FILES=(
  examples/binarySearch.ts
  examples/linearSearch.ts
  examples/arraySum.ts
  examples/maxElement.ts
  examples/isSorted.ts
  # examples/clamp.ts        # needs HOF/lambda support for clampAll
)

for f in "${FILES[@]}"; do
  echo "=== $f ==="
  npx tsx tools/src/lsc.ts regen --backend=dafny "$f"
  echo
done
