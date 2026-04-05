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
  examples/arrayContains.ts
  examples/transition.ts
  examples/packet.ts
  examples/clamp.ts
  # examples/hof.ts          # uses arr.map/filter/every/some (not supported on seq)
  # examples/spec.ts         # kitchen sink, needs HOF + string ops
)

for f in "${FILES[@]}"; do
  echo "=== $f ==="
  npx tsx tools/src/lsc.ts regen --backend=dafny "$f"
  echo
done
