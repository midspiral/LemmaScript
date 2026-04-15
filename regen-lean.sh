#!/bin/bash
# Regenerate all .types.lean and .def.lean from TypeScript sources.
set -e
cd "$(dirname "$0")/tools"
for f in ../examples/*.ts; do
  npx tsx src/lsc.ts gen --backend=lean "$f"
done
