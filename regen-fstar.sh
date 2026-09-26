#!/bin/bash
# Regenerate F* companions, preserve proof additions, and verify every example.
# Companions live beside their TypeScript sources in examples/.
# Pass --no-verify for regeneration only. Other arguments go to lsc regen.
set -u
cd "$(dirname "$0")" || exit 1
npm run build || exit 1
log=$(mktemp) || exit 1
trap 'rm -f "$log"' EXIT
passed=0
failed=0
skipped=0
for f in examples/*.ts; do
  printf '\n%s\n' "$f"
  if node tools/dist/lsc.js regen --backend=fstar "$@" "$f" >"$log" 2>&1; then
    if grep -q '^Skipped:' "$log"; then
      skipped=$((skipped + 1))
    else
      passed=$((passed + 1))
    fi
  else
    failed=$((failed + 1))
  fi
  cat "$log"
done
printf '\nF*: %s succeeded, %s failed, %s skipped\n' "$passed" "$failed" "$skipped"
test "$failed" -eq 0 && test "$skipped" -eq 0
