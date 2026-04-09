#!/usr/bin/env bash
# Regenerate and verify LemmaScript artifacts.
# Usage: ./check.sh <lean|dafny|dafny-slow> [file.ts ...]
#
# LemmaScript-files.txt format:  filepath [timeout_in_seconds]
# No timeout = use Dafny default.
#
# dafny:      verify files with timeout <= 60, gen-check the rest
# dafny-slow: verify all files with their specified timeout
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LSC="npx --prefix $SCRIPT_DIR tsx $SCRIPT_DIR/src/lsc.ts"
CI_LIMIT=60

backend="${1:-all}"; shift 2>/dev/null || true

FILES=()
if [ $# -gt 0 ]; then
  FILES=("$@")
else
  if [ ! -f "LemmaScript-files.txt" ]; then
    echo "No files given and no LemmaScript-files.txt found."
    exit 1
  fi
  while IFS= read -r line || [ -n "$line" ]; do
    [ -n "$line" ] && FILES+=("$line")
  done < LemmaScript-files.txt
fi

check_lean() {
  for entry in "${FILES[@]}"; do
    local f="${entry%% *}"
    $LSC gen --backend=lean "$f"
  done
  lake build
}

check_dafny() {
  for entry in "${FILES[@]}"; do
    local f="${entry%% *}"
    local t="${entry#* }"
    [ "$t" = "$entry" ] && t=""
    if [ -n "$t" ] && [ "$t" -gt "$CI_LIMIT" ] 2>/dev/null; then
      echo "=== $(basename "$f") (timeout ${t}s > ${CI_LIMIT}s, gen-check only) ==="
      $LSC gen-check --backend=dafny "$f"
    else
      $LSC check --backend=dafny ${t:+--time-limit=$t} "$f"
    fi
  done
}

check_dafny_slow() {
  for entry in "${FILES[@]}"; do
    local f="${entry%% *}"
    local t="${entry#* }"
    [ "$t" = "$entry" ] && t=""
    $LSC check --backend=dafny ${t:+--time-limit=$t} "$f"
  done
}

case "$backend" in
  lean)       check_lean ;;
  dafny)      check_dafny ;;
  dafny-slow) check_dafny_slow ;;
  all)        check_lean; check_dafny ;;
  *)
    echo "Usage: check.sh [lean|dafny|dafny-slow] [file.ts ...]"
    exit 1
    ;;
esac
